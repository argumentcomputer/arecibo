#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]
#![allow(unused_mut)]
#[cfg(test)]
mod tests {
  use crate::provider::non_hiding_kzg::{UVKZGPoly, UniversalKZGParam};
  use crate::provider::traits::DlogGroup;
  use crate::provider::util::iterators::DoubleEndedIteratorExt;
  use crate::spartan::polys::univariate::UniPoly;
  use crate::zip_with;
  use ff::Field;
  use group::{Curve, Group};
  use halo2curves::bn256::{multi_miller_loop, pairing, Bn256, Fr, G1Affine, G2Prepared, G1, G2};
  use itertools::Itertools;
  use pairing::{MillerLoopResult, MultiMillerLoop};
  use rand_core::OsRng;

  #[test]
  fn e2e_test_pcs_trivial() {
    /// Trivial PCS
    ///
    /// Setup phase:
    /// - SRS contains [G1, G1^2, G1^3, ... G1^n]
    ///
    /// Proving phase:
    /// - prover computes commitment to a polynomial
    /// - prover sends to verifier: 1) polynomial; 2) commitment
    ///
    /// Verifying phase:
    /// - verifier computes commitment to a polynomial
    /// - verifier compares computed and received commitments
    let mut rng = OsRng;

    // SETUP
    let n = 4;
    let srs = UniversalKZGParam::<Bn256>::gen_srs_for_testing(&mut rng, n);

    // PROVE
    let poly = vec![Fr::from(1), Fr::from(2), Fr::from(1), Fr::from(4)]; // poly = [1, 2, 1, 4]
    let commitment_prover =
      <G1 as DlogGroup>::vartime_multiscalar_mul(&poly, &srs.powers_of_g[..poly.len()]);

    // VERIFY
    let commitment_verifier =
      <G1 as DlogGroup>::vartime_multiscalar_mul(&poly, &srs.powers_of_g[..poly.len()]);
    assert_eq!(commitment_prover, commitment_verifier);
  }

  #[test]
  fn e2e_test_pcs_kzg() {
    /// KZG scheme (from https://risencrypto.github.io/Kate/)
    ///
    /// The advantage is that we don't need to send the whole polynomial (which can be huge)
    /// to the verifier. Instead, prover performs an evaluation of the initial polynomial over
    /// some random scalar (sent previously be the verifier) and then provides an additional
    /// commitment over quotient polynomial: Q(x)=F(x) - c / x - b that "proves" poly(b) = c claim.
    ///
    /// Verifier on its side performs pairing checks that e(Cq, a⋅G2 − b⋅G2) == e(Cf − G1⋅c, G2),
    /// which actually verifies a claim that poly(b) = c
    ///
    let mut rng = OsRng;

    // SETUP
    let n = 4;
    let srs = UniversalKZGParam::<Bn256>::gen_srs_for_testing(&mut rng, n);

    // PROVE
    let poly = vec![Fr::from(1), Fr::from(2), Fr::from(1), Fr::from(4)]; // poly = [1, 2, 1, 4]
    let b = Fr::from(50); // verifier sends this eval to prover initially
    let c = UniPoly::new(poly.clone()).evaluate(&b); // part of proof
    let Cf = <G1 as DlogGroup>::vartime_multiscalar_mul(&poly, &srs.powers_of_g[..poly.len()]); // part of proof

    let divident = UVKZGPoly::new(poly.clone());
    let divisor = UVKZGPoly {
      coeffs: vec![-b, Fr::one()],
    };
    let (quotient_polynomial_q_x, reminder) = divident.divide_with_q_and_r(&divisor).unwrap(); // computing quotient polynomial

    let Cq = <G1 as DlogGroup>::vartime_multiscalar_mul(
      &quotient_polynomial_q_x.coeffs,
      &srs.powers_of_g[..quotient_polynomial_q_x.coeffs.len()],
    ); // part of proof

    // VERIFY
    let g1 = srs.powers_of_g[0];
    let g2 = srs.powers_of_h[0];

    let left = pairing(
      &Cq.to_affine(),
      &(srs.powers_of_h[1] - (g2 * b)).to_affine(),
    );
    let right = pairing(&(Cf.to_affine() - (g1 * c).to_affine()).to_affine(), &g2);
    assert_eq!(left, right);

    // Alternatively (more optimal as it doesn't require executing final_exponentiation twice)
    let term1 = (
      &(srs.powers_of_g[0] * c - Cq * b - Cf).to_affine(),
      &G2Prepared::from_affine(srs.powers_of_h[0]),
    );
    let term2 = (
      &Cq.to_affine(),
      &G2Prepared::from_affine(srs.powers_of_h[1]),
    );
    let result = multi_miller_loop(&[term1, term2]).final_exponentiation();
    assert_eq!(result.is_identity().unwrap_u8(), 0x01);
  }

  #[test]
  fn e2e_test_pcs_kzg_batched_single_poly_multiple_points() {
    /// KZG scheme (https://risencrypto.github.io/Kate/)
    ///
    /// Batch mode. Single polynomial, multiple points
    let mut rng = OsRng;

    // SETUP
    let n = 8;
    let srs = UniversalKZGParam::<Bn256>::gen_srs_for_testing(&mut rng, n);

    // PROVE
    let poly = vec![
      Fr::from(1),
      Fr::from(2),
      Fr::from(1),
      Fr::from(12),
      Fr::from(7),
      Fr::from(11),
      Fr::from(8),
      Fr::from(4),
    ];
    let B = vec![Fr::from(25), Fr::from(47)]; // initial evals provided by verifier

    let Cf = <G1 as DlogGroup>::vartime_multiscalar_mul(&poly, &srs.powers_of_g[..poly.len()]); // part of proof

    // C = [ F(b_i) ]
    let C = B
      .iter()
      .map(|b| UniPoly::new(poly.clone()).evaluate(b))
      .collect::<Vec<Fr>>(); // part of proof

    let divident = UVKZGPoly::new(poly);
    // P(X) = (x-b[0]) * (x-b[1]) = 1 * x^2 - b[1] * x - b[0] * x + b[0] * b[1]
    let divisor = vec![B[0] * B[1], -(B[0] + B[1]), Fr::one()];

    let (Q_x, R_x) = divident
      .divide_with_q_and_r(&UVKZGPoly::new(divisor.clone()))
      .unwrap();
    // R(x) is part of the proof

    let mut Cp = G2::default();
    divisor
      .iter()
      .zip(srs.powers_of_h[..divisor.len()].iter())
      .for_each(|(scalar, g2_elem)| {
        Cp = Cp + (g2_elem * scalar);
      }); // part of proof

    let Cq =
      <G1 as DlogGroup>::vartime_multiscalar_mul(&Q_x.coeffs, &srs.powers_of_g[..Q_x.coeffs.len()]); // part of proof

    // VERIFY (verifier should get the proof(R_x, Cq, Cp, Cf))
    let Cr =
      <G1 as DlogGroup>::vartime_multiscalar_mul(&R_x.coeffs, &srs.powers_of_g[..R_x.coeffs.len()]);

    let R_x_evals = B.iter().map(|b| R_x.evaluate(b)).collect::<Vec<Fr>>();

    // Check that F(b_i) = R(b_i)
    R_x_evals.iter().zip(C).for_each(|(r_x, c)| {
      assert_eq!(r_x, &c);
    });

    let g1 = srs.powers_of_g[0];
    let g2 = srs.powers_of_h[0];

    let left = pairing(&(Cf - Cr).to_affine(), &g2);
    let right = pairing(&Cq.to_affine(), &Cp.to_affine());
    assert_eq!(left, right);
  }

  #[test]
  fn e2e_test_pcs_kzg_batched_multiple_polys_single_point() {
    /// KZG scheme (https://risencrypto.github.io/Kate/)
    ///
    /// Batch mode. Multiple polynomials, single point
    ///
    let mut rng = OsRng;

    // SETUP
    let n = 8;
    let srs = UniversalKZGParam::<Bn256>::gen_srs_for_testing(&mut rng, n);

    // PROVE
    let poly0 = vec![
      Fr::from(1),
      Fr::from(2),
      Fr::from(1),
      Fr::from(12),
      Fr::from(7),
      Fr::from(11),
      Fr::from(8),
      Fr::from(4),
    ];
    let poly1 = vec![
      Fr::from(20),
      Fr::from(12),
      Fr::from(5),
      Fr::from(87),
      Fr::from(54),
      Fr::from(2),
      Fr::from(1),
      Fr::from(23),
    ];
    let poly2 = vec![
      Fr::from(112),
      Fr::from(124),
      Fr::from(12512),
      Fr::from(2),
      Fr::from(42),
      Fr::from(67),
      Fr::from(242),
      Fr::from(88),
    ];

    let z = Fr::from(50); // point

    let poly0_at_z = UniPoly::new(poly0.clone()).evaluate(&z); // part of proof
    let poly1_at_z = UniPoly::new(poly1.clone()).evaluate(&z); // part of proof
    let poly2_at_z = UniPoly::new(poly2.clone()).evaluate(&z); // part of proof

    let Cf_0 = <G1 as DlogGroup>::vartime_multiscalar_mul(&poly0, &srs.powers_of_g[..poly0.len()]);

    let Cf_1 = <G1 as DlogGroup>::vartime_multiscalar_mul(&poly1, &srs.powers_of_g[..poly1.len()]);

    let Cf_2 = <G1 as DlogGroup>::vartime_multiscalar_mul(&poly2, &srs.powers_of_g[..poly2.len()]);

    let gamma = Fr::from(100); // known both to prover and verifier
    let gamma_0 = Fr::one();
    let gamma_1 = gamma;
    let gamma_2 = gamma * gamma;

    let divident = UVKZGPoly::new(poly0);
    let divisor = vec![-z, Fr::one()];
    let (mut Q_x_0, _) = divident
      .divide_with_q_and_r(&UVKZGPoly::new(divisor))
      .unwrap();
    Q_x_0 *= &gamma_0;

    let divident = UVKZGPoly::new(poly1);
    let divisor = vec![-z, Fr::one()];
    let (mut Q_x_1, _) = divident
      .divide_with_q_and_r(&UVKZGPoly::new(divisor))
      .unwrap();
    Q_x_1 *= &gamma_1;

    let divident = UVKZGPoly::new(poly2);
    let divisor = vec![-z, Fr::one()];
    let (mut Q_x_2, _) = divident
      .divide_with_q_and_r(&UVKZGPoly::new(divisor))
      .unwrap();
    Q_x_2 *= &gamma_2;

    let mut h_x = Q_x_0;
    h_x += &Q_x_1;
    h_x += &Q_x_2;

    let Ch =
      <G1 as DlogGroup>::vartime_multiscalar_mul(&h_x.coeffs, &srs.powers_of_g[..h_x.coeffs.len()]); // part of proof

    // VERIFY
    let F_0 = Cf_0 * gamma_0;
    let F_1 = Cf_1 * gamma_1;
    let F_2 = Cf_2 * gamma_2;
    let F = F_0 + F_1 + F_2;

    let v_0 = srs.powers_of_g[0] * poly0_at_z * gamma_0;
    let v_1 = srs.powers_of_g[0] * poly1_at_z * gamma_1;
    let v_2 = srs.powers_of_g[0] * poly2_at_z * gamma_2;
    let v = v_0 + v_1 + v_2;

    let aG = srs.powers_of_h[1];
    let zG = (srs.powers_of_h[0] * z).to_affine();

    let left = pairing(&Ch.to_affine(), &(aG - zG).to_affine());
    let right = pairing(&(F - v).to_affine(), &srs.powers_of_h[0]);
    assert_eq!(left, right);
  }

  #[test]
  fn e2e_test_pcs_mlkzg_flow() {
    let poly = vec![
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
    ];

    let point = vec![Fr::from(4), Fr::from(3), Fr::from(8)];
    let eval = Fr::from(57);

    // SETUP
    let mut rng = OsRng;
    let n = poly.len();
    let srs = UniversalKZGParam::<Bn256>::gen_srs_for_testing(&mut rng, n);

    // PROVE
    assert_eq!(n, 1 << point.len());

    // Phase 1 (constructing Pi polynomials and computing commitments to them)
    let Pi_0 = poly.clone();
    let Pi_1 = construct_next_Pi(Pi_0.as_slice(), point[2]);
    let Pi_2 = construct_next_Pi(Pi_1.as_slice(), point[1]);
    let Pi_3 = construct_next_Pi(Pi_2.as_slice(), point[0]);
    let Pi = vec![Pi_0, Pi_1, Pi_2, Pi_3];
    assert_eq!(Pi.len(), 4);
    assert_eq!(Pi[3].len(), 1);
    assert_eq!(Pi[3][0], eval);

    let pi_commitments = Pi
      .clone()
      .into_iter()
      .map(|poly| {
        <G1 as DlogGroup>::vartime_multiscalar_mul(&poly, &srs.powers_of_g[..poly.len()])
          .to_affine()
      })
      .collect::<Vec<G1Affine>>();

    // Phase 2 (simplified for this flow)
    let r = Fr::from(182345);
    let minus_r = -r;
    let r_squared = r * r;

    // Phase 3

    // Compute evals at r, -r, r^2 for each Pi polynomial
    let evals_at_r = Pi
      .clone()
      .into_iter()
      .map(|poly| UniPoly::new(poly).evaluate(&r))
      .collect::<Vec<Fr>>();

    let evals_at_minus_r = Pi
      .clone()
      .into_iter()
      .map(|poly| UniPoly::new(poly).evaluate(&minus_r))
      .collect::<Vec<Fr>>();

    let evals_at_r_squared = Pi
      .clone()
      .into_iter()
      .map(|poly| UniPoly::new(poly).evaluate(&r_squared))
      .collect::<Vec<Fr>>();

    // Compute B(x) = f_0(x) + q * f_1(x) + ... + q^(k-1) * f_{k-1}(x)
    let q = Fr::from(1983758);
    let batched_Pi: UniPoly<Fr> = Pi.clone().into_iter().map(UniPoly::new).rlc(&q);

    // Compute openings (commitments to quotient polynomial) at r, -r, r^2
    let compute_witness_polynomial = |f: &[Fr], r: Fr| -> Vec<Fr> {
      let d = f.len();
      // Compute h(x) = f(x)/(x - r)
      let mut h = vec![Fr::ZERO; d];
      for i in (1..d).rev() {
        h[i - 1] = f[i] + h[i] * r;
      }
      h
    };

    let h_at_r = compute_witness_polynomial(batched_Pi.coeffs.as_slice(), r);
    let h_at_minus_r = compute_witness_polynomial(batched_Pi.coeffs.as_slice(), minus_r);
    let h_at_r_squared = compute_witness_polynomial(batched_Pi.coeffs.as_slice(), r_squared);

    /*
    /// 'compute_witness_polynomial' is equivalent to 'divide_with_q_and_r'

    let divident = UVKZGPoly::new(batched_Pi.coeffs.clone());
    let divisor = vec![minus_r, Fr::one()];
    let (Q_x, _) = divident
        .divide_with_q_and_r(&UVKZGPoly::new(divisor.clone()))
        .unwrap();

    assert_eq!(&h_at_r[..h_at_r.len()-1], Q_x.coeffs.as_slice());
    */

    let w0 = <G1 as DlogGroup>::vartime_multiscalar_mul(&h_at_r, &srs.powers_of_g[..h_at_r.len()])
      .to_affine();
    let w1 = <G1 as DlogGroup>::vartime_multiscalar_mul(
      &h_at_minus_r,
      &srs.powers_of_g[..h_at_minus_r.len()],
    )
    .to_affine();
    let w2 = <G1 as DlogGroup>::vartime_multiscalar_mul(
      &h_at_r_squared,
      &srs.powers_of_g[..h_at_r_squared.len()],
    )
    .to_affine();

    // VERIFY
    // Compute powers of q : (1, q, q^2, ..., q^(k-1))
    let q_powers = std::iter::successors(Some(Fr::one()), |&x| Some(x * q))
      .take(pi_commitments.len())
      .collect::<Vec<Fr>>();

    let d_0 = Fr::from(187465);
    let d_1 = d_0 * d_0;
    let q_power_multiplier = Fr::one() + d_0 + d_1;
    let q_powers_multiplied: Vec<Fr> = q_powers
      .iter()
      .map(|q_power| *q_power * q_power_multiplier)
      .collect();

    let B_u = [evals_at_r, evals_at_minus_r, evals_at_r_squared]
      .into_iter()
      .map(|evals| zip_with!(iter, (q_powers, evals), |a, b| *a * *b).sum())
      .collect::<Vec<Fr>>();

    let L_scalars = [
      q_powers_multiplied,
      vec![
        r,
        (minus_r * d_0),
        (r_squared * d_1),
        (B_u[0] + d_0 * B_u[1] + d_1 * B_u[2]),
      ],
    ]
    .concat();

    let L_bases = [
      pi_commitments,
      vec![
        G1::from(w0).to_affine(),
        G1::from(w1).to_affine(),
        G1::from(w2).to_affine(),
        (-G1::from(srs.powers_of_g[0])).to_affine(),
      ],
    ]
    .concat();

    let L = <G1 as DlogGroup>::vartime_multiscalar_mul(L_scalars.as_slice(), L_bases.as_slice());

    let R0 = G1::from(w0);
    let R1 = G1::from(w1);
    let R2 = G1::from(w2);
    let R = R0 + R1 * d_0 + R2 * d_1;

    // Check that e(L, vk.H) == e(R, vk.tau_H)
    let pairing_inputs = [
      (&(-L).to_affine(), &G2Prepared::from(srs.powers_of_h[0])),
      (&R.to_affine(), &G2Prepared::from(srs.powers_of_h[1])),
    ];

    let pairing_result = multi_miller_loop(&pairing_inputs).final_exponentiation();
    assert_eq!(pairing_result.is_identity().unwrap_u8(), 0x01);
  }

  #[test]
  fn batching_property_unit_testing() {
    let poly = vec![
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
    ];

    let point = vec![Fr::from(4), Fr::from(3), Fr::from(8)];

    let Pi_0 = poly.clone();
    let Pi_1 = construct_next_Pi(Pi_0.as_slice(), point[2]);
    let Pi_2 = construct_next_Pi(Pi_1.as_slice(), point[1]);
    let Pi_3 = construct_next_Pi(Pi_2.as_slice(), point[0]);
    let Pi = vec![Pi_0, Pi_1, Pi_2, Pi_3];

    let q = Fr::from(1983758);
    let q_powers = std::iter::successors(Some(Fr::one()), |&x| Some(x * q))
        .take(Pi.len())
        .collect::<Vec<Fr>>();

    let r = Fr::from(182345);

    let evals_at_r = Pi
        .clone()
        .into_iter()
        .map(|poly| UniPoly::new(poly).evaluate(&r))
        .collect::<Vec<Fr>>();

    // Compute B(x) = f_0(x) + q * f_1(x) + ... + q^(k-1) * f_{k-1}(x)
    let batched_Pi: UniPoly<Fr> = Pi.clone().into_iter().map(UniPoly::new).rlc(&q);

    let eval_r_1 = evals_at_r.iter().zip(q_powers.iter()).map(|(eval, q)| eval * q).collect::<Vec<Fr>>().into_iter().sum::<Fr>();
    let eval_r_2 = batched_Pi.evaluate(&r);
    assert_eq!(eval_r_1, eval_r_2);
  }

  fn construct_next_Pi(pi: &[Fr], point: Fr) -> Vec<Fr> {
    let Pi_len = pi.len() / 2;
    let mut Pi = vec![Fr::ZERO; Pi_len];
    for j in 0..Pi_len {
      Pi[j] = point * (pi[2 * j + 1] - pi[2 * j]) + pi[2 * j];
    }
    Pi
  }

  #[test]
  fn shplonk_test_1() {
    let mut rng = OsRng;
    let n = 8;
    let srs = UniversalKZGParam::<Bn256>::gen_srs_for_testing(&mut rng, n);

    let poly = vec![
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
    ];

    let eval = Fr::from(57);
    let point = vec![Fr::from(4), Fr::from(3), Fr::from(8)];



    // Phase 1 (constructing Pi polynomials and computing commitments to them)
    let Pi_0 = poly.clone();
    let Pi_1 = construct_next_Pi(Pi_0.as_slice(), point[2]);
    let Pi_2 = construct_next_Pi(Pi_1.as_slice(), point[1]);
    let Pi_3 = construct_next_Pi(Pi_2.as_slice(), point[0]);
    let Pi = vec![Pi_0, Pi_1, Pi_2, Pi_3];
    assert_eq!(Pi.len(), 4);
    assert_eq!(Pi[3].len(), 1);
    assert_eq!(Pi[3][0], eval);

    let pi_commitments = Pi
        .clone()
        .into_iter()
        .map(|poly| {
          <G1 as DlogGroup>::vartime_multiscalar_mul(&poly, &srs.powers_of_g[..poly.len()])
              .to_affine()
        })
        .collect::<Vec<G1Affine>>();


    // Phase 2 (simplified for this flow)
    let r = Fr::from(182345);
    let minus_r = -r;
    let r_squared = r * r;

    // Phase 3

    // Compute evals at r, -r, r^2 for each Pi polynomial
    let evals_at_r = Pi
        .clone()
        .into_iter()
        .map(|poly| UniPoly::new(poly).evaluate(&r))
        .collect::<Vec<Fr>>();

    let evals_at_minus_r = Pi
        .clone()
        .into_iter()
        .map(|poly| UniPoly::new(poly).evaluate(&minus_r))
        .collect::<Vec<Fr>>();

    let evals_at_r_squared = Pi
        .clone()
        .into_iter()
        .map(|poly| UniPoly::new(poly).evaluate(&r_squared))
        .collect::<Vec<Fr>>();


    let q = Fr::from(1983758);
    let q_powers = std::iter::successors(Some(Fr::one()), |&x| Some(x * q))
        .take(pi_commitments.len())
        .collect::<Vec<Fr>>();

    let mut v_0 = Fr::zero();
    evals_at_r.iter().zip(q_powers.iter()).for_each(|(v_i_at_r, q_i)| {
      v_0 = v_0 + (v_i_at_r * q_i)
    });

    let mut v_1 = Fr::zero();
    evals_at_minus_r.iter().zip(q_powers.iter()).for_each(|(v_i_at_minus_r, q_i)| {
      v_1 = v_1 + (v_i_at_minus_r * q_i)
    });

    let mut v_2 = Fr::zero();
    evals_at_r_squared.iter().zip(q_powers.iter()).for_each(|(v_i_at_r_squared, q_i)| {
      v_2 = v_2 + (v_i_at_r_squared * q_i)
    });


    // Compute B(x) = f_0(x) + q * f_1(x) + ... + q^(k-1) * f_{k-1}(x)
    let batched_Pi: UniPoly<Fr> = Pi.clone().into_iter().map(UniPoly::new).rlc(&q);

    let divident = batched_Pi;
    let divisor = vec![-q, Fr::one()];
    let (mut Q_x, R_x) = divident
        .divide_with_q_and_r(&UVKZGPoly::new(divisor.clone()))
        .unwrap();

    assert_eq!(v_0, R_x.evaluate(&r));
    assert_eq!(v_1, R_x.evaluate(&minus_r));
    assert_eq!(v_2, R_x.evaluate(&r_squared));
  }

  #[test]
  fn e2e_test_pcs_kzg_shplonk_flow() {
    let mut rng = OsRng;
    let n = 8;
    let srs = UniversalKZGParam::<Bn256>::gen_srs_for_testing(&mut rng, n);

    let poly = vec![
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
    ];

    let eval = Fr::from(57);
    let point = vec![Fr::from(4), Fr::from(3), Fr::from(8)];

    // Phase 1 (constructing Pi polynomials and computing commitments to them)
    let Pi_0 = poly.clone();
    let Pi_1 = construct_next_Pi(Pi_0.as_slice(), point[2]);
    let Pi_2 = construct_next_Pi(Pi_1.as_slice(), point[1]);
    let Pi_3 = construct_next_Pi(Pi_2.as_slice(), point[0]);
    let Pi = vec![Pi_0, Pi_1, Pi_2, Pi_3];
    assert_eq!(Pi.len(), 4);
    assert_eq!(Pi[3].len(), 1);
    assert_eq!(Pi[3][0], eval);

    let pi_commitments = Pi
        .clone()
        .into_iter()
        .map(|poly| {
          <G1 as DlogGroup>::vartime_multiscalar_mul(&poly, &srs.powers_of_g[..poly.len()])
              .to_affine()
        })
        .collect::<Vec<G1Affine>>();


    let q = Fr::from(1983758);
    let q_powers = std::iter::successors(Some(Fr::one()), |&x| Some(x * q))
        .take(pi_commitments.len())
        .collect::<Vec<Fr>>();

    // Compute B(x) = f_0(x) + q * f_1(x) + ... + q^(k-1) * f_{k-1}(x)
    let batched_Pi: UniPoly<Fr> = Pi.clone().into_iter().map(UniPoly::new).rlc(&q);

    let r = Fr::from(182345);
    let minus_r = -r;
    let r_squared = r * r;


    /*let evals_at_r = Pi
        .clone()
        .into_iter()
        .map(|poly| UniPoly::new(poly).evaluate(&r))
        .collect::<Vec<Fr>>();


    let eval_r_expected = evals_at_r.iter().zip(q_powers.iter()).map(|(eval, q)| eval * q).collect::<Vec<Fr>>().into_iter().sum::<Fr>();
    assert_eq!(evals_at_r, eval_r_expected);
    */

    let eval_r = batched_Pi.evaluate(&r);
    let eval_minus_r = batched_Pi.evaluate(&minus_r);
    let eval_r_squared = batched_Pi.evaluate(&r_squared);

    let mut C_P = G1Affine::default();
    q_powers.iter().zip(pi_commitments.iter()).for_each(|(q_i, C_i)| {
      C_P = (C_P + (C_i * q_i)).to_affine();
    });

    let C =  <G1 as DlogGroup>::vartime_multiscalar_mul(&batched_Pi.coeffs, &srs.powers_of_g[..batched_Pi.coeffs.len()])
        .to_affine();

    // D = (x - r) * (x + r) * (x - r^2) = 1 * x^3 - r^2 * x^2 - r^2 * x + r^4
    let divident = batched_Pi.clone();
    let D = UVKZGPoly::new(vec![r_squared * r_squared, -r_squared, -r_squared, Fr::one()]);
    let (mut Q_x, R_x) = divident
        .divide_with_q_and_r(&D)
        .unwrap();

    let C_Q = <G1 as DlogGroup>::vartime_multiscalar_mul(&Q_x.coeffs, &srs.powers_of_g[..Q_x.coeffs.len()])
        .to_affine();

    let a = Fr::from(241);

    let mut K_x = batched_Pi.clone();
    K_x += &(R_x.evaluate(&a));
    let mut tmp = Q_x.clone();
    tmp *= &(-D.evaluate(&a));
    K_x += &tmp;


    //let minus_batched_Pi = UniPoly::new(batched_Pi.coeffs.clone().into_iter().map(|coeff| -coeff).collect::<Vec<Fr>>());
    //let minus_R_x = UniPoly::new(R_x.coeffs.clone().into_iter().map(|coeff| -coeff).collect::<Vec<Fr>>());
    //let mut K_x = Q_x.clone();
    //K_x *= &(R_x.evaluate(&a));
    //K_x += &minus_batched_Pi;
    //K_x += &minus_R_x;


    let C_K = C_P - C_Q * D.evaluate(&a) + srs.powers_of_g[0] * R_x.evaluate(&a);

    //let C_R = <G1 as DlogGroup>::vartime_multiscalar_mul(&R_x.coeffs, &srs.powers_of_g[..R_x.coeffs.len()])
    //    .to_affine();
    //let C_K = C_Q * R_x.evaluate(&a) - C_P - C_R;

    let divident = K_x.clone();
    let divisor = UVKZGPoly::new(vec![-a, Fr::one()]);
    let (mut H_x, _) = divident
        .divide_with_q_and_r(&divisor)
        .unwrap();

    let C_H = <G1 as DlogGroup>::vartime_multiscalar_mul(&H_x.coeffs, &srs.powers_of_g[..H_x.coeffs.len()])
        .to_affine();

    let left = pairing(&C_H, &(srs.powers_of_h[1] - srs.powers_of_h[0] * a).to_affine());
    let right = pairing(&C_K.to_affine(), &srs.powers_of_h[0]);
    assert_eq!(left, right);
  }
}
