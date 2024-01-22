#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]
#[cfg(test)]
mod tests {
  use crate::provider::non_hiding_kzg::{UVKZGPoly, UniversalKZGParam};
  use crate::provider::traits::DlogGroup;
  use crate::spartan::polys::univariate::UniPoly;
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
}
