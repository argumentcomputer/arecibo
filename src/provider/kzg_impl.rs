#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]
#[cfg(test)]
mod tests {
  use crate::provider::non_hiding_kzg::{UVKZGPoly, UniversalKZGParam};
  use crate::provider::traits::DlogGroup;
  use crate::spartan::polys::univariate::UniPoly;
  use group::{Curve, Group};
  use halo2curves::bn256::{multi_miller_loop, pairing, Bn256, Fr, G1Affine, G2Prepared, G1, G2};
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
    let term1 = (&(srs.powers_of_g[0] * c - Cq * b - Cf).to_affine(), &G2Prepared::from_affine(srs.powers_of_h[0]));
    let term2 = (&Cq.to_affine(), &G2Prepared::from_affine(srs.powers_of_h[1]));
    let result = multi_miller_loop(&[term1, term2]).final_exponentiation();
    assert_eq!(result.is_identity().unwrap_u8(), 0x01);
  }
}
