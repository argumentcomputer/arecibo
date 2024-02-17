//! Non-hiding variant of KZG10 scheme for univariate polynomials.
use crate::digest::SimpleDigestible;
use abomonation_derive::Abomonation;
use ff::{Field, PrimeField, PrimeFieldBits};
use group::{prime::PrimeCurveAffine, Curve, Group as _};
use pairing::{Engine, MillerLoopResult, MultiMillerLoop};
use rand_core::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
use std::{borrow::Borrow, marker::PhantomData, ops::Mul, sync::Arc};

use crate::{
  errors::{NovaError, PCSError},
  provider::traits::DlogGroup,
  provider::util::fb_msm,
  traits::{commitment::Len, Group, TranscriptReprTrait},
};

/// `UniversalParams` are the universal parameters for the KZG10 scheme.
#[derive(Debug, Clone, Eq, Serialize, Deserialize, Abomonation)]
#[serde(bound(
  serialize = "E::G1Affine: Serialize, E::G2Affine: Serialize",
  deserialize = "E::G1Affine: Deserialize<'de>, E::G2Affine: Deserialize<'de>"
))]
#[abomonation_omit_bounds]
pub struct UniversalKZGParam<E: Engine> {
  /// Group elements of the form `{ β^i G }`, where `i` ranges from 0 to
  /// `degree`.
  // this is a hack; we just assume the size of the element.
  // Look for the static assertions in provider macros for a justification
  #[abomonate_with(Vec<[u64; 8]>)]
  pub powers_of_g: Vec<E::G1Affine>,
  /// Group elements of the form `{ β^i H }`, where `i` ranges from 0 to
  /// `degree`.
  // this is a hack; we just assume the size of the element.
  // Look for the static assertions in provider macros for a justification
  #[abomonate_with(Vec<[u64; 16]>)]
  pub powers_of_h: Vec<E::G2Affine>,
}

impl<E: Engine> PartialEq for UniversalKZGParam<E> {
  fn eq(&self, other: &Self) -> bool {
    self.powers_of_g == other.powers_of_g && self.powers_of_h == other.powers_of_h
  }
}

// for the purpose of the Len trait, we count commitment bases, i.e. G1 elements
impl<E: Engine> Len for UniversalKZGParam<E> {
  fn length(&self) -> usize {
    self.powers_of_g.len()
  }
}

/// `UnivariateProverKey` is used to generate a proof
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KZGProverKey<E: Engine> {
  /// generators from the universal parameters
  uv_params: Arc<UniversalKZGParam<E>>,
  /// offset at which we start reading into the SRS
  offset: usize,
  /// maximum supported size
  supported_size: usize,
}

impl<E: Engine> KZGProverKey<E> {
  pub(in crate::provider) fn new(
    uv_params: Arc<UniversalKZGParam<E>>,
    offset: usize,
    supported_size: usize,
  ) -> Self {
    assert!(
      uv_params.max_degree() >= offset + supported_size,
      "not enough bases (req: {} from offset {}) in the UVKZGParams (length: {})",
      supported_size,
      offset,
      uv_params.max_degree()
    );
    Self {
      uv_params,
      offset,
      supported_size,
    }
  }

  pub fn powers_of_g(&self) -> &[E::G1Affine] {
    &self.uv_params.powers_of_g[self.offset..self.offset + self.supported_size]
  }
}

/// `UVKZGVerifierKey` is used to check evaluation proofs for a given
/// commitment.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(bound(serialize = "E::G1Affine: Serialize, E::G2Affine: Serialize",))]
pub struct KZGVerifierKey<E: Engine> {
  /// The generator of G1.
  pub g: E::G1Affine,
  /// The generator of G2.
  pub h: E::G2Affine,
  /// β times the above generator of G2.
  pub beta_h: E::G2Affine,
}

impl<E: Engine> SimpleDigestible for KZGVerifierKey<E>
where
  E::G1Affine: Serialize,
  E::G2Affine: Serialize,
{
}

impl<E: Engine> UniversalKZGParam<E> {
  /// Returns the maximum supported degree
  pub fn max_degree(&self) -> usize {
    self.powers_of_g.len()
  }
}

/// Trim the universal parameters to specialize the public parameters
/// for univariate polynomials to the given `supported_size`, and
/// returns prover key and verifier key. `supported_size` should
/// be in range `1..params.len()`
///
/// # Panics
/// If `supported_size` is greater than `self.max_degree()`, or `self.max_degree()` is zero.
pub fn trim<E: Engine>(
  ukzg: Arc<UniversalKZGParam<E>>,
  supported_size: usize,
) -> (KZGProverKey<E>, KZGVerifierKey<E>) {
  assert!(ukzg.max_degree() > 0, "max_degree is zero");
  let g = ukzg.powers_of_g[0];
  let h = ukzg.powers_of_h[0];
  let beta_h = ukzg.powers_of_h[1];
  let pk = KZGProverKey::new(ukzg, 0, supported_size + 1);
  let vk = KZGVerifierKey { g, h, beta_h };
  (pk, vk)
}

impl<E: Engine> UniversalKZGParam<E>
where
  E::Fr: PrimeFieldBits,
{
  /// Build SRS for testing.
  /// WARNING: THIS FUNCTION IS FOR TESTING PURPOSE ONLY.
  /// THE OUTPUT SRS SHOULD NOT BE USED IN PRODUCTION.
  pub fn gen_srs_for_testing<R: RngCore + CryptoRng>(mut rng: &mut R, max_degree: usize) -> Self {
    let beta = E::Fr::random(&mut rng);
    let g = E::G1::random(&mut rng);
    let h = E::G2::random(rng);

    let nz_powers_of_beta = (0..=max_degree)
      .scan(beta, |acc, _| {
        let val = *acc;
        *acc *= beta;
        Some(val)
      })
      .collect::<Vec<E::Fr>>();

    let window_size = fb_msm::get_mul_window_size(max_degree);
    let scalar_bits = E::Fr::NUM_BITS as usize;

    let (powers_of_g_projective, powers_of_h_projective) = rayon::join(
      || {
        let g_table = fb_msm::get_window_table(scalar_bits, window_size, g);
        fb_msm::multi_scalar_mul::<E::G1>(scalar_bits, window_size, &g_table, &nz_powers_of_beta)
      },
      || {
        let h_table = fb_msm::get_window_table(scalar_bits, window_size, h);
        fb_msm::multi_scalar_mul::<E::G2>(scalar_bits, window_size, &h_table, &nz_powers_of_beta)
      },
    );

    let mut powers_of_g = vec![E::G1Affine::identity(); powers_of_g_projective.len()];
    let mut powers_of_h = vec![E::G2Affine::identity(); powers_of_h_projective.len()];

    rayon::join(
      || E::G1::batch_normalize(&powers_of_g_projective, &mut powers_of_g),
      || E::G2::batch_normalize(&powers_of_h_projective, &mut powers_of_h),
    );

    Self {
      powers_of_g,
      powers_of_h,
    }
  }
}
/// Commitments
#[derive(Debug, Clone, Copy, Eq, PartialEq, Default, Serialize, Deserialize)]
#[serde(bound(
  serialize = "E::G1Affine: Serialize",
  deserialize = "E::G1Affine: Deserialize<'de>"
))]
pub struct UVKZGCommitment<E: Engine>(
  /// the actual commitment is an affine point.
  pub E::G1Affine,
);

impl<E: Engine> TranscriptReprTrait<E::G1> for UVKZGCommitment<E>
where
  E::G1: DlogGroup,
  // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
  <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>,
{
  fn to_transcript_bytes(&self) -> Vec<u8> {
    // TODO: avoid the round-trip through the group (to_curve .. to_coordinates)
    let (x, y, is_infinity) = self.0.to_curve().to_coordinates();
    let is_infinity_byte = (!is_infinity).into();
    [
      x.to_transcript_bytes(),
      y.to_transcript_bytes(),
      [is_infinity_byte].to_vec(),
    ]
    .concat()
  }
}

/// Polynomial Evaluation
#[derive(Debug, Eq, PartialEq, Default)]
pub struct UVKZGEvaluation<E: Engine>(pub E::Fr);

#[derive(Debug, Eq, PartialEq, Default)]

/// Proofs
pub struct UVKZGProof<E: Engine> {
  /// proof
  pub proof: E::G1Affine,
}

/// Polynomial and its associated types
type UVKZGPoly<F> = crate::spartan::polys::univariate::UniPoly<F>;

#[derive(Debug, Eq, PartialEq, Default)]
/// KZG Polynomial Commitment Scheme on univariate polynomial.
/// Note: this is non-hiding, which is why we will implement traits on this token struct,
/// as we expect to have several impls for the trait pegged on the same instance of a `pairing::Engine`.
#[allow(clippy::upper_case_acronyms)]
pub struct UVKZGPCS<E> {
  #[doc(hidden)]
  phantom: PhantomData<E>,
}

impl<E: MultiMillerLoop> UVKZGPCS<E>
where
  E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
{
  pub fn commit_offset(
    prover_param: impl Borrow<KZGProverKey<E>>,
    poly: &UVKZGPoly<E::Fr>,
    offset: usize,
  ) -> Result<UVKZGCommitment<E>, NovaError> {
    let prover_param = prover_param.borrow();

    if poly.degree() > prover_param.powers_of_g().len() {
      return Err(NovaError::PCSError(PCSError::LengthError));
    }

    let scalars = poly.coeffs.as_slice();
    let bases = prover_param.powers_of_g();

    // We can avoid some scalar multiplications if 'scalars' contains a lot of leading zeroes using
    // offset, that points where non-zero scalars start.
    let C = <E::G1 as DlogGroup>::vartime_multiscalar_mul(
      &scalars[offset..],
      &bases[offset..scalars.len()],
    );

    Ok(UVKZGCommitment(C.to_affine()))
  }

  /// Generate a commitment for a polynomial
  /// Note that the scheme is not hiding
  pub fn commit(
    prover_param: impl Borrow<KZGProverKey<E>>,
    poly: &UVKZGPoly<E::Fr>,
  ) -> Result<UVKZGCommitment<E>, NovaError> {
    let prover_param = prover_param.borrow();

    if poly.degree() > prover_param.powers_of_g().len() {
      return Err(NovaError::PCSError(PCSError::LengthError));
    }
    let C = <E::G1 as DlogGroup>::vartime_multiscalar_mul(
      poly.coeffs.as_slice(),
      &prover_param.powers_of_g()[..poly.coeffs.len()],
    );
    Ok(UVKZGCommitment(C.to_affine()))
  }

  /// On input a polynomial `p` and a point `point`, outputs a proof for the
  /// same.
  pub fn open(
    prover_param: impl Borrow<KZGProverKey<E>>,
    polynomial: &UVKZGPoly<E::Fr>,
    point: &E::Fr,
  ) -> Result<(UVKZGProof<E>, UVKZGEvaluation<E>), NovaError> {
    let prover_param = prover_param.borrow();
    let divisor = UVKZGPoly {
      coeffs: vec![-*point, E::Fr::ONE],
    };
    let witness_polynomial = polynomial
      .divide_with_q_and_r(&divisor)
      .map(|(q, _r)| q)
      .ok_or(NovaError::PCSError(PCSError::ZMError))?;
    let proof = <E::G1 as DlogGroup>::vartime_multiscalar_mul(
      witness_polynomial.coeffs.as_slice(),
      &prover_param.powers_of_g()[..witness_polynomial.coeffs.len()],
    );
    let evaluation = UVKZGEvaluation(polynomial.evaluate(point));

    Ok((
      UVKZGProof {
        proof: proof.to_affine(),
      },
      evaluation,
    ))
  }

  /// Verifies that `value` is the evaluation at `x` of the polynomial
  /// committed inside `comm`.
  #[allow(dead_code, clippy::unnecessary_wraps)]
  fn verify(
    verifier_param: impl Borrow<KZGVerifierKey<E>>,
    commitment: &UVKZGCommitment<E>,
    point: &E::Fr,
    proof: &UVKZGProof<E>,
    evaluation: &UVKZGEvaluation<E>,
  ) -> Result<bool, NovaError> {
    let verifier_param = verifier_param.borrow();

    let pairing_inputs: Vec<(E::G1Affine, E::G2Prepared)> = vec![
      (
        (verifier_param.g.mul(evaluation.0) - proof.proof.mul(point) - commitment.0.to_curve())
          .to_affine(),
        verifier_param.h.into(),
      ),
      (proof.proof, verifier_param.beta_h.into()),
    ];
    #[allow(clippy::map_identity)] // this does by_ref() on a tuple
    let pairing_input_refs = pairing_inputs
      .iter()
      .map(|(a, b)| (a, b))
      .collect::<Vec<_>>();
    let pairing_result = E::multi_miller_loop(pairing_input_refs.as_slice()).final_exponentiation();
    Ok(pairing_result.is_identity().into())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::spartan::polys::univariate::UniPoly;
  use rand::{thread_rng, Rng};
  use rand_core::{CryptoRng, RngCore};

  fn random<F: PrimeField, R: RngCore + CryptoRng>(degree: usize, mut rng: &mut R) -> UVKZGPoly<F> {
    let coeffs = (0..=degree).map(|_| F::random(&mut rng)).collect();
    UniPoly::new(coeffs)
  }

  fn end_to_end_test_template<E>() -> Result<(), NovaError>
  where
    E: MultiMillerLoop,
    E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::Fr: PrimeFieldBits,
  {
    for _ in 0..100 {
      let mut rng = &mut thread_rng();
      let degree = rng.gen_range(2..20);

      let pp = Arc::new(UniversalKZGParam::<E>::gen_srs_for_testing(
        &mut rng, degree,
      ));
      let (ck, vk) = trim(pp, degree);
      let p = random(degree, rng);
      let comm = UVKZGPCS::<E>::commit(&ck, &p)?;
      let point = E::Fr::random(rng);
      let (proof, value) = UVKZGPCS::<E>::open(&ck, &p, &point)?;
      assert!(
        UVKZGPCS::<E>::verify(&vk, &comm, &point, &proof, &value)?,
        "proof was incorrect for max_degree = {}, polynomial_degree = {}",
        degree,
        p.degree(),
      );
    }
    Ok(())
  }

  #[test]
  fn end_to_end_test() {
    end_to_end_test_template::<halo2curves::bn256::Bn256>().expect("test failed for Bn256");
  }
}
