//! Non-hiding Zeromorph scheme for Multilinear Polynomials.
//!
//!

use crate::{
  digest::SimpleDigestible,
  errors::{NovaError, PCSError},
  provider::{
    kzg_commitment::{
      KZGCommitmentEngine, KZGProverKey, KZGVerifierKey, UVKZGCommitment, UniversalKZGParam,
    },
    traits::DlogGroup,
  },
  spartan::polys::{multilinear::MultilinearPolynomial, univariate::UniPoly},
  traits::{
    commitment::Len, evaluation::EvaluationEngineTrait, Engine as NovaEngine, Group,
    TranscriptEngineTrait, TranscriptReprTrait,
  },
  Commitment,
};
use ff::{BatchInvert, Field, PrimeField, PrimeFieldBits};
use group::{Curve, Group as _};
use itertools::Itertools as _;
use pairing::{Engine, MillerLoopResult, MultiMillerLoop};
use rayon::{
  iter::IntoParallelRefIterator,
  prelude::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator},
};
use ref_cast::RefCast;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::{borrow::Borrow, iter, marker::PhantomData};

/// Polynomial Evaluation
#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct UVKZGEvaluation<E: Engine>(pub E::Fr);

#[derive(Debug, Clone, Eq, PartialEq, Default)]

/// Proofs
pub struct UVKZGProof<E: Engine> {
  /// proof
  pub proof: E::G1Affine,
}

/// Polynomial and its associated types
pub type UVKZGPoly<F> = UniPoly<F>;

#[derive(Debug, Clone, Eq, PartialEq, Default)]
/// KZG Polynomial Commitment Scheme on univariate polynomial.
/// Note: this is non-hiding, which is why we will implement traits on this token struct,
/// as we expect to have several impls for the trait pegged on the same instance of a pairing::Engine.
#[allow(clippy::upper_case_acronyms)]
pub struct UVKZGPCS<E> {
  #[doc(hidden)]
  phantom: PhantomData<E>,
}

impl<E: MultiMillerLoop> UVKZGPCS<E>
where
  E::G1: DlogGroup<AffineExt = E::G1Affine, ScalarExt = E::Fr>,
{
  fn commit_offset(
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
  /// Note that the scheme is not hidding
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
}

/// `ZMProverKey` is used to generate a proof
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZMProverKey<E: Engine> {
  commit_pp: KZGProverKey<E>,
  open_pp: KZGProverKey<E>,
}

/// `ZMVerifierKey` is used to check evaluation proofs for a given
/// commitment.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(bound(serialize = "E::G1Affine: Serialize, E::G2Affine: Serialize",))]
pub struct ZMVerifierKey<E: Engine> {
  vp: KZGVerifierKey<E>,
  s_offset_h: E::G2Affine,
}

impl<E: Engine> SimpleDigestible for ZMVerifierKey<E>
where
  E::G1Affine: Serialize,
  E::G2Affine: Serialize,
{
}

/// Trim the universal parameters to specialize the public parameters
/// for multilinear polynomials to the given `max_degree`, and
/// returns prover key and verifier key. `supported_size` should
/// be in range `1..params.len()`
///
/// # Panics
/// If `params.max_degree() < 2 * max_degree + 1`
//
// TODO: important, we need a better way to handle that the commitment key should be 2^max_degree sized,
// see the runtime error in commit() below
fn trim_zeromorph<E: Engine>(
  params: Arc<UniversalKZGParam<E>>,
  max_degree: usize,
) -> (ZMProverKey<E>, ZMVerifierKey<E>) {
  let (commit_pp, vp) = UniversalKZGParam::trim(params.clone(), max_degree);
  let offset = params.max_degree() - max_degree;
  let s_offset_h = params.powers_of_h[offset];
  let open_pp = KZGProverKey::new(params, offset, max_degree);

  (
    ZMProverKey { commit_pp, open_pp },
    ZMVerifierKey { vp, s_offset_h },
  )
}

/// Commitments
#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct ZMCommitment<E: Engine>(
  /// the actual commitment is an affine point.
  E::G1Affine,
);

impl<E: Engine> From<UVKZGCommitment<E>> for ZMCommitment<E> {
  fn from(value: UVKZGCommitment<E>) -> Self {
    Self(value.0)
  }
}

impl<E: Engine> From<ZMCommitment<E>> for UVKZGCommitment<E> {
  fn from(value: ZMCommitment<E>) -> Self {
    Self(value.0)
  }
}

/// Polynomial Evaluation
#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct ZMEvaluation<E: Engine>(E::Fr);

impl<E: Engine> From<UVKZGEvaluation<E>> for ZMEvaluation<E> {
  fn from(value: UVKZGEvaluation<E>) -> Self {
    Self(value.0)
  }
}

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
#[serde(bound(
  serialize = "E::G1Affine: Serialize",
  deserialize = "E::G1Affine: Deserialize<'de>"
))]
/// Proofs
pub struct ZMProof<E: Engine> {
  /// proof
  pi: E::G1Affine,
  /// Polynomial commitment to qhat
  cqhat: UVKZGCommitment<E>,
  /// Polynomial commitment to qk
  ck: Vec<UVKZGCommitment<E>>,
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
/// Zeromorph Polynomial Commitment Scheme on multilinear polynomials.
/// Note: this is non-hiding, which is why we will implement the `EvaluationEngineTrait` on this token struct,
/// as we will have several impls for the trait pegged on the same instance of a `pairing::Engine`.
#[allow(clippy::upper_case_acronyms)]
pub struct ZMPCS<E, NE> {
  #[doc(hidden)]
  phantom: PhantomData<(E, NE)>,
}

impl<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> ZMPCS<E, NE>
where
  E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
  // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
  <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>,
{
  const fn protocol_name() -> &'static [u8] {
    b"Zeromorph"
  }

  /// Generate a commitment for a polynomial
  /// Note that the scheme is not hiding
  fn commit(
    pp: impl Borrow<ZMProverKey<E>>,
    poly: &MultilinearPolynomial<E::Fr>,
  ) -> Result<ZMCommitment<E>, NovaError> {
    let pp = pp.borrow();
    if pp.commit_pp.powers_of_g().len() < poly.Z.len() {
      return Err(PCSError::LengthError.into());
    }
    UVKZGPCS::commit(&pp.commit_pp, UniPoly::ref_cast(&poly.Z)).map(|c| c.into())
  }

  /// On input a polynomial `poly` and a point `point`, outputs a proof for the
  /// same.
  fn open(
    pp: &impl Borrow<ZMProverKey<E>>,
    comm: &ZMCommitment<E>,
    poly: &MultilinearPolynomial<E::Fr>,
    point: &[E::Fr],
    eval: &ZMEvaluation<E>,
    transcript: &mut impl TranscriptEngineTrait<NE>,
  ) -> Result<ZMProof<E>, NovaError> {
    transcript.dom_sep(Self::protocol_name());

    let pp = pp.borrow();
    if pp.commit_pp.powers_of_g().len() < poly.Z.len() {
      return Err(NovaError::PCSError(PCSError::LengthError));
    }

    debug_assert_eq!(Self::commit(pp, poly).unwrap().0, comm.0);
    debug_assert_eq!(poly.evaluate(point), eval.0);

    let (quotients, remainder) = quotients(poly, point);
    debug_assert_eq!(quotients.len(), poly.get_num_vars());
    debug_assert_eq!(remainder, eval.0);

    // Compute the multilinear quotients q_k = q_k(X_0, ..., X_{k-1})
    let quotients_polys = quotients.into_iter().map(UniPoly::new).collect::<Vec<_>>();

    // Compute and absorb commitments C_{q_k} = [q_k], k = 0,...,d-1
    let q_comms = quotients_polys
      .par_iter()
      .map(|q| UVKZGPCS::commit(&pp.commit_pp, q))
      .collect::<Result<Vec<_>, _>>()?;
    q_comms.iter().for_each(|c| transcript.absorb(b"quo", c));

    // Get challenge y
    let y = transcript.squeeze(b"y")?;

    // Compute the batched, lifted-degree quotient `\hat{q}`
    // qq_hat = ∑_{i=0}^{num_vars-1} y^i * X^(2^num_vars - d_k - 1) * q_i(x)
    let (q_hat, offset) = batched_lifted_degree_quotient(y, &quotients_polys);

    // Compute and absorb the commitment C_q = [\hat{q}]
    let q_hat_comm = UVKZGPCS::commit_offset(&pp.commit_pp, &q_hat, offset)?;
    transcript.absorb(b"q_hat", &q_hat_comm);

    // Get challenges x and z
    let x = transcript.squeeze(b"x")?;
    let z = transcript.squeeze(b"z")?;

    // Compute batched degree and ZM-identity quotient polynomial pi
    let (eval_scalar, (degree_check_q_scalars, zmpoly_q_scalars)) =
      eval_and_quotient_scalars(y, x, z, point);
    // f = z * poly.Z + q_hat + (-z * Φ_n(x) * e) + ∑_k (q_scalars_k * q_k)
    let mut f = UniPoly::new(poly.Z.clone());
    f *= &z;
    f += &q_hat;
    f[0] += eval_scalar * eval.0;
    quotients_polys
      .into_iter()
      .zip_eq(degree_check_q_scalars)
      .zip_eq(zmpoly_q_scalars)
      .for_each(|((mut q, degree_check_scalar), zm_poly_scalar)| {
        q *= &(degree_check_scalar + zm_poly_scalar);
        f += &q;
      });
    debug_assert_eq!(f.evaluate(&x), E::Fr::ZERO);
    // hence uveval == Fr::ZERO

    // Compute and send proof commitment pi
    let (uvproof, _uveval): (UVKZGProof<_>, UVKZGEvaluation<_>) =
      UVKZGPCS::<E>::open(&pp.open_pp, &f, &x)?;

    let proof = ZMProof {
      pi: uvproof.proof,
      cqhat: q_hat_comm,
      ck: q_comms,
    };

    Ok(proof)
  }

  /// Verifies that `value` is the evaluation at `x` of the polynomial
  /// committed inside `comm`.
  fn verify(
    vk: &impl Borrow<ZMVerifierKey<E>>,
    transcript: &mut impl TranscriptEngineTrait<NE>,
    comm: &ZMCommitment<E>,
    point: &[E::Fr],
    evaluation: &ZMEvaluation<E>,
    proof: &ZMProof<E>,
  ) -> Result<bool, NovaError> {
    transcript.dom_sep(Self::protocol_name());

    let vk = vk.borrow();

    // Receive commitments [q_k]
    proof.ck.iter().for_each(|c| transcript.absorb(b"quo", c));

    // Challenge y
    let y = transcript.squeeze(b"y")?;

    // Receive commitment C_{q}
    transcript.absorb(b"q_hat", &proof.cqhat);

    // Challenges x, z
    let x = transcript.squeeze(b"x")?;
    let z = transcript.squeeze(b"z")?;

    let (eval_scalar, (mut q_scalars, zmpoly_q_scalars)) =
      eval_and_quotient_scalars(y, x, z, point);
    q_scalars
      .iter_mut()
      .zip_eq(zmpoly_q_scalars)
      .for_each(|(scalar, zm_poly_scalar)| {
        *scalar += zm_poly_scalar;
      });
    let scalars = [vec![E::Fr::ONE, z, eval_scalar * evaluation.0], q_scalars].concat();
    let bases = [
      vec![proof.cqhat.0, comm.0, vk.vp.g],
      proof.ck.iter().map(|c| c.0).collect(),
    ]
    .concat();
    let c = <E::G1 as DlogGroup>::vartime_multiscalar_mul(&scalars, &bases).to_affine();

    let pi = proof.pi;

    let pairing_inputs = [
      (&c, &(-vk.s_offset_h).into()),
      (
        &pi,
        &(E::G2::from(vk.vp.beta_h) - (vk.vp.h * x))
          .to_affine()
          .into(),
      ),
    ];

    let pairing_result = E::multi_miller_loop(&pairing_inputs).final_exponentiation();
    Ok(pairing_result.is_identity().into())
  }
}

/// Computes the quotient polynomials of a given multilinear polynomial with respect to a specific input point.
///
/// Given a multilinear polynomial `poly` and a point `point`, this function calculates the quotient polynomials `q_k`
/// and the evaluation at `point`, such that:
///
/// ```text
/// poly - poly(point) = Σ (X_k - point_k) * q_k(X_0, ..., X_{k-1})
/// ```
///
/// where `poly(point)` is the evaluation of `poly` at `point`, and each `q_k` is a polynomial in `k` variables.
///
/// Since our evaluations are presented in order reverse from the coefficients, if we want to interpret index `q_k`
/// to be the k-th coefficient in the polynomials returned here, the equality that holds is:
///
/// ```text
/// poly - poly(point) = Σ (X_{n-1-k} - point_{n-1-k}) * q_k(X_0, ..., X_{k-1})
/// ```
///
fn quotients<F: PrimeField>(poly: &MultilinearPolynomial<F>, point: &[F]) -> (Vec<Vec<F>>, F) {
  let num_var = poly.get_num_vars();
  assert_eq!(num_var, point.len());

  let mut remainder = poly.Z.to_vec();
  let mut quotients = point
    .iter()
    .enumerate()
    .map(|(idx, x_i)| {
      let (remainder_lo, remainder_hi) = remainder.split_at_mut(1 << (num_var - 1 - idx));
      let mut quotient = vec![F::ZERO; remainder_lo.len()];

      quotient
        .par_iter_mut()
        .zip_eq(&*remainder_lo)
        .zip_eq(&*remainder_hi)
        .for_each(|((q, r_lo), r_hi)| {
          *q = *r_hi - *r_lo;
        });
      remainder_lo
        .par_iter_mut()
        .zip_eq(remainder_hi)
        .for_each(|(r_lo, r_hi)| {
          *r_lo += (*r_hi - r_lo as &_) * x_i;
        });

      remainder.truncate(1 << (num_var - 1 - idx));

      quotient
    })
    .collect::<Vec<Vec<F>>>();
  quotients.reverse();

  (quotients, remainder[0])
}

// Compute the batched, lifted-degree quotient `\hat{q}`
fn batched_lifted_degree_quotient<F: PrimeField>(
  y: F,
  quotients_polys: &[UniPoly<F>],
) -> (UniPoly<F>, usize) {
  let num_vars = quotients_polys.len();

  let powers_of_y = (0..num_vars)
    .scan(F::ONE, |acc, _| {
      let val = *acc;
      *acc *= y;
      Some(val)
    })
    .collect::<Vec<F>>();

  #[allow(clippy::disallowed_methods)]
  let q_hat = powers_of_y
    .iter()
    .zip_eq(quotients_polys.iter().map(|qp| qp.as_ref()))
    .enumerate()
    .fold(
      vec![F::ZERO; 1 << num_vars],
      |mut q_hat, (idx, (power_of_y, q))| {
        q_hat[(1 << num_vars) - (1 << idx)..]
          .par_iter_mut()
          .zip(q)
          .for_each(|(q_hat, q)| {
            *q_hat += *power_of_y * *q;
          });
        q_hat
      },
    );

  (UniPoly::new(q_hat), 1 << (num_vars - 1))
}

/// Computes some key terms necessary for computing the partially evaluated univariate ZM polynomial
fn eval_and_quotient_scalars<F: Field>(y: F, x: F, z: F, point: &[F]) -> (F, (Vec<F>, Vec<F>)) {
  let num_vars = point.len();

  // squares_of_x = [x, x^2, .. x^{2^k}, .. x^{2^num_vars}]
  let squares_of_x = iter::successors(Some(x), |&x| Some(x.square()))
    .take(num_vars + 1)
    .collect::<Vec<_>>();
  // offsets_of_x = [Π_{j=i}^{num_vars-1} x^(2^j), i ∈ [0, num_vars-1]] = [x^(2^num_vars - d_i - 1), i ∈ [0, num_vars-1]]
  let offsets_of_x = {
    let mut offsets_of_x = squares_of_x
      .iter()
      .rev()
      .skip(1)
      .scan(F::ONE, |state, power_of_x| {
        *state *= power_of_x;
        Some(*state)
      })
      .collect::<Vec<_>>();
    offsets_of_x.reverse();
    offsets_of_x
  };

  // vs = [ (x^(2^num_vars) - 1) / (x^(2^i) - 1), i ∈ [0, num_vars-1]]
  // Note Φ_(n-i)(x^(2^i)) = (x^(2^i))^(2^(n-i) - 1) / (x^(2^i) - 1) = (x^(2^num_vars) - 1) / (x^(2^i) - 1) = vs[i]
  //      Φ_(n-i-1)(x^(2^(i+1))) = (x^(2^(i+1)))^(2^(n-i-1)) - 1 / (x^(2^(i+1)) - 1) = (x^(2^num_vars) - 1) / (x^(2^(i+1)) - 1) = vs[i+1]
  let vs = {
    let v_number = squares_of_x[num_vars] - F::ONE;
    let mut v_denoms = squares_of_x
      .iter()
      .map(|square_of_x| *square_of_x - F::ONE)
      .collect::<Vec<_>>();
    v_denoms.iter_mut().batch_invert();
    v_denoms
      .iter()
      .map(|v_denom| v_number * v_denom)
      .collect::<Vec<_>>()
  };

  // q_scalars = [- (y^i * x^(2^num_vars - d_i - 1) + z * (x^(2^i) * vs[i+1] - u_i * vs[i])), i ∈ [0, num_vars-1]]
  //           = [- (y^i * x^(2^num_vars - d_i - 1) + z * (x^(2^i) * Φ_(n-i-1)(x^(2^(i+1))) - u_i * Φ_(n-i)(x^(2^i)))), i ∈ [0, num_vars-1]]
  #[allow(clippy::disallowed_methods)]
  let q_scalars = iter::successors(Some(F::ONE), |acc| Some(*acc * y)).take(num_vars)
      .zip_eq(offsets_of_x)
      // length: num_vars + 1
      .zip(squares_of_x)
      // length: num_vars + 1
      .zip(&vs)
      .zip_eq(&vs[1..])
      .zip_eq(point.iter().rev()) // assume variables come in BE form
      .map(
        |(((((power_of_y, offset_of_x), square_of_x), v_i), v_j), u_i)| {
          (-(power_of_y * offset_of_x), -(z * (square_of_x * v_j - *u_i * v_i)))
        },
      )
      .unzip();

  // -vs[0] * z = -z * (x^(2^num_vars) - 1) / (x - 1) = -z Φ_n(x)
  (-vs[0] * z, q_scalars)
}

impl<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr, CE = KZGCommitmentEngine<E>>>
  EvaluationEngineTrait<NE> for ZMPCS<E, NE>
where
  E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
  E::G1Affine: Serialize + for<'de> Deserialize<'de>,
  E::G2Affine: Serialize + for<'de> Deserialize<'de>,
  <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>, // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
  E::Fr: PrimeFieldBits, // TODO due to use of gen_srs_for_testing, make optional
{
  type ProverKey = ZMProverKey<E>;
  type VerifierKey = ZMVerifierKey<E>;

  type EvaluationArgument = ZMProof<E>;

  fn setup(ck: Arc<UniversalKZGParam<E>>) -> (Self::ProverKey, Self::VerifierKey) {
    let len = ck.length() - 1;
    trim_zeromorph(ck, len)
  }

  fn prove(
    _ck: &UniversalKZGParam<E>,
    pk: &Self::ProverKey,
    transcript: &mut NE::TE,
    comm: &Commitment<NE>,
    poly: &[NE::Scalar],
    point: &[NE::Scalar],
    eval: &NE::Scalar,
  ) -> Result<Self::EvaluationArgument, NovaError> {
    let commitment = ZMCommitment::from(UVKZGCommitment::from(*comm));
    let polynomial = MultilinearPolynomial::new(poly.to_vec());
    let evaluation = ZMEvaluation(*eval);

    Self::open(pk, &commitment, &polynomial, point, &evaluation, transcript)
  }

  fn verify(
    vk: &Self::VerifierKey,
    transcript: &mut NE::TE,
    comm: &Commitment<NE>,
    point: &[NE::Scalar],
    eval: &NE::Scalar,
    arg: &Self::EvaluationArgument,
  ) -> Result<(), NovaError> {
    let commitment = ZMCommitment::from(UVKZGCommitment::from(*comm));
    let evaluation = ZMEvaluation(*eval);

    if !Self::verify(vk, transcript, &commitment, point, &evaluation, arg)? {
      return Err(NovaError::UnSat);
    }
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use ff::{Field, PrimeField, PrimeFieldBits};
  use group::Curve;
  use halo2curves::bn256::Bn256;
  use halo2curves::bn256::Fr as Scalar;
  use itertools::Itertools as _;
  use pairing::MultiMillerLoop;
  use rand::thread_rng;
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;
  use std::borrow::Borrow;
  use std::sync::Arc;

  use super::{quotients, UVKZGPCS};

  use crate::spartan::polys::univariate::UniPoly;
  use crate::{
    errors::PCSError,
    provider::{
      kzg_commitment::{KZGProverKey, UVKZGCommitment, UniversalKZGParam},
      non_hiding_zeromorph::{batched_lifted_degree_quotient, eval_and_quotient_scalars, ZMPCS},
      traits::DlogGroup,
      util::test_utils::prove_verify_from_num_vars,
      Bn256EngineZM,
    },
    spartan::polys::multilinear::MultilinearPolynomial,
    NovaError,
  };

  #[test]
  fn test_multiple_polynomial_size() {
    for num_vars in [4, 5, 6] {
      prove_verify_from_num_vars::<_, ZMPCS<Bn256, Bn256EngineZM>>(num_vars);
    }
  }

  #[test]
  fn test_quotients() {
    // Define size parameters
    let num_vars = 4; // Example number of variables for the multilinear polynomial

    // Construct a random multilinear polynomial f, and u such that f(u) = v.
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
    let poly = MultilinearPolynomial::random(num_vars, &mut rng);
    let u_challenge: Vec<_> = (0..num_vars).map(|_| Scalar::random(&mut rng)).collect();
    let v_evaluation = poly.evaluate(&u_challenge);

    // Compute the multilinear quotients q_k = q_k(X_0, ..., X_{k-1})
    let (quotients, constant_term) = quotients(&poly, &u_challenge);

    // Assert that the constant term is equal to v_evaluation
    assert_eq!(constant_term, v_evaluation, "The constant term should be equal to the evaluation of the polynomial at the challenge point.");

    // Check that the identity holds for a random evaluation point z
    // poly - poly(z) = Σ (X_k - z_k) * q_k(X_0, ..., X_{k-1})
    // except for our inversion of coefficient order in polynomials and points (see below)
    let z_challenge: Vec<_> = (0..num_vars).map(|_| Scalar::random(&mut rng)).collect();
    let mut result = poly.evaluate(&z_challenge);
    result -= v_evaluation;

    for (k, q_k) in quotients.iter().enumerate() {
      let q_k_poly = MultilinearPolynomial::new(q_k.clone());
      // the following looks weird because the quotient polynomials are coefficiented in reverse order from evaluation
      // IOW in 'normal evaluation order' this should be let z_partial = &z_challenge[..k];
      let z_partial = &z_challenge[z_challenge.len() - k..];

      let q_k_eval = q_k_poly.evaluate(z_partial);
      // the following looks weird because the quotient polynomials are coefficiented in reverse order from evaluation
      // IOW in 'normal evaluation order' this should be
      // result -= (z_challenge[k] - u_challenge[k]) * q_k_eval;
      result -= (z_challenge[z_challenge.len() - k - 1] - u_challenge[z_challenge.len() - k - 1])
        * q_k_eval;
    }

    // Assert that the result is zero, which verifies the correctness of the quotients
    assert!(
      bool::from(result.is_zero()),
      "The computed quotients should satisfy the polynomial identity."
    );
  }

  #[test]
  fn test_batched_lifted_degree_quotient() {
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    let num_vars = 3;
    let n = 1 << num_vars; // Assuming N = 2^num_vars

    // Define mock q_k with deg(q_k) = 2^k - 1
    let q_0 = UniPoly::new(vec![Scalar::one()]);
    let q_1 = UniPoly::new(vec![Scalar::from(2), Scalar::from(3)]);
    let q_2 = UniPoly::new(vec![
      Scalar::from(4),
      Scalar::from(5),
      Scalar::from(6),
      Scalar::from(7),
    ]);
    let quotients = vec![q_0, q_1, q_2];

    // Generate a random y challenge
    let y_challenge = Scalar::random(&mut rng);

    // Compute batched quotient \hat{q} using the function
    let batched_quotient = batched_lifted_degree_quotient(y_challenge, &quotients);

    // Now explicitly define q_k_lifted = X^{N-2^k} * q_k and compute the expected batched result
    let q_0_lifted = [vec![Scalar::zero(); n - 1], vec![Scalar::one()]].concat();
    let q_1_lifted = [
      vec![Scalar::zero(); n - 2],
      vec![Scalar::from(2), Scalar::from(3)],
    ]
    .concat();
    let q_2_lifted = [
      vec![Scalar::zero(); n - 4],
      vec![
        Scalar::from(4),
        Scalar::from(5),
        Scalar::from(6),
        Scalar::from(7),
      ],
    ]
    .concat();

    // Explicitly compute \hat{q}
    let mut batched_quotient_expected = vec![Scalar::zero(); n];
    batched_quotient_expected
      .iter_mut()
      .zip_eq(q_0_lifted)
      .zip_eq(q_1_lifted)
      .zip_eq(q_2_lifted)
      .for_each(|(((res, q_0), q_1), q_2)| {
        *res += q_0 + y_challenge * q_1 + y_challenge * y_challenge * q_2;
      });

    // Compare the computed and expected batched quotients
    assert_eq!(batched_quotient.0, UniPoly::new(batched_quotient_expected));
  }

  #[test]
  fn test_partially_evaluated_quotient_zeta() {
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    let num_vars = 3;

    // Define some mock q_k with deg(q_k) = 2^k - 1
    let _q_0 = UniPoly::new(vec![Scalar::one()]);
    let _q_1 = UniPoly::new(vec![Scalar::from(2), Scalar::from(3)]);
    let _q_2 = UniPoly::new(vec![
      Scalar::from(4),
      Scalar::from(5),
      Scalar::from(6),
      Scalar::from(7),
    ]);

    let y_challenge = Scalar::random(&mut rng);

    let x_challenge = Scalar::random(&mut rng);

    // Unused in this test
    let u_challenge: Vec<_> = (0..num_vars).map(|_| Scalar::random(&mut rng)).collect();
    let z_challenge = Scalar::random(&mut rng);

    // Construct ζ_x using the function
    let (_eval_scalar, (zeta_x_scalars, _right_quo_scalars)) =
      eval_and_quotient_scalars(y_challenge, x_challenge, z_challenge, &u_challenge);

    // Now construct ζ_x explicitly
    let n: u64 = 1 << num_vars;
    // q_batched - \sum_k q_k * y^k * x^{N - deg(q_k) - 1}
    assert_eq!(zeta_x_scalars[0], -x_challenge.pow([n - 1]));
    assert_eq!(
      zeta_x_scalars[1],
      -y_challenge * x_challenge.pow_vartime([n - 1 - 1])
    );
    assert_eq!(
      zeta_x_scalars[2],
      -y_challenge * y_challenge * x_challenge.pow_vartime([n - 3 - 1])
    );
  }

  // Evaluate phi using an inefficient formula
  fn phi<F: PrimeField>(challenge: F, n: usize) -> F {
    let length = 1 << n;
    let mut result = F::ZERO;
    let mut current = F::ONE; // Start with x^0

    for _ in 0..length {
      result += current;
      current *= challenge; // Increment the power of x for the next iteration
    }

    result
  }

  #[test]
  fn test_partially_evaluated_quotient_z() {
    let num_vars: usize = 3;

    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    // Define some mock q_k with deg(q_k) = 2^k - 1
    let _q_0 = UniPoly::new(vec![Scalar::one()]);
    let _q_1 = UniPoly::new(vec![Scalar::from(2), Scalar::from(3)]);
    let _q_2 = UniPoly::new(vec![
      Scalar::from(4),
      Scalar::from(5),
      Scalar::from(6),
      Scalar::from(7),
    ]);

    // Unused in this test
    let y_challenge = Scalar::random(&mut rng);

    let x_challenge = Scalar::random(&mut rng);
    let z_challenge = Scalar::random(&mut rng);

    let u_challenge: Vec<_> = (0..num_vars).map(|_| Scalar::random(&mut rng)).collect();

    // Construct Z_x using the function
    let (_eval_scalar, (_left_quo_scalars, zeta_x_scalars)) =
      eval_and_quotient_scalars(y_challenge, x_challenge, z_challenge, &u_challenge);

    // beware the Nova coefficient evaluation order!
    let u_rev = {
      let mut res = u_challenge.clone();
      res.reverse();
      res
    };

    // Compute Z_x directly
    for k in 0..num_vars {
      let x_pow_2k = x_challenge.pow([1 << k]);
      let x_pow_2kp1 = x_challenge.pow([1 << (k + 1)]);
      let mut scalar =
        x_pow_2k * phi(x_pow_2kp1, num_vars - k - 1) - u_rev[k] * phi(x_pow_2k, num_vars - k);
      scalar *= z_challenge;
      scalar *= -Scalar::ONE;
      assert_eq!(zeta_x_scalars[k], scalar);
    }
  }

  fn commit_filtered<E>(
    prover_param: impl Borrow<KZGProverKey<E>>,
    poly: &UniPoly<E::Fr>,
  ) -> Result<UVKZGCommitment<E>, NovaError>
  where
    E: MultiMillerLoop,
    E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::Fr: PrimeFieldBits,
  {
    let prover_param = prover_param.borrow();

    if poly.degree() > prover_param.powers_of_g().len() {
      return Err(NovaError::PCSError(PCSError::LengthError));
    }

    // We use following filter to optimise MSM for cases where scalars contain a lot of zeroes
    let initial_bases = &prover_param.powers_of_g()[..poly.coeffs.len()].to_vec();
    let mut scalars = vec![];
    let mut bases = vec![];
    for (index, scalar) in poly.coeffs.iter().enumerate() {
      if !scalar.is_zero_vartime() {
        scalars.push(*scalar);
        bases.push(initial_bases[index]);
      }
    }

    let C = <E::G1 as DlogGroup>::vartime_multiscalar_mul(&scalars, &bases);

    Ok(UVKZGCommitment(C.to_affine()))
  }

  fn test_ZM_commit_sparsity_template<E>() -> Result<(), NovaError>
  where
    E: MultiMillerLoop,
    E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
    E::Fr: PrimeFieldBits,
  {
    let degree = 10;
    let num_vars_multilinear = 3;

    let mut rng = &mut thread_rng();
    let multilinear_poly = MultilinearPolynomial::<E::Fr>::random(num_vars_multilinear, &mut rng);

    let mut random_points = vec![];
    for _ in 0..num_vars_multilinear {
      random_points.push(E::Fr::random(&mut rng));
    }

    let (quotients, _remainder) = quotients(&multilinear_poly, random_points.as_slice());
    let quotients_polys = quotients.into_iter().map(UniPoly::new).collect::<Vec<_>>();

    let (q_hat, offset) = batched_lifted_degree_quotient(E::Fr::random(&mut rng), &quotients_polys);

    let pp = Arc::new(UniversalKZGParam::<E>::gen_srs_for_testing(
      &mut rng, degree,
    ));
    let (ck, _vk) = UniversalKZGParam::trim(pp, degree);

    let commitment_expected = UVKZGPCS::commit(&ck, &q_hat)?;
    let commitment_actual_1 = commit_filtered(&ck, &q_hat)?;
    let commitment_actual_2 = UVKZGPCS::commit_offset(&ck, &q_hat, offset)?;

    assert_eq!(commitment_expected.0, commitment_actual_1.0);
    assert_eq!(commitment_expected.0, commitment_actual_2.0);

    Ok(())
  }

  #[test]
  fn test_ZM_commit_sparsity() {
    test_ZM_commit_sparsity_template::<Bn256>().expect("test failed for Bn256");
  }
}
