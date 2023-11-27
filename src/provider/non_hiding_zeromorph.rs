//! Non-hiding Zeromorph scheme for Multilinear Polynomials.
//!
//!

use crate::{
  errors::{NovaError, PCSError},
  provider::{
    non_hiding_kzg::{
      UVKZGCommitment, UVKZGEvaluation, UVKZGPoly, UVKZGProof, UVKZGProverKey, UVKZGVerifierKey,
      UVUniversalKZGParam, UVKZGPCS,
    },
    DlogGroup,
  },
  spartan::polys::multilinear::MultilinearPolynomial,
  traits::{
    commitment::Len, evaluation::EvaluationEngineTrait, Engine as NovaEngine, Group,
    TranscriptEngineTrait, TranscriptReprTrait,
  },
  Commitment,
};
use abomonation_derive::Abomonation;
use ff::{BatchInvert, Field, PrimeField, PrimeFieldBits};
use group::{Curve, Group as _};
use pairing::{Engine, MillerLoopResult, MultiMillerLoop};
use rayon::prelude::{
  IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
};
use ref_cast::RefCast;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{borrow::Borrow, iter, marker::PhantomData};

use super::kzg_commitment::KZGCommitmentEngine;

/// `ZMProverKey` is used to generate a proof
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize, Abomonation)]
#[abomonation_omit_bounds]
#[serde(bound(
  serialize = "E::G1Affine: Serialize",
  deserialize = "E::G1Affine: Deserialize<'de>"
))]
pub struct ZMProverKey<E: Engine> {
  commit_pp: UVKZGProverKey<E>,
  open_pp: UVKZGProverKey<E>,
}

/// `ZMVerifierKey` is used to check evaluation proofs for a given
/// commitment.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize, Abomonation)]
#[abomonation_omit_bounds]
#[serde(bound(
  serialize = "E::G1Affine: Serialize, E::G2Affine: Serialize",
  deserialize = "E::G1Affine: Deserialize<'de>, E::G2Affine: Deserialize<'de>"
))]
pub struct ZMVerifierKey<E: Engine> {
  vp: UVKZGVerifierKey<E>,
  #[abomonate_with([u64; 16])] // this is a hack; we just assume the size of the element.
  s_offset_h: E::G2Affine,
}

/// Trim the universal parameters to specialize the public parameters
/// for multilinear polynomials to the given `max_degree`, and
/// returns prover key and verifier key. `supported_size` should
/// be in range `1..params.len()`
///
/// # Panics
/// If `supported_size` is greater than `self.max_degree()`, or `self.max_degree()` is zero.
//
// TODO: important, we need a better way to handle that the commitment key should be 2^max_degree sized,
// see the runtime error in commit() below
pub fn trim<E: Engine>(
  params: &UVUniversalKZGParam<E>,
  max_degree: usize,
) -> (ZMProverKey<E>, ZMVerifierKey<E>) {
  let (commit_pp, vp) = params.trim(max_degree);
  let offset = params.powers_of_g.len() - max_degree;
  let open_pp = {
    let offset_powers_of_g1 = params.powers_of_g[offset..].to_vec();
    UVKZGProverKey {
      powers_of_g: offset_powers_of_g1,
    }
  };
  let s_offset_h = params.powers_of_h[offset];

  (
    ZMProverKey { commit_pp, open_pp },
    ZMVerifierKey { vp, s_offset_h },
  )
}

/// Commitments
#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct ZMCommitment<E: Engine>(
  /// the actual commitment is an affine point.
  pub E::G1Affine,
);

impl<E: Engine> From<UVKZGCommitment<E>> for ZMCommitment<E> {
  fn from(value: UVKZGCommitment<E>) -> Self {
    ZMCommitment(value.0)
  }
}

impl<E: Engine> From<ZMCommitment<E>> for UVKZGCommitment<E> {
  fn from(value: ZMCommitment<E>) -> Self {
    UVKZGCommitment(value.0)
  }
}

/// Polynomial Evaluation
#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct ZMEvaluation<E: Engine>(E::Fr);

impl<E: Engine> From<UVKZGEvaluation<E>> for ZMEvaluation<E> {
  fn from(value: UVKZGEvaluation<E>) -> Self {
    ZMEvaluation(value.0)
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
  pub pi: E::G1Affine,
  /// Polynomial commitment to qhat
  pub cqhat: UVKZGCommitment<E>,
  /// Polynomial commitment to qk
  pub ck: Vec<UVKZGCommitment<E>>,
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
/// Zeromorph Polynomial Commitment Scheme on multilinear polynomials.
/// Note: this is non-hiding, which is why we will implement the EvaluationEngineTrait on this token struct,
/// as we will have several impls for the trait pegged on the same instance of a pairing::Engine.
pub struct ZMPCS<E, NE> {
  #[doc(hidden)]
  phantom: PhantomData<(E, NE)>,
}

impl<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> ZMPCS<E, NE>
where
  E::G1: DlogGroup<PreprocessedGroupElement = E::G1Affine, Scalar = E::Fr>,
  // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
  <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>,
{
  const fn protocol_name() -> &'static [u8] {
    b"Zeromorph"
  }

  /// Generate a commitment for a polynomial
  /// Note that the scheme is not hidding
  pub fn commit(
    pp: impl Borrow<ZMProverKey<E>>,
    poly: &MultilinearPolynomial<E::Fr>,
  ) -> Result<ZMCommitment<E>, NovaError> {
    let pp = pp.borrow();
    if pp.commit_pp.powers_of_g.len() < poly.Z.len() {
      return Err(PCSError::LengthError.into());
    }
    UVKZGPCS::commit(&pp.commit_pp, UVKZGPoly::ref_cast(&poly.Z)).map(|c| c.into())
  }

  /// Generate a commitment for a list of polynomials
  pub fn batch_commit(
    prover_param: impl Borrow<ZMProverKey<E>>,
    polys: &[MultilinearPolynomial<E::Fr>],
  ) -> Result<Vec<ZMCommitment<E>>, NovaError> {
    let prover_param = prover_param.borrow();

    polys
      .into_par_iter()
      .map(|poly| Self::commit(prover_param, poly))
      .collect::<Result<Vec<ZMCommitment<E>>, NovaError>>()
  }

  /// On input a polynomial `poly` and a point `point`, outputs a proof for the
  /// same.
  pub fn open(
    pp: &impl Borrow<ZMProverKey<E>>,
    comm: &ZMCommitment<E>,
    poly: &MultilinearPolynomial<E::Fr>,
    point: &[E::Fr],
    eval: &ZMEvaluation<E>,
    transcript: &mut impl TranscriptEngineTrait<NE>,
  ) -> Result<ZMProof<E>, NovaError> {
    transcript.dom_sep(Self::protocol_name());

    let pp = pp.borrow();
    if pp.commit_pp.powers_of_g.len() < poly.Z.len() {
      return Err(NovaError::PCSError(PCSError::LengthError));
    }

    debug_assert_eq!(Self::commit(pp, poly).unwrap().0, comm.0);
    debug_assert_eq!(poly.evaluate(point), eval.0);

    let (quotients, remainder) = quotients(poly, point);
    debug_assert_eq!(quotients.len(), poly.get_num_vars());
    debug_assert_eq!(remainder, eval.0);

    // TODO: this should be a Cow
    // Compute the multilinear quotients q_k = q_k(X_0, ..., X_{k-1})
    let quotients_polys = quotients
      .into_iter()
      .map(UVKZGPoly::new)
      .collect::<Vec<_>>();

    // Compute and absorb commitments C_{q_k} = [q_k], k = 0,...,d-1
    let q_comms = quotients_polys
      .iter()
      .map(|q| UVKZGPCS::commit(&pp.commit_pp, q))
      .collect::<Result<Vec<_>, _>>()?;
    q_comms.iter().for_each(|c| transcript.absorb(b"quo", c));

    // Get challenge y
    let y = transcript.squeeze(b"y")?;

    // Compute the batched, lifted-degree quotient `\hat{q}`
    // q_hat = \sum_{i=0}^{num_vars-1} y^i * q_i(x)
    let q_hat = batched_lifted_degree_quotient(y, &quotients_polys);
    // Compute and absorb the commitment C_q = [\hat{q}]
    let q_hat_comm = UVKZGPCS::commit(&pp.commit_pp, &q_hat)?;
    transcript.absorb(b"q_hat", &q_hat_comm);

    // Get challenges x and z
    let x = transcript.squeeze(b"x")?;
    let z = transcript.squeeze(b"z")?;

    // Compute batched degree and ZM-identity quotient polynomial pi
    let (eval_scalar, q_scalars) = eval_and_quotient_scalars(y, x, z, point);
    // f = z * poly.Z + q\_hat + (-z * Φ_n(x) * e) + \sum_k (q\_scalars_k * q_k)
    let mut f = UVKZGPoly::new(poly.Z.clone());
    f *= &z;
    f += &q_hat;
    f[0] += eval_scalar * eval.0;
    quotients_polys
      .into_iter()
      .zip(q_scalars)
      .for_each(|(mut q, scalar)| {
        q *= &scalar;
        f += &q;
      });
    debug_assert_eq!(f.evaluate(&x), E::Fr::ZERO);
    // hence uveval == Fr::ZERO

    // Compute and send proof commitment pi
    let (uvproof, _uveval): (UVKZGProof<_>, UVKZGEvaluation<_>) =
      UVKZGPCS::<E>::open(&pp.open_pp, &f, &x).map(|(proof, eval)| (proof, eval))?;

    let proof = ZMProof {
      pi: uvproof.proof,
      cqhat: q_hat_comm,
      ck: q_comms,
    };

    Ok(proof)
  }

  /// Verifies that `value` is the evaluation at `x` of the polynomial
  /// committed inside `comm`.
  pub fn verify(
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

    let (eval_scalar, q_scalars) = eval_and_quotient_scalars(y, x, z, point);
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
/// Since our evaluations are presented in order reverse from the coefficients, if we want to interpret index q_k
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
    .iter() // assume polynomial variables come in LE form
    .enumerate()
    .map(|(idx, x_i)| {
      let (remainder_lo, remainder_hi) = remainder.split_at_mut(1 << (num_var - 1 - idx));
      let mut quotient = vec![F::ZERO; remainder_lo.len()];

      quotient
        .par_iter_mut()
        .zip(&*remainder_lo)
        .zip(&*remainder_hi)
        .for_each(|((q, r_lo), r_hi)| {
          *q = *r_hi - *r_lo;
        });
      remainder_lo
        .par_iter_mut()
        .zip(remainder_hi)
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
  quotients_polys: &[UVKZGPoly<F>],
) -> UVKZGPoly<F> {
  let num_vars = quotients_polys.len();

  let powers_of_y = (0..num_vars)
    .scan(y, |acc, _| {
      let val = *acc;
      *acc *= y;
      Some(val)
    })
    .collect::<Vec<F>>();

  let q_hat = powers_of_y
    .iter()
    .zip(quotients_polys.iter().map(|qp| qp.as_ref()))
    .enumerate()
    .fold(
      vec![F::ZERO; 1 << num_vars],
      |mut q_hat, (idx, (power_of_y, q))| {
        let offset = q_hat.len() - (1 << idx);
        q_hat[offset..]
          .par_iter_mut()
          .zip(q)
          .for_each(|(q_hat, q)| {
            *q_hat += *power_of_y * *q;
          });
        q_hat
      },
    );
  UVKZGPoly::new(q_hat)
}

/// Computes some key terms necessary for computing the partially evaluated univariate ZM polynomial
fn eval_and_quotient_scalars<F: Field>(y: F, x: F, z: F, point: &[F]) -> (F, Vec<F>) {
  let num_vars = point.len();

  // squares_of_x = [x, x^2, .. x^{2^k}, .. x^{2^num_vars}]
  let squares_of_x = iter::successors(Some(x), |&x| Some(x.square()))
    .take(num_vars + 1)
    .collect::<Vec<_>>();
  // offsets_of_x = [Π_{j=i}^{num_vars-1} x^{2^j}, i \in 0..=num_vars-1] = [x^{2^num_vars - 2^i}, i \in 0..=num_vars-1]
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

  // vs = [ \frac{(x^{2^{num_vars}} - 1)}{x^{2^i} - 1}, i \in 0..=num_vars-1]
  // Note Φ_{n-i}(x^{2^i}) = \frac{(x^{2^i})^{2^{n-i|} - 1}{x^{2^i} - 1} = \frac{(x^{2^{num_vars}} - 1)}{x^{2^i} - 1} = vs[i]
  //      Φ_{n-i-1}(x^{2^{i+1}}) = \frac{(x^{2^{i+1}})^{2^{n-i-1}} - 1}{x^{2^{i+1}} - 1} = \frac{(x^{2^{num_vars}} - 1)}{x^{2^{i+1}} - 1} = vs[i+1]
  let vs = {
    let v_numer = squares_of_x[num_vars] - F::ONE;
    let mut v_denoms = squares_of_x
      .iter()
      .map(|square_of_x| *square_of_x - F::ONE)
      .collect::<Vec<_>>();
    v_denoms.iter_mut().batch_invert();
    v_denoms
      .iter()
      .map(|v_denom| v_numer * v_denom)
      .collect::<Vec<_>>()
  };

  // q_scalars = [- (y^i * x^{2^num_vars - 2^i} + z * (x^{2^i} * vs_{i+1} - u_i * vs_i)), i = 0..=num_vars-1]
  //           = [- (y^i * x^{2^num_vars - 2^i} + z * (x^{2^i} * Φ_{n-i-1}(x^{2^{i+1}}) - u_i * Φ_{n-i}(x^{2^i}))), i = 0..=num_vars-1]
  let q_scalars = iter::successors(Some(y), |acc| Some(*acc * y))
    .zip(offsets_of_x)
    .zip(squares_of_x)
    .zip(&vs)
    .zip(&vs[1..])
    .zip(point.iter().rev()) // assume variables come in LE form u_n..u_0
    .map(
      |(((((power_of_y, offset_of_x), square_of_x), v_i), v_j), u_i)| {
        -(power_of_y * offset_of_x + z * (square_of_x * v_j - *u_i * v_i))
      },
    )
    .collect::<Vec<_>>();

  // -vs[0] * z = -z \frac{x^{2^{num\_vars}} - 1}{x - 1} = -z Φ_n(x)
  (-vs[0] * z, q_scalars)
}

impl<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr, CE = KZGCommitmentEngine<E>>>
  EvaluationEngineTrait<NE> for ZMPCS<E, NE>
where
  E::G1: DlogGroup<PreprocessedGroupElement = E::G1Affine, Scalar = E::Fr>,
  E::G1Affine: Serialize + DeserializeOwned,
  E::G2Affine: Serialize + DeserializeOwned,
  <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>, // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
  E::Fr: PrimeFieldBits, // TODO due to use of gen_srs_for_testing, make optional
{
  type ProverKey = ZMProverKey<E>;
  type VerifierKey = ZMVerifierKey<E>;

  type EvaluationArgument = ZMProof<E>;

  fn setup(ck: &UVUniversalKZGParam<E>) -> (Self::ProverKey, Self::VerifierKey) {
    // TODO: refine!!
    trim(ck, ck.length() - 1)
  }

  fn prove(
    _ck: &UVUniversalKZGParam<E>,
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

    ZMPCS::open(pk, &commitment, &polynomial, point, &evaluation, transcript)
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

    ZMPCS::verify(vk, transcript, &commitment, point, &evaluation, arg)?;
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use std::iter;

  use ff::{Field, PrimeFieldBits};
  use halo2curves::bn256::Bn256;
  use pairing::MultiMillerLoop;
  use rand::thread_rng;
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;

  use super::quotients;
  use crate::{
    provider::{
      bn256_grumpkin::{bn256, Bn256Engine},
      keccak::Keccak256Transcript,
      non_hiding_kzg::{UVKZGPoly, UVUniversalKZGParam},
      non_hiding_zeromorph::{batched_lifted_degree_quotient, trim, ZMEvaluation, ZMPCS},
      DlogGroup,
    },
    spartan::polys::multilinear::MultilinearPolynomial,
    traits::{Engine as NovaEngine, Group, TranscriptEngineTrait, TranscriptReprTrait},
  };

  fn commit_open_verify_with<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>>()
  where
    E::G1: DlogGroup<PreprocessedGroupElement = E::G1Affine, Scalar = E::Fr>,
    <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>, // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
    E::Fr: PrimeFieldBits,
  {
    let max_vars = 16;
    let mut rng = thread_rng();
    let max_poly_size = 1 << (max_vars + 1);
    let universal_setup = UVUniversalKZGParam::<E>::gen_srs_for_testing(&mut rng, max_poly_size);

    for num_vars in 3..max_vars {
      // this takes a while, run in --release
      // Setup
      let (pp, vk) = {
        let poly_size = 1 << (num_vars + 1);

        trim(&universal_setup, poly_size)
      };

      // Commit and open
      let mut transcript = Keccak256Transcript::<NE>::new(b"test");
      let poly = MultilinearPolynomial::<E::Fr>::random(num_vars, &mut thread_rng());
      let comm = ZMPCS::<E, NE>::commit(&pp, &poly).unwrap();
      // TODO: make sure the commitment drives the choice of the point challenge, i.e. that the commitment is absorbed in the transcript
      let point = iter::from_fn(|| transcript.squeeze(b"pt").ok())
        .take(num_vars)
        .collect::<Vec<_>>();
      let eval = ZMEvaluation(poly.evaluate(&point));

      let mut transcript_prover = Keccak256Transcript::<NE>::new(b"test");
      let proof = ZMPCS::open(&pp, &comm, &poly, &point, &eval, &mut transcript_prover).unwrap();

      // Verify
      let mut transcript_verifier = Keccak256Transcript::<NE>::new(b"test");
      let result = ZMPCS::verify(
        &vk,
        &mut transcript_verifier,
        &comm,
        point.as_slice(),
        &eval,
        &proof,
      );

      // check both random oracles are synced, as expected
      assert_eq!(
        transcript_prover.squeeze(b"test"),
        transcript_verifier.squeeze(b"test")
      );

      result.unwrap();
    }
  }

  #[test]
  fn test_commit_open_verify() {
    commit_open_verify_with::<Bn256, Bn256Engine>();
  }

  #[test]
  fn test_quotients() {
    // Define size parameters
    let num_vars = 4; // Example number of variables for the multilinear polynomial

    // Construct a random multilinear polynomial f, and u such that f(u) = v.
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
    let poly = MultilinearPolynomial::random(num_vars, &mut rng);
    let u_challenge: Vec<_> = (0..num_vars)
      .map(|_| bn256::Scalar::random(&mut rng))
      .collect();
    let v_evaluation = poly.evaluate(&u_challenge);

    // Compute the multilinear quotients q_k = q_k(X_0, ..., X_{k-1})
    let (quotients, constant_term) = quotients(&poly, &u_challenge);

    // Assert that the constant term is equal to v_evaluation
    assert_eq!(constant_term, v_evaluation, "The constant term should be equal to the evaluation of the polynomial at the challenge point.");

    // Check that the identity holds for a random evaluation point z
    // poly - poly(z) = Σ (X_k - z_k) * q_k(X_0, ..., X_{k-1})
    // except for our inversion of coefficient order in polynomials and points (see below)
    let z_challenge: Vec<_> = (0..num_vars)
      .map(|_| bn256::Scalar::random(&mut rng))
      .collect();
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
    // Define the field and polynomial types
    type Fr = bn256::Scalar;
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    let num_vars = 3;
    let n = 1 << num_vars; // Assuming N = 2^num_vars

    // Define mock q_k with deg(q_k) = 2^k - 1
    let q_0 = UVKZGPoly::new(vec![Fr::one()]);
    let q_1 = UVKZGPoly::new(vec![Fr::from(2), Fr::from(3)]);
    let q_2 = UVKZGPoly::new(vec![Fr::from(4), Fr::from(5), Fr::from(6), Fr::from(7)]);
    let quotients = vec![q_0, q_1, q_2];

    // Generate a random y challenge
    let y_challenge = Fr::random(&mut rng); // Assuming rng is a random number generator

    // Compute batched quotient \hat{q} using the function
    let batched_quotient = batched_lifted_degree_quotient(y_challenge, &quotients);

    // Now explicitly define q_k_lifted = X^{N-2^k} * q_k and compute the expected batched result
    let q_0_lifted = [vec![Fr::zero(); n - 1], vec![Fr::one()]].concat();
    let q_1_lifted = [vec![Fr::zero(); n - 2], vec![Fr::from(2), Fr::from(3)]].concat();
    let q_2_lifted = [
      vec![Fr::zero(); n - 4],
      vec![Fr::from(4), Fr::from(5), Fr::from(6), Fr::from(7)],
    ]
    .concat();

    // Explicitly compute \hat{q}
    let mut batched_quotient_expected = vec![Fr::zero(); n];
    batched_quotient_expected
      .iter_mut()
      .zip(q_0_lifted)
      .zip(q_1_lifted)
      .zip(q_2_lifted)
      .for_each(|(((res, q_0), q_1), q_2)| {
        *res += y_challenge * q_0
          + y_challenge * y_challenge * q_1
          + y_challenge * y_challenge * y_challenge * q_2;
      });

    // Compare the computed and expected batched quotients
    assert_eq!(batched_quotient, UVKZGPoly::new(batched_quotient_expected));
  }
}
