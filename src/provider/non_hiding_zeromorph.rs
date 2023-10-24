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
use ff::{BatchInvert, Field, PrimeField};
use group::{Curve, Group as _};
use pairing::{Engine, MillerLoopResult, MultiMillerLoop};
use rayon::prelude::{
  IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
};
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
    // TODO: remove the undue clone in the creation of an UVKZGPoly here
    UVKZGPCS::commit(&pp.commit_pp, &UVKZGPoly::new(poly.Z.clone())).map(|c| c.into())
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

    let num_vars = poly.get_num_vars();
    let pp = pp.borrow();
    if pp.commit_pp.powers_of_g.len() < poly.Z.len() {
      return Err(NovaError::PCSError(PCSError::LengthError));
    }

    debug_assert_eq!(Self::commit(pp, poly).unwrap().0, comm.0);
    debug_assert_eq!(poly.evaluate(point), eval.0);

    let (quotients, remainder) = quotients(poly, point);
    debug_assert_eq!(remainder, eval.0);

    // TODO: this should be a Cow
    let quotients_polys = quotients
      .into_iter()
      .map(UVKZGPoly::new)
      .collect::<Vec<_>>();

    let q_comms = quotients_polys
      .iter()
      .map(|q| UVKZGPCS::commit(&pp.commit_pp, q))
      .collect::<Result<Vec<_>, _>>()?;
    q_comms.iter().for_each(|c| transcript.absorb(b"quo", c));

    let y = transcript.squeeze(b"y")?;

    let powers_of_y = (0..num_vars)
      .scan(y, |acc, _| {
        let val = *acc;
        *acc *= y;
        Some(val)
      })
      .collect::<Vec<E::Fr>>();

    let q_hat = {
      let q_hat = powers_of_y
        .iter()
        .zip(quotients_polys.iter().map(|qp| qp.as_ref()))
        .enumerate()
        .fold(
          vec![E::Fr::ZERO; 1 << num_vars],
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
    };
    let q_hat_comm = UVKZGPCS::commit(&pp.commit_pp, &q_hat)?;
    transcript.absorb(b"q_hat", &q_hat_comm);

    let x = transcript.squeeze(b"x")?;

    let z = transcript.squeeze(b"z")?;

    let (eval_scalar, q_scalars) = eval_and_quotient_scalars(y, x, z, point);

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
    proof: ZMProof<E>,
  ) -> Result<bool, NovaError> {
    transcript.dom_sep(Self::protocol_name());

    let vk = vk.borrow();

    proof.ck.iter().for_each(|c| transcript.absorb(b"quo", c));
    let y = transcript.squeeze(b"y")?;

    transcript.absorb(b"q_hat", &proof.cqhat);

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

/// Compute quotient polynomials of the polynomial w.r.t. an input point
/// i.e. q_k s.t. $$self - v = \Sum_{k=0}^(n-1) q_k (X_k-point_k)$$
///
/// The polynomials q_k can be computed explicitly as the difference of the partial evaluation of self in the last
/// (n - k) variables at, respectively, point'' = (point_k + 1, point_{k+1}, ..., point_{n-1}) and
/// point' = (point_k, ..., point_{n-1}).
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

fn eval_and_quotient_scalars<F: Field>(y: F, x: F, z: F, point: &[F]) -> (F, Vec<F>) {
  let num_vars = point.len();

  let squares_of_x = iter::successors(Some(x), |&x| Some(x.square()))
    .take(num_vars + 1)
    .collect::<Vec<_>>();
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
  let q_scalars = iter::successors(Some(y), |acc| Some(*acc * y))
    .zip(offsets_of_x)
    .zip(squares_of_x)
    .zip(&vs)
    .zip(&vs[1..])
    .zip(point.iter().rev()) // assume variables come in LE form
    .map(
      |(((((power_of_y, offset_of_x), square_of_x), v_i), v_j), u_i)| {
        -(power_of_y * offset_of_x + z * (square_of_x * v_j - *u_i * v_i))
      },
    )
    .collect::<Vec<_>>();

  (-vs[0] * z, q_scalars)
}

impl<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr, CE = KZGCommitmentEngine<E>>>
  EvaluationEngineTrait<NE> for ZMPCS<E, NE>
where
  E::G1: DlogGroup<PreprocessedGroupElement = E::G1Affine, Scalar = E::Fr>,
  E::G1Affine: Serialize + DeserializeOwned,
  E::G2Affine: Serialize + DeserializeOwned,
    // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
    <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>,
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
    // TODO: the following two lines will need to change base
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

    // TODO: this clone is unsightly!
    ZMPCS::verify(vk, transcript, &commitment, point, &evaluation, arg.clone())?;
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use std::iter;

  use ff::FromUniformBytes;
  use halo2curves::bn256::Bn256;
  use pairing::MultiMillerLoop;
  use rand::{thread_rng, Rng};
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;

  use super::quotients;
  use crate::{
    provider::{
      bn256_grumpkin::{bn256, Bn256Engine},
      keccak::Keccak256Transcript,
      non_hiding_kzg::UVUniversalKZGParam,
      non_hiding_zeromorph::{trim, ZMEvaluation, ZMPCS},
      DlogGroup,
    },
    spartan::polys::multilinear::MultilinearPolynomial,
    traits::{Engine as NovaEngine, Group, TranscriptEngineTrait, TranscriptReprTrait},
  };

  fn commit_open_verify_with<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>>()
  where
    E::G1: DlogGroup<PreprocessedGroupElement = E::G1Affine, Scalar = E::Fr>,
    // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
    <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>,
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
        proof,
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
  fn test_quo() {
    let num_vars = 10;
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
    let poly = MultilinearPolynomial::random(num_vars, &mut rng);

    let point: Vec<_> = std::iter::from_fn(|| {
      let mut bytes = [0u8; 64];
      rng.fill(&mut bytes);
      bn256::Scalar::from_uniform_bytes(&bytes).into()
    })
    .take(num_vars)
    .collect();

    for scalar in point.iter() {
      println!("scalar: {:?}", scalar);
    }
    let (_quotients, remainder) = quotients(&poly, &point);
    assert_eq!(
      poly.evaluate(&point),
      remainder,
      "point: {:?}, \n eval: {:?}, remainder:{:?}",
      point,
      poly.evaluate(&point),
      remainder
    );
  }
}
