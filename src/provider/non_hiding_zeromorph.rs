//! Non-hiding Zeromorph scheme for Multilinear Polynomials.
//!
//!

use ff::{BatchInvert, Field};
use group::{Curve, Group as _};
use itertools::Itertools as _;
use pairing::{Engine, MillerLoopResult, MultiMillerLoop};
use rayon::prelude::{
  IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
};
use std::{borrow::Borrow, iter, marker::PhantomData};

use crate::{
  errors::NovaError,
  spartan::polys::multilinear::MultilinearPolynomial,
  traits::{Engine as NovaEngine, TranscriptEngineTrait},
};

use super::{
  non_hiding_kzg::{
    UVKZGCommitment, UVKZGEvaluation, UVKZGPoly, UVKZGProof, UVKZGProverKey, UVKZGVerifierKey,
    UVUniversalKZGParam, UVKZGPCS,
  },
  traits::DlogGroup,
};

/// `ZMProverKey` is used to generate a proof
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZMProverKey<E: Engine> {
  commit_pp: UVKZGProverKey<E>,
  open_pp: UVKZGProverKey<E>,
}

/// `ZMVerifierKey` is used to check evaluation proofs for a given
/// commitment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZMVerifierKey<E: Engine> {
  vp: UVKZGVerifierKey<E>,
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
#[derive(Debug, Clone, Eq, PartialEq, Default)]
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

#[derive(Debug, Clone, Eq, PartialEq, Default)]

/// Proofs
pub struct ZMProof<E: Engine> {
  /// proof
  pub proof: E::G1Affine,
}

impl<E: Engine> From<UVKZGProof<E>> for ZMProof<E> {
  fn from(value: UVKZGProof<E>) -> Self {
    ZMProof { proof: value.proof }
  }
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
{
  /// Generate a commitment for a polynomial
  /// Note that the scheme is not hidding
  pub fn commit(
    pp: impl Borrow<ZMProverKey<E>>,
    poly: &MultilinearPolynomial<E::Fr>,
  ) -> Result<ZMCommitment<E>, NovaError> {
    let pp = pp.borrow();
    if pp.commit_pp.powers_of_g.len() < poly.Z.len() {
      return Err(NovaError::InvalidIPA); // TODO: better error
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
    poly: &MultilinearPolynomial<E::Fr>,
    comm: &ZMCommitment<E>,
    point: &[E::Fr],
    transcript: &mut impl TranscriptEngineTrait<NE>,
  ) -> Result<(ZMProof<E>, ZMEvaluation<E>), NovaError> {
    let num_vars = poly.get_num_vars();
    let pp = pp.borrow();
    if pp.commit_pp.powers_of_g.len() < poly.Z.len() {
      return Err(NovaError::InvalidIPA); // TODO: better error
    }

    debug_assert_eq!(Self::commit(pp, poly).unwrap().0, comm.0);
    let eval = poly.evaluate(point);

    let (quotients, _remainder) = poly.quotients(point);
    // TODO: see test_quo below
    // debug_assert_eq!(remainder, eval);

    // TODO: this should be a Cow
    let quotients_polys = quotients
      .iter()
      .map(|q| UVKZGPoly::new(q.clone()))
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
      let q_hat = powers_of_y.iter().zip(&quotients).enumerate().fold(
        vec![E::Fr::ZERO; 1 << num_vars],
        |mut q_hat, (idx, (power_of_y, q))| {
          let offset = q_hat.len() - (1 << idx);
          q_hat[offset..]
            .par_iter_mut()
            .zip(q)
            .for_each(|(q_hat, q)| {
              *q_hat = *q_hat + *power_of_y * *q;
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
    f[0] += eval_scalar * eval;
    quotients_polys
      .into_iter()
      .zip(q_scalars)
      .for_each(|(mut q, scalar)| {
        q *= &scalar;
        f += &q;
      });
    debug_assert_eq!(f.evaluate(&x), E::Fr::ZERO);

    UVKZGPCS::<E>::open(&pp.open_pp, &f, &x).map(|(proof, eval)| (proof.into(), eval.into()))
  }

  /// Verifies that `value` is the evaluation at `x` of the polynomial
  /// committed inside `comm`.
  pub fn verify(
    vk: &impl Borrow<ZMVerifierKey<E>>,
    comm: &ZMCommitment<E>,
    point: &[E::Fr],
    proof: ZMProof<E>,
    evaluation: ZMEvaluation<E>,
    transcript: &mut impl TranscriptEngineTrait<NE>,
  ) -> Result<bool, NovaError> {
    let vk = vk.borrow();
    let num_vars = point.len();

    let q_comms = E::G1::from_label(b"quo", num_vars);

    let y = transcript.squeeze(b"y")?;

    let q_hat_comm = E::G1::from_label(b"q_hat", 1);

    let x = transcript.squeeze(b"x")?;
    let z = transcript.squeeze(b"z")?;

    let (eval_scalar, q_scalars) = eval_and_quotient_scalars(y, x, z, point);
    let scalars = [vec![E::Fr::ONE, z, eval_scalar * evaluation.0], q_scalars].concat();
    let bases = [vec![q_hat_comm[0], comm.0, vk.vp.g], q_comms].concat();
    let c = <E::G1 as DlogGroup>::vartime_multiscalar_mul(&scalars, &bases).to_affine();

    let pi = proof.proof;

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

// TODO : move this somewhere else
// TODO: remove the transitory allocations
fn eval_and_quotient_scalars<F: Field>(y: F, x: F, z: F, u: &[F]) -> (F, Vec<F>) {
  let num_vars = u.len();

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
    .zip(u)
    .map(
      |(((((power_of_y, offset_of_x), square_of_x), v_i), v_j), u_i)| {
        -(power_of_y * offset_of_x + z * (square_of_x * v_j - *u_i * v_i))
      },
    )
    .collect::<Vec<_>>();

  (-vs[0] * z, q_scalars)
}

#[cfg(test)]
mod test {

  use std::iter;

  use ff::FromUniformBytes;
  use halo2curves::bn256::{Bn256, Fr as Scalar};
  use pairing::MultiMillerLoop;
  use rand::{thread_rng, Rng};
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;

  use crate::{
    provider::{
      Bn256Engine,
      keccak::Keccak256Transcript,
      non_hiding_kzg::UVUniversalKZGParam,
      non_hiding_zeromorph::{trim, ZMPCS},
      traits::DlogGroup,
    },
    spartan::polys::multilinear::MultilinearPolynomial,
    traits::{Engine as NovaEngine, TranscriptEngineTrait},
  };

  fn commit_open_verify_with<E: MultiMillerLoop, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>>()
  where
    E::G1: DlogGroup<PreprocessedGroupElement = E::G1Affine, Scalar = E::Fr>,
  {
    for num_vars in 3..16 {
      // Setup
      let (pp, vk) = {
        let mut rng = thread_rng();
        let poly_size = 1 << (num_vars + 1);
        let param = UVUniversalKZGParam::<E>::gen_srs_for_testing(&mut rng, poly_size);
        trim(&param, poly_size)
      };

      // Commit and open
      let mut transcript = Keccak256Transcript::<NE>::new(b"test");
      let poly = MultilinearPolynomial::<E::Fr>::random(num_vars, &mut thread_rng());
      let comm = ZMPCS::<E, NE>::commit(&pp, &poly).unwrap();
      let point = iter::from_fn(|| transcript.squeeze(b"pt").ok())
        .take(num_vars)
        .collect::<Vec<_>>();
      let eval_pre = poly.evaluate(point.as_slice());

      let (proof, eval) = ZMPCS::open(&pp, &poly, &comm, &point, &mut transcript).unwrap();
      assert_eq!(eval_pre, eval.0);

      // Verify

      let mut transcript = Keccak256Transcript::<NE>::new(b"test");
      let result = ZMPCS::verify(&vk, &comm, point.as_slice(), proof, eval, &mut transcript);

      assert_eq!(result, Ok(true));
    }
  }

  #[test]
  fn test_commit_open_verify() {
    commit_open_verify_with::<Bn256, Bn256Engine>();
  }

  #[ignore]
  #[test]
  fn test_quo() {
    let num_vars = 10;
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
    let poly = MultilinearPolynomial::random(num_vars, &mut rng);

    let point: Vec<_> = std::iter::from_fn(|| {
      let mut bytes = [0u8; 64];
      rng.fill(&mut bytes);
      Scalar::from_uniform_bytes(&bytes).into()
    })
    .take(num_vars)
    .collect();

    for scalar in point.iter() {
      println!("scalar: {:?}", scalar);
    }
    let (_quotients, remainder) = poly.quotients(&point);
    // TODO: the evaluation this is meant to compare to is that of the underlying univ. poly, see Lemma 2.3.1
    // whith is not what poly.evaluate(point) returns.
    // debug_assert_eq!(remainder, eval);
    assert_eq!(
      poly.evaluate(&point),
      remainder,
      "poly: {:?}, \n point: {:?}, \n eval: {:?}, remainder:{:?}",
      poly,
      point,
      poly.evaluate(&point),
      remainder
    );
  }
}
