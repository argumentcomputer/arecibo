//! Shplonk PCS
use crate::provider::kzg_commitment::KZGCommitmentEngine;
use crate::provider::kzg_commitment::{KZGProverKey, KZGVerifierKey, UniversalKZGParam};
use crate::provider::pedersen::Commitment;
use crate::provider::traits::DlogGroup;
use crate::provider::util::iterators::DoubleEndedIteratorExt;
use crate::spartan::polys::univariate::UniPoly;
use crate::traits::commitment::Len;
use crate::traits::evaluation::EvaluationEngineTrait;
use crate::traits::{Engine as NovaEngine, Group, TranscriptEngineTrait, TranscriptReprTrait};
use crate::{CommitmentEngineTrait, NovaError};
use ff::{Field, PrimeFieldBits};
use group::{Curve, Group as group_Group};
use pairing::{Engine, MillerLoopResult, MultiMillerLoop};
use rayon::iter::{
  IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::marker::PhantomData;

use crate::provider::hyperkzg::EvaluationEngine as HyperKZG;
use group::prime::PrimeCurveAffine;
use itertools::Itertools;
use ref_cast::RefCast as _;
use std::sync::Arc;

/// EvaluationArgument of Shplonk
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(
  serialize = "E::G1Affine: Serialize, E::Fr: Serialize",
  deserialize = "E::G1Affine: Deserialize<'de>, E::Fr: Deserialize<'de>"
))]
pub struct EvaluationArgument<E: Engine> {
  comms: Vec<E::G1Affine>,
  evals: Vec<Vec<E::Fr>>,
  R_x: Vec<E::Fr>,
  C_Q: E::G1Affine,
  C_H: E::G1Affine,
}

/// EvaluationEngine of Shplonk
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EvaluationEngine<E, NE> {
  _p: PhantomData<(E, NE)>,
}

impl<E, NE> EvaluationEngine<E, NE>
where
  E: Engine,
  NE: NovaEngine<GE = E::G1, Scalar = E::Fr, CE = KZGCommitmentEngine<E>>,
  E::Fr: Serialize + DeserializeOwned,
  E::G1Affine: Serialize + DeserializeOwned,
  E::G2Affine: Serialize + DeserializeOwned,
  E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
  E::Fr: PrimeFieldBits,
  <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>,
  E::Fr: TranscriptReprTrait<E::G1>,
  E::G1Affine: TranscriptReprTrait<E::G1>,
{
  fn compute_a(c_q: &E::G1Affine, transcript: &mut impl TranscriptEngineTrait<NE>) -> E::Fr {
    transcript.absorb(b"C_Q", c_q);
    transcript.squeeze(b"a").unwrap()
  }

  fn compute_pi_polynomials(hat_P: &[E::Fr], point: &[E::Fr], eval: &E::Fr) -> Vec<Vec<E::Fr>> {
    let mut polys: Vec<Vec<E::Fr>> = Vec::new();
    polys.push(hat_P.to_vec());

    for i in 0..point.len() - 1 {
      let Pi_len = polys[i].len() / 2;
      let mut Pi = vec![E::Fr::ZERO; Pi_len];

      (0..Pi_len)
        .into_par_iter()
        .map(|j| {
          point[point.len() - i - 1] * (polys[i][2 * j + 1] - polys[i][2 * j]) + polys[i][2 * j]
        })
        .collect_into_vec(&mut Pi);

      polys.push(Pi);
    }

    // TODO avoid including last constant polynomial, known to verifier
    polys.push(vec![*eval]);

    assert_eq!(polys.len(), 1 + (hat_P.len() as f32).log2().ceil() as usize);

    polys
  }

  fn compute_commitments(
    ck: &UniversalKZGParam<E>,
    C: &Commitment<NE>,
    polys: &[Vec<E::Fr>],
  ) -> Vec<E::G1Affine> {
    // TODO avoid computing commitment to constant polynomial
    let mut comms: Vec<NE::GE> = (1..polys.len())
      .into_par_iter()
      .map(|i| <NE::CE as CommitmentEngineTrait<NE>>::commit(ck, &polys[i]).comm)
      .collect();
    // TODO avoid inserting commitment known to verifier
    comms.insert(0, C.comm);

    let mut comms_affine: Vec<E::G1Affine> = vec![E::G1Affine::identity(); comms.len()];
    NE::GE::batch_normalize(&comms, &mut comms_affine);
    comms_affine
  }

  fn compute_evals(polys: &[Vec<E::Fr>], u: &[E::Fr]) -> Vec<Vec<E::Fr>> {
    // TODO: avoid computing eval to a constant polynomial
    let mut v = vec![vec!(E::Fr::ZERO; polys.len()); u.len()];
    v.par_iter_mut().enumerate().for_each(|(i, v_i)| {
      // for each point u
      v_i.par_iter_mut().zip_eq(polys).for_each(|(v_ij, f)| {
        // for each poly f (except the last one - since it is constant)
        *v_ij = UniPoly::ref_cast(f).evaluate(&u[i]);
      });
    });
    v
  }

  fn compute_k_polynomial(
    batched_Pi: &UniPoly<E::Fr>,
    Q_x: &UniPoly<E::Fr>,
    D: &UniPoly<E::Fr>,
    R_x: &UniPoly<E::Fr>,
    a: E::Fr,
  ) -> UniPoly<E::Fr> {
    let mut tmp = Q_x.clone();
    tmp *= &D.evaluate(&a);
    tmp[0] += &R_x.evaluate(&a);
    tmp = UniPoly::new(
      tmp
        .coeffs
        .into_iter()
        .map(|coeff| -coeff)
        .collect::<Vec<E::Fr>>(),
    );
    let mut K_x = batched_Pi.clone();
    K_x += &tmp;
    K_x
  }
}

impl<E, NE> EvaluationEngineTrait<NE> for EvaluationEngine<E, NE>
where
  E: MultiMillerLoop,
  NE: NovaEngine<GE = E::G1, Scalar = E::Fr, CE = KZGCommitmentEngine<E>>,
  E::Fr: Serialize + DeserializeOwned,
  E::G1Affine: Serialize + DeserializeOwned,
  E::G2Affine: Serialize + DeserializeOwned,
  E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
  <E::G1 as Group>::Base: TranscriptReprTrait<E::G1>, // Note: due to the move of the bound TranscriptReprTrait<G> on G::Base from Group to Engine
  E::Fr: PrimeFieldBits, // TODO due to use of gen_srs_for_testing, make optional
  E::Fr: TranscriptReprTrait<E::G1>,
  E::G1Affine: TranscriptReprTrait<E::G1>,
{
  type ProverKey = KZGProverKey<E>;
  type VerifierKey = KZGVerifierKey<E>;
  type EvaluationArgument = EvaluationArgument<E>;

  fn setup(ck: Arc<UniversalKZGParam<E>>) -> (KZGProverKey<E>, KZGVerifierKey<E>) {
    let len = ck.length() - 1;
    UniversalKZGParam::trim(ck, len)
  }

  fn prove(
    ck: &UniversalKZGParam<E>,
    _pk: &KZGProverKey<E>,
    transcript: &mut <NE as NovaEngine>::TE,
    C: &Commitment<NE>,
    hat_P: &[E::Fr],
    point: &[E::Fr],
    eval: &E::Fr,
  ) -> Result<EvaluationArgument<E>, NovaError> {
    let x: Vec<E::Fr> = point.to_vec();
    let ell = x.len();
    let n = hat_P.len();
    assert_eq!(n, 1 << ell);

    // Phase 1 (similar to hyperkzg)
    let polys = Self::compute_pi_polynomials(hat_P, point, eval);
    let comms = Self::compute_commitments(ck, C, &polys);

    // Phase 2 (similar to hyperkzg)
    let r = HyperKZG::<E, NE>::compute_challenge(&comms, transcript);
    let u = vec![r, -r, r * r];

    let evals = Self::compute_evals(&polys, &u);

    // Phase 3
    // Compute B(x) = f_0(x) + q * f_1(x) + ... + q^(k-1) * f_{k-1}(x)
    let q = HyperKZG::<E, NE>::get_batch_challenge(&evals, transcript);
    let batched_Pi: UniPoly<E::Fr> = polys.into_iter().map(UniPoly::new).rlc(&q);

    // Q(x), R(x) = P(x) / D(x), where D(x) = (x - r) * (x + r) * (x - r^2) = 1 * x^3 - r^2 * x^2 - r^2 * x + r^4
    let D = UniPoly::new(vec![u[2] * u[2], -u[2], -u[2], E::Fr::from(1)]);
    let (Q_x, R_x) = batched_Pi.divide_with_q_and_r(&D).unwrap();

    let C_Q = <NE::CE as CommitmentEngineTrait<NE>>::commit(ck, &Q_x.coeffs)
      .comm
      .to_affine();

    let a = Self::compute_a(&C_Q, transcript);

    // K(x) = P(x) - Q(x) * D(a) - R(a), note that R(a) should be subtracted from a free term of polynomial
    let K_x = Self::compute_k_polynomial(&batched_Pi, &Q_x, &D, &R_x, a);

    // TODO: since this is a usual KZG10 we should use it as utility instead
    // H(x) = K(x) / (x - a)
    let divisor = UniPoly::new(vec![-a, E::Fr::from(1)]);
    let (H_x, _) = K_x.divide_with_q_and_r(&divisor).unwrap();

    let C_H = <NE::CE as CommitmentEngineTrait<NE>>::commit(ck, &H_x.coeffs)
      .comm
      .to_affine();

    Ok(EvaluationArgument::<E> {
      comms,
      evals,
      R_x: R_x.coeffs,
      C_Q,
      C_H,
    })
  }

  /// A method to verify purported evaluations of a batch of polynomials
  fn verify(
    vk: &KZGVerifierKey<E>,
    transcript: &mut <NE as NovaEngine>::TE,
    _C: &Commitment<NE>,
    point: &[E::Fr],
    _P_of_x: &E::Fr,
    pi: &EvaluationArgument<E>,
  ) -> Result<(), NovaError> {
    let r = HyperKZG::<E, NE>::compute_challenge(&pi.comms, transcript);
    let u = [r, -r, r * r];

    if pi.evals.len() != u.len() {
      return Err(NovaError::ProofVerifyError);
    }
    if pi.R_x.len() != u.len() {
      return Err(NovaError::ProofVerifyError);
    }

    // TODO:
    // insert _P_of_x into every pi.evals_i[last]
    // insert _C into pi.comms[0]
    // compute commitment for eval and insert it into pi.comms[last]

    let q = HyperKZG::<E, NE>::get_batch_challenge(&pi.evals, transcript);
    //let q_powers = HyperKZG::<E, NE>::batch_challenge_powers(q, pi.comms.len());

    let R_x = UniPoly::new(pi.R_x.clone());

    let mut evals_at_r = vec![];
    let mut evals_at_minus_r = vec![];
    let mut evals_at_r_squared = vec![];
    for (i, evals_i) in pi.evals.iter().enumerate() {
      if i == 0 {
        evals_at_r = evals_i.clone();
      }
      if i == 1 {
        evals_at_minus_r = evals_i.clone();
      }
      if i == 2 {
        evals_at_r_squared = evals_i.clone();
      }

      let batched_eval = UniPoly::ref_cast(evals_i).evaluate(&q);

      // here we check correlation between R polynomial and batched evals, e.g.:
      // 1) R(r) == eval at r
      // 2) R(-r) == eval at -r
      // 3) R(r^2) == eval at r^2
      if batched_eval != R_x.evaluate(&u[i]) {
        return Err(NovaError::ProofVerifyError);
      }
    }

    // here we check that Pi polynomials were correctly constructed by the prover, using 'r' as a random point, e.g:
    // P_i_even = P_i(r) + P_i(-r) * 1/2
    // P_i_odd = P_i(r) - P_i(-r) * 1/2*r
    // P_i+1(r^2) == (1 - point_i) * P_i_even + point_i * P_i_odd -> should hold, according to Gemini transformation
    let mut point = point.to_vec();
    point.reverse();
    #[allow(clippy::disallowed_methods)]
    for (index, ((eval_r, eval_minus_r), eval_r_squared)) in evals_at_r
      .iter()
      .zip_eq(evals_at_minus_r.iter())
      // TODO: Ask Adrian if we need evals_at_r_squared[0] for some additional checks
      .zip(evals_at_r_squared[1..].iter())
      .enumerate()
    {
      let even = (*eval_r + eval_minus_r) * (E::Fr::from(2).invert().unwrap());
      let odd = (*eval_r - eval_minus_r) * ((E::Fr::from(2) * r).invert().unwrap());

      if *eval_r_squared != ((E::Fr::ONE - point[index]) * even) + (point[index] * odd) {
        return Err(NovaError::ProofVerifyError);
      }
    }

    let C_P: E::G1 = pi.comms.iter().map(|comm| comm.to_curve()).rlc(&q);
    let C_Q = pi.C_Q;
    let C_H = pi.C_H;
    let r_squared = u[2];

    // D = (x - r) * (x + r) * (x - r^2) = 1 * x^3 - r^2 * x^2 - r^2 * x + r^4
    let D = UniPoly::new(vec![
      r_squared * r_squared,
      -r_squared,
      -r_squared,
      E::Fr::from(1),
    ]);

    let a = Self::compute_a(&C_Q, transcript);

    let C_K = C_P - (C_Q * D.evaluate(&a) + vk.g * R_x.evaluate(&a));

    let pairing_inputs: Vec<(E::G1Affine, E::G2Prepared)> = vec![
      (C_H, vk.beta_h.into()),
      ((C_H * (-a) - C_K).to_affine(), vk.h.into()),
    ];

    #[allow(clippy::map_identity)]
    let pairing_input_refs = pairing_inputs
      .iter()
      .map(|(a, b)| (a, b))
      .collect::<Vec<_>>();

    let pairing_result = E::multi_miller_loop(pairing_input_refs.as_slice()).final_exponentiation();
    if pairing_result.is_identity().unwrap_u8() == 0x00 {
      return Err(NovaError::ProofVerifyError);
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::traits::TranscriptEngineTrait;
  use crate::{provider::keccak::Keccak256Transcript, CommitmentEngineTrait, CommitmentKey};
  use halo2curves::bn256::G1;
  use itertools::Itertools;

  type E = halo2curves::bn256::Bn256;
  type NE = crate::provider::Bn256EngineKZG;
  type Fr = <NE as NovaEngine>::Scalar;

  fn test_commitment_to_k_polynomial_correctness(
    ck: &CommitmentKey<NE>,
    C: &Commitment<NE>,
    poly: &[Fr],
    point: &[Fr],
    eval: &Fr,
  ) {
    let polys = EvaluationEngine::<E, NE>::compute_pi_polynomials(poly, point, eval);
    let comms = EvaluationEngine::<E, NE>::compute_commitments(ck, C, &polys);

    let q = Fr::from(8165763);
    let q_powers = HyperKZG::<E, NE>::batch_challenge_powers(q, polys.len());
    let batched_Pi: UniPoly<Fr> = polys.clone().into_iter().map(UniPoly::new).rlc(&q);

    let r = Fr::from(1354678);
    let r_squared = r * r;

    let divident = batched_Pi.clone();
    let D = UniPoly::new(vec![
      r_squared * r_squared,
      -r_squared,
      -r_squared,
      Fr::from(1),
    ]);
    let (Q_x, R_x) = divident.divide_with_q_and_r(&D).unwrap();

    let a = Fr::from(938576);

    let K_x = EvaluationEngine::<E, NE>::compute_k_polynomial(&batched_Pi, &Q_x, &D, &R_x, a);

    let mut C_P = G1::identity();
    q_powers.iter().zip_eq(comms.iter()).for_each(|(q_i, C_i)| {
      C_P += *C_i * q_i;
    });

    let C_Q =
      <<crate::provider::Bn256EngineKZG as NovaEngine>::CE as CommitmentEngineTrait<NE>>::commit(
        ck,
        &Q_x.coeffs,
      )
      .comm
      .to_affine();

    // Check that Cp - Cq * D(a) - g1 * R(a) == MSM(ck, K(x))
    let C_K = C_P - C_Q * D.evaluate(&a) - ck.powers_of_g[0] * R_x.evaluate(&a);

    let C_K_expected =
      <<crate::provider::Bn256EngineKZG as NovaEngine>::CE as CommitmentEngineTrait<NE>>::commit(
        ck,
        &K_x.coeffs,
      )
      .comm
      .to_affine();

    assert_eq!(C_K_expected, C_K.to_affine());
  }

  fn test_k_polynomial_correctness(poly: &[Fr], point: &[Fr], eval: &Fr) {
    let polys = EvaluationEngine::<E, NE>::compute_pi_polynomials(poly, point, eval);
    let q = Fr::from(8165763);
    let batched_Pi: UniPoly<Fr> = polys.clone().into_iter().map(UniPoly::new).rlc(&q);

    let r = Fr::from(56263);
    let r_squared = r * r;

    let divident = batched_Pi.clone();
    let D = UniPoly::new(vec![
      r_squared * r_squared,
      -r_squared,
      -r_squared,
      Fr::from(1),
    ]);
    let (Q_x, R_x) = divident.divide_with_q_and_r(&D).unwrap();

    let a = Fr::from(190837645);

    let K_x = EvaluationEngine::<E, NE>::compute_k_polynomial(&batched_Pi, &Q_x, &D, &R_x, a);

    assert_eq!(Fr::from(0), K_x.evaluate(&a));
  }

  fn test_d_polynomial_correctness(poly: &[Fr], point: &[Fr], eval: &Fr) {
    let polys = EvaluationEngine::<E, NE>::compute_pi_polynomials(poly, point, eval);
    let q = Fr::from(8165763);
    let batched_Pi: UniPoly<Fr> = polys.clone().into_iter().map(UniPoly::new).rlc(&q);

    let r = Fr::from(2895776832);
    let r_squared = r * r;

    let divident = batched_Pi.clone();
    // D(x) = (x - r) * (x + r) * (x - r^2)
    let D = UniPoly::new(vec![
      r_squared * r_squared,
      -r_squared,
      -r_squared,
      Fr::from(1),
    ]);
    let (Q_x, R_x) = divident.divide_with_q_and_r(&D).unwrap();

    let evaluation_scalar = Fr::from(182746);
    assert_eq!(
      batched_Pi.evaluate(&evaluation_scalar),
      D.evaluate(&evaluation_scalar) * Q_x.evaluate(&evaluation_scalar)
        + R_x.evaluate(&evaluation_scalar)
    );

    // Check that Q(x) = (P(x) - R(x)) / D(x)
    let mut P_x = batched_Pi.clone();
    let minus_R_x = UniPoly::new(
      R_x
        .clone()
        .coeffs
        .into_iter()
        .map(|coeff| -coeff)
        .collect::<Vec<Fr>>(),
    );
    P_x += &minus_R_x;

    let divident = P_x.clone();
    let (Q_x_recomputed, _) = divident.divide_with_q_and_r(&D).unwrap();

    assert_eq!(Q_x, Q_x_recomputed);
  }

  fn test_batching_property_on_evaluation(poly: &[Fr], point: &[Fr], eval: &Fr) {
    let polys = EvaluationEngine::<E, NE>::compute_pi_polynomials(poly, point, eval);

    let q = Fr::from(97652);
    let u = [Fr::from(10), Fr::from(20), Fr::from(50)];

    let batched_Pi: UniPoly<Fr> = polys.clone().into_iter().map(UniPoly::new).rlc(&q);

    let q_powers = HyperKZG::<E, NE>::batch_challenge_powers(q, polys.len());
    for evaluation_scalar in u.iter() {
      let evals = polys
        .clone()
        .into_iter()
        .map(|poly| UniPoly::new(poly).evaluate(evaluation_scalar))
        .collect::<Vec<Fr>>();

      let expected = evals
        .iter()
        .zip_eq(q_powers.iter())
        .map(|(eval, q)| eval * q)
        .collect::<Vec<Fr>>()
        .into_iter()
        .sum::<Fr>();

      let actual = batched_Pi.evaluate(evaluation_scalar);
      assert_eq!(expected, actual);
    }
  }

  #[test]
  fn test_shplonk_unit_tests() {
    // poly = [1, 2, 1, 4, 1, 2, 1, 4]
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

    // point = [4,3,8]
    let point = vec![Fr::from(4), Fr::from(3), Fr::from(8)];

    // eval = 57
    let eval = Fr::from(57);

    let ck: CommitmentKey<NE> =
      <KZGCommitmentEngine<E> as CommitmentEngineTrait<NE>>::setup(b"test", poly.len());

    let ck = Arc::new(ck);
    let C: Commitment<NE> = KZGCommitmentEngine::commit(&ck, &poly);

    test_batching_property_on_evaluation(&poly, &point, &eval);
    test_d_polynomial_correctness(&poly, &point, &eval);
    test_k_polynomial_correctness(&poly, &point, &eval);
    test_commitment_to_k_polynomial_correctness(&ck, &C, &poly, &point, &eval);
  }

  #[test]
  fn test_shplonk_pcs() {
    let n = 8;

    // poly = [1, 2, 1, 4, 1, 2, 1, 4]
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

    // point = [4,3,8]
    let point = vec![Fr::from(4), Fr::from(3), Fr::from(8)];

    // eval = 57
    let eval = Fr::from(57);

    let ck: CommitmentKey<NE> =
      <KZGCommitmentEngine<E> as CommitmentEngineTrait<NE>>::setup(b"test", n);
    let ck = Arc::new(ck);
    let (pk, vk): (KZGProverKey<E>, KZGVerifierKey<E>) =
      EvaluationEngine::<E, NE>::setup(ck.clone());

    // make a commitment
    let C: Commitment<NE> = KZGCommitmentEngine::commit(&ck, &poly);

    let mut prover_transcript = Keccak256Transcript::new(b"TestEval");
    let proof =
      EvaluationEngine::<E, NE>::prove(&ck, &pk, &mut prover_transcript, &C, &poly, &point, &eval)
        .unwrap();

    let mut verifier_transcript = Keccak256Transcript::<NE>::new(b"TestEval");
    assert!(EvaluationEngine::<E, NE>::verify(
      &vk,
      &mut verifier_transcript,
      &C,
      &point,
      &eval,
      &proof
    )
    .is_ok());
  }

  #[test]
  fn test_shplonk_pcs_negative() {
    let n = 8;
    // poly = [1, 2, 1, 4, 1, 2, 1, 4]
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
    // point = [4,3,8]
    let point = vec![Fr::from(4), Fr::from(3), Fr::from(8)];
    // eval = 57
    let eval = Fr::from(57);

    // eval = 57
    let eval1 = Fr::from(56); // wrong eval
    test_negative_inner(n, &poly, &point, &eval1);

    // point = [4,3,8]
    let point1 = vec![Fr::from(4), Fr::from(3), Fr::from(7)]; // wrong point
    test_negative_inner(n, &poly, &point1, &eval);

    // poly = [1, 2, 1, 4, 1, 2, 1, 4]
    let poly1 = vec![
      Fr::ONE,
      Fr::from(2),
      Fr::from(1),
      Fr::from(4),
      Fr::ONE,
      Fr::from(2),
      Fr::from(200),
      Fr::from(100),
    ]; // wrong poly
    test_negative_inner(n, &poly1, &point, &eval);
  }

  fn test_negative_inner(n: usize, poly: &[Fr], point: &[Fr], eval: &Fr) {
    let ck: CommitmentKey<NE> =
      <KZGCommitmentEngine<E> as CommitmentEngineTrait<NE>>::setup(b"test", n);
    let ck = Arc::new(ck);
    let (pk, vk): (KZGProverKey<E>, KZGVerifierKey<E>) =
      EvaluationEngine::<E, NE>::setup(ck.clone());

    // make a commitment
    let C: Commitment<NE> = KZGCommitmentEngine::commit(&ck, poly);

    let mut prover_transcript = Keccak256Transcript::new(b"TestEval");
    let mut verifier_transcript = Keccak256Transcript::<NE>::new(b"TestEval");

    let proof =
      EvaluationEngine::<E, NE>::prove(&ck, &pk, &mut prover_transcript, &C, poly, point, eval)
        .unwrap();

    assert!(EvaluationEngine::<E, NE>::verify(
      &vk,
      &mut verifier_transcript,
      &C,
      point,
      eval,
      &proof
    )
    .is_err());
  }
}
