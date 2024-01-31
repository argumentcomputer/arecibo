use crate::provider::kzg_commitment::KZGCommitmentEngine;
use crate::provider::non_hiding_kzg::{KZGProverKey, KZGVerifierKey, UVKZGPoly, UniversalKZGParam};
use crate::provider::pedersen::Commitment;
use crate::provider::traits::DlogGroup;
use crate::provider::util::iterators::DoubleEndedIteratorExt;
use crate::spartan::polys::univariate::UniPoly;
use crate::traits::commitment::Len;
use crate::traits::evaluation::EvaluationEngineTrait;
use crate::traits::{Engine as NovaEngine, Group, TranscriptEngineTrait, TranscriptReprTrait};
use crate::{CommitmentEngineTrait, NovaError};
use ff::{Field, PrimeFieldBits};
use group::prime::PrimeCurveAffine;
use group::{Curve, Group as group_Group};
use halo2curves::bn256::G1;
use pairing::{Engine, MultiMillerLoop};
use rayon::iter::IndexedParallelIterator;
use rayon::iter::{IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::marker::PhantomData;

use crate::provider::hyperkzg::EvaluationEngine as HyperKZG;
use ref_cast::RefCast as _;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(
  serialize = "E::G1Affine: Serialize, E::Fr: Serialize",
  deserialize = "E::G1Affine: Deserialize<'de>, E::Fr: Deserialize<'de>"
))]
pub struct EvaluationArgument<E: Engine> {
  comms: Vec<E::G1Affine>,
  evals: Vec<Vec<E::Fr>>,
  R_x: Vec<E::Fr>,
  C_P: E::G1Affine,
  C_Q: E::G1Affine,
  C_H: E::G1Affine,
}

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
  fn compute_a(c: &[E::G1Affine], transcript: &mut impl TranscriptEngineTrait<NE>) -> E::Fr {
    transcript.absorb(b"C_P_C_Q", &c.to_vec().as_slice());
    transcript.squeeze(b"a").unwrap()
  }

  fn compute_pi_polynomials(hat_P: &[E::Fr], point: &[E::Fr], eval: &E::Fr) -> Vec<Vec<E::Fr>> {
    let mut polys: Vec<Vec<E::Fr>> = Vec::new();
    polys.push(hat_P.to_vec());

    for i in 0..point.len() - 1 {
      let Pi_len = polys[i].len() / 2;
      let mut Pi = vec![E::Fr::ZERO; Pi_len];

      #[allow(clippy::needless_range_loop)]
      Pi.par_iter_mut().enumerate().for_each(|(j, Pi_j)| {
        *Pi_j =
          point[point.len() - i - 1] * (polys[i][2 * j + 1] - polys[i][2 * j]) + polys[i][2 * j];
      });

      polys.push(Pi);
    }
    // TODO: Ask Adrian, whether we can skip adding eval to polys as we did in HyperKZG
    polys.push(vec![*eval]);

    assert_eq!(polys.len(), 1 + (hat_P.len() as f32).log2().ceil() as usize);

    polys
  }

  fn compute_commitments(
    ck: &UniversalKZGParam<E>,
    C: &Commitment<NE>,
    polys: &[Vec<E::Fr>],
  ) -> Vec<E::G1Affine> {
    let mut comms: Vec<E::G1Affine> = (1..polys.len())
      .into_par_iter()
      .map(|i| {
        <NE::CE as CommitmentEngineTrait<NE>>::commit(ck, &polys[i])
          .comm
          .to_affine()
      })
      .collect();
    comms.insert(0, C.comm.to_affine());
    comms
  }

  fn compute_evals(polys: &[Vec<E::Fr>], u: &[E::Fr]) -> Vec<Vec<E::Fr>> {
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
    tmp = UVKZGPoly::new(
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

  fn setup(ck: &UniversalKZGParam<E>) -> (KZGProverKey<E>, KZGVerifierKey<E>) {
    ck.trim(ck.length() - 1)
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
    let comms = Self::compute_commitments(&ck, C, &polys);

    // Phase 2 (similar to hyperkzg)
    let r = HyperKZG::<E, NE>::compute_challenge(&comms, transcript);
    let u = vec![r, -r, r * r];

    let evals = Self::compute_evals(&polys, &u);

    // Phase 3
    // Compute B(x) = f_0(x) + q * f_1(x) + ... + q^(k-1) * f_{k-1}(x)
    let q = HyperKZG::<E, NE>::get_batch_challenge(&evals, transcript);
    let q_powers = HyperKZG::<E, NE>::batch_challenge_powers(q, polys.len());
    let batched_Pi: UniPoly<E::Fr> = polys.into_iter().map(UniPoly::new).rlc(&q);

    let C_P = q_powers
      .iter()
      .zip(comms.iter())
      .fold(E::G1::identity(), |acc, (q_i, C_i)| acc + *C_i * q_i);

    // Q(x), R(x) = P(x) / D(x), where D(x) = (x - r) * (x + r) * (x - r^2) = 1 * x^3 - r^2 * x^2 - r^2 * x + r^4
    let D = UVKZGPoly::new(vec![u[2] * u[2], -u[2], -u[2], E::Fr::from(1)]);
    let (Q_x, R_x) = batched_Pi.divide_with_q_and_r(&D).unwrap();

    let C_Q = <NE::CE as CommitmentEngineTrait<NE>>::commit(ck, &Q_x.coeffs)
      .comm
      .to_affine();

    let a = Self::compute_a(&vec![C_P.to_affine(), C_Q], transcript);

    // K(x) = P(x) - Q(x) * D(a) - R(a), R(a) should be subtracted from a free term of polynomial
    let K_x = Self::compute_k_polynomial(&batched_Pi, &Q_x, &D, &R_x, a);

    // TODO: since this is a usual KZG10 we should use it as utility instead
    // H(x) = K(x) / (x - a)
    let divisor = UVKZGPoly::new(vec![-a, E::Fr::from(1)]);
    let (H_x, _) = K_x.divide_with_q_and_r(&divisor).unwrap();

    let C_H = <NE::CE as CommitmentEngineTrait<NE>>::commit(ck, &H_x.coeffs)
      .comm
      .to_affine();

    Ok(EvaluationArgument::<E> {
      comms,
      evals,
      R_x: R_x.coeffs,
      C_P: C_P.into(),
      C_Q,
      C_H,
    })
  }

  /// A method to verify purported evaluations of a batch of polynomials
  fn verify(
    vk: &KZGVerifierKey<E>,
    transcript: &mut <NE as NovaEngine>::TE,
    _C: &Commitment<NE>,
    _point: &[E::Fr],
    _P_of_x: &E::Fr,
    pi: &EvaluationArgument<E>,
  ) -> Result<(), NovaError> {
    let r = HyperKZG::<E, NE>::compute_challenge(&pi.comms, transcript);

    // TODO: verifier needs to check that evals are valid. Ask Adrian for additional clarification
    let _q = HyperKZG::<E, NE>::get_batch_challenge(&pi.evals, transcript);

    let r_squared = r * r;

    // C_H, C_P, C_Q, R_x come from prover
    let C_P = pi.C_P;
    let C_Q = pi.C_Q;
    let C_H = pi.C_H;
    let R_x = UVKZGPoly::new(pi.R_x.clone());

    // D = (x - r) * (x + r) * (x - r^2) = 1 * x^3 - r^2 * x^2 - r^2 * x + r^4
    let D = UVKZGPoly::new(vec![
      r_squared * r_squared,
      -r_squared,
      -r_squared,
      E::Fr::from(1),
    ]);

    let a = Self::compute_a(&vec![C_P, C_Q], transcript);

    let C_K = C_P.to_curve() - (C_Q * D.evaluate(&a) + vk.g * R_x.evaluate(&a));

    // TODO switch to multi-miller-loop
    let left = E::pairing(&C_H, &(vk.beta_h.to_curve() - vk.h * a).to_affine());
    let right = E::pairing(&C_K.to_affine(), &vk.h);
    assert_eq!(left, right);
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::traits::TranscriptEngineTrait;
  use crate::{provider::keccak::Keccak256Transcript, CommitmentEngineTrait, CommitmentKey};

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
    let comms = EvaluationEngine::<E, NE>::compute_commitments(&ck, &C, &polys);

    let q = Fr::from(8165763);
    let q_powers = HyperKZG::<E, NE>::batch_challenge_powers(q, polys.len());
    let batched_Pi: UniPoly<Fr> = polys.clone().into_iter().map(UniPoly::new).rlc(&q);

    let r = Fr::from(1354678);
    let r_squared = r * r;

    let divident = batched_Pi.clone();
    let D = UVKZGPoly::new(vec![
      r_squared * r_squared,
      -r_squared,
      -r_squared,
      Fr::from(1),
    ]);
    let (Q_x, R_x) = divident.divide_with_q_and_r(&D).unwrap();

    let a = Fr::from(938576);

    let K_x = EvaluationEngine::<E, NE>::compute_k_polynomial(&batched_Pi, &Q_x, &D, &R_x, a);

    let mut C_P = G1::identity();
    q_powers.iter().zip(comms.iter()).for_each(|(q_i, C_i)| {
      C_P = C_P + (*C_i * q_i);
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
    let D = UVKZGPoly::new(vec![
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
    let D = UVKZGPoly::new(vec![
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
    let minus_R_x = UVKZGPoly::new(
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
    let u = vec![Fr::from(10), Fr::from(20), Fr::from(50)];

    let batched_Pi: UniPoly<Fr> = polys.clone().into_iter().map(UniPoly::new).rlc(&q);

    let q_powers = HyperKZG::<E, NE>::batch_challenge_powers(q, polys.len());
    for evaluation_scalar in u.iter() {
      let evals = polys
        .clone()
        .into_iter()
        .map(|poly| UniPoly::new(poly).evaluate(&evaluation_scalar))
        .collect::<Vec<Fr>>();

      let expected = evals
        .iter()
        .zip(q_powers.iter())
        .map(|(eval, q)| eval * q)
        .collect::<Vec<Fr>>()
        .into_iter()
        .sum::<Fr>();

      let actual = batched_Pi.evaluate(evaluation_scalar);
      assert_eq!(expected, actual);
    }
  }

  #[test]
  fn unit_tests() {
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
    let eval = Fr::from(56);

    let ck: CommitmentKey<NE> =
      <KZGCommitmentEngine<E> as CommitmentEngineTrait<NE>>::setup(b"test", n);
    let (pk, vk): (KZGProverKey<E>, KZGVerifierKey<E>) = EvaluationEngine::<E, NE>::setup(&ck);

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
}
