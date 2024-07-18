//! This module implements `RelaxedR1CSSNARK` traits using a spark-based approach to prove evaluations of
//! sparse multilinear polynomials involved in Spartan's sum-check protocol, thereby providing a preprocessing SNARK
//! The verifier in this preprocessing SNARK maintains a commitment to R1CS matrices. This is beneficial when using a
//! polynomial commitment scheme in which the verifier's costs is succinct.
//! This code includes experimental optimizations to reduce runtimes and proof sizes.
use crate::{
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  r1cs::{R1CSShape, RelaxedR1CSInstance, ZKRelaxedR1CSWitness},
  spartan::{
    math::Math, nizk::ProductProof, polys::{
      eq::EqPolynomial,
      identity::IdentityPolynomial,
      multilinear::MultilinearPolynomial,
      power::PowPolynomial,
      univariate::UniPoly,
    }, powers, zksumcheck::{
      engine::{
        InnerSumcheckInstance, MemorySumcheckInstance, OuterSumcheckInstance, WitnessBoundSumcheck, ZKSumcheckEngine
      },
      ZKSumcheckProof,
    }, PolyEvalInstance, PolyEvalWitness
  },
  traits::{
    self, commitment::{CommitmentTrait, Len}, zkevaluation::EvaluationEngineTrait, zksnark::{DigestHelperTrait, RelaxedR1CSSNARKTrait}, Engine, TranscriptEngineTrait, TranscriptReprTrait
  },
  zip_with, Commitment, CommitmentKey, CompressedCommitment,
};
use crate::traits::commitment::ZKCommitmentEngineTrait;
use crate::provider::Bn256EngineZKPedersen;
use crate::spartan::zksnark::SumcheckGens;
use core::cmp::max;
use ff::Field;
use rand_core::OsRng;
use itertools::Itertools as _;
use once_cell::sync::OnceCell;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use super::polys::{masked_eq::MaskedEqPolynomial, multilinear::SparsePolynomial};

fn padded(v: &[<E as Engine>::Scalar], n: usize, e: &<E as Engine>::Scalar) -> Vec<<E as Engine>::Scalar> {
  let mut v_padded = vec![*e; n];
  v_padded[..v.len()].copy_from_slice(v);
  v_padded
}

/// A type that holds `R1CSShape` in a form amenable to memory checking
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct R1CSShapeSparkRepr {
  pub(in crate::spartan) N: usize, // size of the vectors

  // dense representation
  pub(in crate::spartan) row: Vec<<E as Engine>::Scalar>,
  pub(in crate::spartan) col: Vec<<E as Engine>::Scalar>,
  pub(in crate::spartan) val_A: Vec<<E as Engine>::Scalar>,
  pub(in crate::spartan) val_B: Vec<<E as Engine>::Scalar>,
  pub(in crate::spartan) val_C: Vec<<E as Engine>::Scalar>,

  // timestamp polynomials
  pub(in crate::spartan) ts_row: Vec<<E as Engine>::Scalar>,
  pub(in crate::spartan) ts_col: Vec<<E as Engine>::Scalar>,
}

/// A type that holds a commitment to a sparse polynomial
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ZKR1CSShapeSparkCommitment {
  pub(in crate::spartan) N: usize, // size of each vector

  // commitments to the dense representation
  pub(in crate::spartan) comm_row: Commitment<E>,
  pub(in crate::spartan) comm_col: Commitment<E>,
  pub(in crate::spartan) comm_val_A: Commitment<E>,
  pub(in crate::spartan) comm_val_B: Commitment<E>,
  pub(in crate::spartan) comm_val_C: Commitment<E>,

  // commitments to the timestamp polynomials
  pub(in crate::spartan) comm_ts_row: Commitment<E>,
  pub(in crate::spartan) comm_ts_col: Commitment<E>,


  // randomness for commitments to the dense representation
  pub(in crate::spartan) r_comm_row: <E as Engine>::Scalar,
  pub(in crate::spartan) r_comm_col: <E as Engine>::Scalar,
  pub(in crate::spartan) r_comm_val_A: <E as Engine>::Scalar,
  pub(in crate::spartan) r_comm_val_B: <E as Engine>::Scalar,
  pub(in crate::spartan) r_comm_val_C: <E as Engine>::Scalar,

  // randomness for commitments to the timestamp polynomials
  pub(in crate::spartan) r_comm_ts_row: <E as Engine>::Scalar,
  pub(in crate::spartan) r_comm_ts_col: <E as Engine>::Scalar,
}

impl TranscriptReprTrait<<E as Engine>::GE> for ZKR1CSShapeSparkCommitment {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    [
      self.comm_row,
      self.comm_col,
      self.comm_val_A,
      self.comm_val_B,
      self.comm_val_C,
      self.comm_ts_row,
      self.comm_ts_col,
    ]
    .as_slice()
    .to_transcript_bytes()
  }
}

impl R1CSShapeSparkRepr {
  /// represents `R1CSShape` in a Spark-friendly format amenable to memory checking
  pub fn new(S: &R1CSShape<E>) -> Self {
    let N = {
      let total_nz = S.A.len() + S.B.len() + S.C.len();
      max(total_nz, max(2 * S.num_vars, S.num_cons)).next_power_of_two()
    };

    // we make col lookup into the last entry of z, so we commit to zeros
    let (mut row, mut col, mut val_A, mut val_B, mut val_C) = (
      vec![0; N],
      vec![N - 1; N],
      vec![<E as Engine>::Scalar::ZERO; N],
      vec![<E as Engine>::Scalar::ZERO; N],
      vec![<E as Engine>::Scalar::ZERO; N],
    );

    for (i, entry) in S.A.iter().enumerate() {
      let (r, c, v) = entry;
      row[i] = r;
      col[i] = c;
      val_A[i] = v;
    }

    let b_offset = S.A.len();
    for (i, entry) in S.B.iter().enumerate() {
      let (r, c, v) = entry;
      row[b_offset + i] = r;
      col[b_offset + i] = c;
      val_B[b_offset + i] = v;
    }

    let c_offset = S.A.len() + S.B.len();
    for (i, entry) in S.C.iter().enumerate() {
      let (r, c, v) = entry;
      row[c_offset + i] = r;
      col[c_offset + i] = c;
      val_C[c_offset + i] = v;
    }

    // timestamp calculation routine
    let timestamp_calc = |num_ops: usize, num_cells: usize, addr_trace: &[usize]| -> Vec<usize> {
      let mut ts = vec![0usize; num_cells];

      assert!(num_ops >= addr_trace.len());
      for addr in addr_trace {
        assert!(*addr < num_cells);
        ts[*addr] += 1;
      }
      ts
    };

    // timestamp polynomials for row
    let (ts_row, ts_col) =
      rayon::join(|| timestamp_calc(N, N, &row), || timestamp_calc(N, N, &col));

    // a routine to turn a vector of usize into a vector scalars
    let to_vec_scalar = |v: &[usize]| -> Vec<<E as Engine>::Scalar> {
      v.iter()
        .map(|x| <E as Engine>::Scalar::from(*x as u64))
        .collect::<Vec<_>>()
    };

    Self {
      N,

      // dense representation
      row: to_vec_scalar(&row),
      col: to_vec_scalar(&col),
      val_A,
      val_B,
      val_C,

      // timestamp polynomials
      ts_row: to_vec_scalar(&ts_row),
      ts_col: to_vec_scalar(&ts_col),
    }
  }

  pub(in crate::spartan) fn commit(&self, ck: &CommitmentKey<E>) -> ZKR1CSShapeSparkCommitment {
    let blinds = (0..7)
    .map(|_i| <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng))
    .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>();
    let comm_vec: Vec<Commitment<E>> = [
      &self.row,
      &self.col,
      &self.val_A,
      &self.val_B,
      &self.val_C,
      &self.ts_row,
      &self.ts_col,
    ]
    .par_iter().enumerate()
    .map(|(i,v)| <E as Engine>::CE::zkcommit(ck, v, &blinds[i]))
    .collect();

    ZKR1CSShapeSparkCommitment {
      N: self.row.len(),
      comm_row: comm_vec[0],
      comm_col: comm_vec[1],
      comm_val_A: comm_vec[2],
      comm_val_B: comm_vec[3],
      comm_val_C: comm_vec[4],
      comm_ts_row: comm_vec[5],
      comm_ts_col: comm_vec[6],

      r_comm_row: blinds[0],
      r_comm_col: blinds[1],
      r_comm_val_A: blinds[2],
      r_comm_val_B: blinds[3],
      r_comm_val_C: blinds[4],
      r_comm_ts_row: blinds[5],
      r_comm_ts_col: blinds[6],
    }
  }

  // computes evaluation oracles
  fn evaluation_oracles(
    &self,
    S: &R1CSShape<E>,
    r_x: &<E as Engine>::Scalar,
    z: &[<E as Engine>::Scalar],
  ) -> (
    Vec<<E as Engine>::Scalar>,
    Vec<<E as Engine>::Scalar>,
    Vec<<E as Engine>::Scalar>,
    Vec<<E as Engine>::Scalar>,
  ) {
    let mem_row = PowPolynomial::new(r_x, self.N.log_2()).evals();
    let mem_col = padded(z, self.N, &<E as Engine>::Scalar::ZERO);

    let (L_row, L_col) = {
      let mut L_row = vec![mem_row[0]; self.N]; // we place mem_row[0] since resized row is appended with 0s
      let mut L_col = vec![mem_col[self.N - 1]; self.N]; // we place mem_col[N-1] since resized col is appended with N-1

      for (i, (val_r, val_c)) in S
        .A
        .iter()
        .chain(S.B.iter())
        .chain(S.C.iter())
        .map(|(r, c, _)| (mem_row[r], mem_col[c]))
        .enumerate()
      {
        L_row[i] = val_r;
        L_col[i] = val_c;
      }
      (L_row, L_col)
    };

    (mem_row, mem_col, L_row, L_col)
  }
}

/// A type that represents the prover's key
#[derive(Debug, Clone)]
pub struct ProverKey<EE: EvaluationEngineTrait<E>> {
  pk_ee: EE::ProverKey,
  sumcheck_gens: SumcheckGens,
  S_repr: R1CSShapeSparkRepr,
  S_comm: ZKR1CSShapeSparkCommitment,
  vk_digest: <E as Engine>::Scalar, // digest of verifier's key
}

/// A type that represents the verifier's key
#[derive(Debug, Clone, Serialize)]
#[serde(bound = "EE::VerifierKey: Serialize")]
pub struct VerifierKey<EE: EvaluationEngineTrait<E>> {
  num_cons: usize,
  num_vars: usize,
  vk_ee: EE::VerifierKey,
  sumcheck_gens: SumcheckGens,
  S_comm: ZKR1CSShapeSparkCommitment,
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<<E as Engine>::Scalar>,
}

impl<EE: EvaluationEngineTrait<E>> SimpleDigestible for VerifierKey<EE> where
  EE::VerifierKey: Serialize
{
}

/// A succinct proof of knowledge of a witness to a relaxed R1CS instance
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RelaxedR1CSSNARK<EE: EvaluationEngineTrait<E>> {
  // commitment to oracles: the first three are for Az, Bz, Cz,
  // and the last two are for memory reads
  comm_Az: CompressedCommitment<E>,
  comm_Bz: CompressedCommitment<E>,
  comm_Cz: CompressedCommitment<E>,
  comm_L_row: CompressedCommitment<E>,
  comm_L_col: CompressedCommitment<E>,

  // commitments to aid the memory checks
  comm_t_plus_r_inv_row: CompressedCommitment<E>,
  comm_w_plus_r_inv_row: CompressedCommitment<E>,
  comm_t_plus_r_inv_col: CompressedCommitment<E>,
  comm_w_plus_r_inv_col: CompressedCommitment<E>,

  // claims about Az, Bz, and Cz polynomials
  comm_eval_Az_at_tau: CompressedCommitment<E>,
  comm_eval_Bz_at_tau: CompressedCommitment<E>,
  comm_eval_Cz_at_tau: CompressedCommitment<E>,

  // sum-check
  sc: ZKSumcheckProof,

  // claims from the end of sum-check
  comm_eval_Az: CompressedCommitment<E>,
  comm_eval_Bz: CompressedCommitment<E>,
  comm_eval_Cz: CompressedCommitment<E>,
  comm_eval_E: CompressedCommitment<E>,
  comm_eval_L_row: CompressedCommitment<E>,
  comm_eval_L_col: CompressedCommitment<E>,
  comm_eval_val_A: CompressedCommitment<E>,
  comm_eval_val_B: CompressedCommitment<E>,
  comm_eval_val_C: CompressedCommitment<E>,

  comm_eval_W: CompressedCommitment<E>,
  comm_eval_W_X: CompressedCommitment<E>,

  comm_eval_t_plus_r_inv_row: CompressedCommitment<E>,
  comm_eval_row: CompressedCommitment<E>, // address
  comm_eval_w_plus_r_inv_row: CompressedCommitment<E>,
  comm_eval_ts_row: CompressedCommitment<E>,

  comm_eval_t_plus_r_inv_col: CompressedCommitment<E>,
  comm_eval_col: CompressedCommitment<E>, // address
  comm_eval_w_plus_r_inv_col: CompressedCommitment<E>,
  comm_eval_ts_col: CompressedCommitment<E>,

  proof_prod_eval_Az_eval_Bz: ProductProof,
  comm_prod_eval_Az_eval_Bz: CompressedCommitment<E>,

  proof_prod_eval_L_row_eval_L_col: ProductProof,
  comm_prod_eval_L_row_eval_L_col: CompressedCommitment<E>,

  proof_prod_eval_L_row_eval_L_col_eval_val_A: ProductProof,
  comm_prod_eval_L_row_eval_L_col_eval_val_A: CompressedCommitment<E>,

  proof_prod_eval_L_row_eval_L_col_eval_val_B: ProductProof,
  comm_prod_eval_L_row_eval_L_col_eval_val_B: CompressedCommitment<E>,

  proof_prod_eval_L_row_eval_L_col_eval_val_C: ProductProof,
  comm_prod_eval_L_row_eval_L_col_eval_val_C: CompressedCommitment<E>,

  proof_prod_eval_t_plus_r_inv_col_eval_W_X: ProductProof,
  comm_prod_eval_t_plus_r_inv_col_eval_W_X: CompressedCommitment<E>,

  proof_prod_eval_row_eval_w_plus_r_inv_row: ProductProof,
  comm_prod_eval_row_eval_w_plus_r_inv_row: CompressedCommitment<E>,

  proof_prod_eval_L_row_eval_w_plus_r_inv_row: ProductProof,
  comm_prod_eval_L_row_eval_w_plus_r_inv_row: CompressedCommitment<E>,

  proof_prod_eval_w_plus_r_inv_col_eval_col: ProductProof,
  comm_prod_eval_w_plus_r_inv_col_eval_col: CompressedCommitment<E>,

  proof_prod_eval_w_plus_r_inv_col_eval_L_col: ProductProof,
  comm_prod_eval_w_plus_r_inv_col_eval_L_col: CompressedCommitment<E>,

  comm_claim: CompressedCommitment<E>,

  // a PCS evaluation argument
  eval_arg: EE::EvaluationArgument,
}

type E = Bn256EngineZKPedersen;

impl<EE: EvaluationEngineTrait<Bn256EngineZKPedersen>> RelaxedR1CSSNARK<EE> {
  fn prove_helper<T1, T2, T3, T4>(
    ck: &CommitmentKey<E>,
    mem: &mut T1,
    outer: &mut T2,
    inner: &mut T3,
    witness: &mut T4,
    transcript: &mut <E as Engine>::TE,
  ) -> Result<
    (
      ZKSumcheckProof,
      Vec<<E as Engine>::Scalar>,
      Vec<Vec<<E as Engine>::Scalar>>,
      Vec<Vec<<E as Engine>::Scalar>>,
      Vec<Vec<<E as Engine>::Scalar>>,
      Vec<Vec<<E as Engine>::Scalar>>,
      Vec<<E as Engine>::Scalar>,
      Vec<<E as Engine>::Scalar>,
    ),
    NovaError,
  >
  where
    T1: ZKSumcheckEngine,
    T2: ZKSumcheckEngine,
    T3: ZKSumcheckEngine,
    T4: ZKSumcheckEngine,
  {
    // sanity checks
    assert_eq!(mem.size(), outer.size());
    assert_eq!(mem.size(), inner.size());
    assert_eq!(mem.size(), witness.size());
    assert_eq!(mem.degree(), outer.degree());
    assert_eq!(mem.degree(), inner.degree());
    assert_eq!(mem.degree(), witness.degree());

    // these claims are already added to the transcript, so we do not need to add
    let claims = mem
      .initial_claims()
      .into_iter()
      .chain(outer.initial_claims())
      .chain(inner.initial_claims())
      .chain(witness.initial_claims())
      .collect::<Vec<<E as Engine>::Scalar>>();

    let s = transcript.squeeze(b"r")?;
    let coeffs = powers(&s, claims.len());

    // compute the joint claim
    let claim = zip_with!(iter, (claims, coeffs), |c_1, c_2| *c_1 * c_2).sum();

    let mut e = claim;
    let mut r: Vec<<E as Engine>::Scalar> = Vec::new();
    let mut comm_polys = Vec::new();
    let mut comm_evals = Vec::new();
    let proofs = Vec::new();
    
    let num_rounds = mem.size().log_2();

    let (blinds_poly, blinds_evals) = {
      (
          (0..num_rounds)
              .map(|_i| <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng))
              .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>(),
          (0..num_rounds)
              .map(|_i| <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng))
              .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>(),
      )
    };


    for j in 0..num_rounds {
      let ((evals_mem, evals_outer), (evals_inner, evals_witness)) = rayon::join(
        || rayon::join(|| mem.evaluation_points(), || outer.evaluation_points()),
        || rayon::join(|| inner.evaluation_points(), || witness.evaluation_points()),
      );

      let evals: Vec<Vec<<E as Engine>::Scalar>> = evals_mem
        .into_iter()
        .chain(evals_outer.into_iter())
        .chain(evals_inner.into_iter())
        .chain(evals_witness.into_iter())
        .collect::<Vec<Vec<<E as Engine>::Scalar>>>();
      assert_eq!(evals.len(), claims.len());

      let evals_combined_0 = (0..evals.len()).map(|i| evals[i][0] * coeffs[i]).sum();
      let evals_combined_2 = (0..evals.len()).map(|i| evals[i][1] * coeffs[i]).sum();
      let evals_combined_3 = (0..evals.len()).map(|i| evals[i][2] * coeffs[i]).sum();

      let evals = vec![
        evals_combined_0,
        e - evals_combined_0,
        evals_combined_2,
        evals_combined_3,
      ];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      transcript.absorb(b"p", &poly);

      // derive the verifier's challenge for the next round
      let r_i = transcript.squeeze(b"c")?;
      r.push(r_i);

      let _ = rayon::join(
        || rayon::join(|| mem.bound(&r_i), || outer.bound(&r_i)),
        || rayon::join(|| inner.bound(&r_i), || witness.bound(&r_i)),
      );

      e = poly.evaluate(&r_i);
      let comm_e: crate::provider::zk_pedersen::CompressedCommitment<Bn256EngineZKPedersen> = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck, &[e], &blinds_evals[j]).compress();

      let comm_poly: crate::provider::zk_pedersen::CompressedCommitment<Bn256EngineZKPedersen> = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck, &poly.coeffs, &blinds_poly[j]).compress();
      comm_polys.push(comm_poly);
      comm_evals.push(comm_e);
    }

    let mem_claims = mem.final_claims();
    let outer_claims = outer.final_claims();
    let inner_claims = inner.final_claims();
    let witness_claims = witness.final_claims();

    Ok((
      ZKSumcheckProof::new(comm_polys, comm_evals, proofs),
      r,
      mem_claims,
      outer_claims,
      inner_claims,
      witness_claims,
      blinds_poly,
      blinds_evals,
    ))
  }
}

impl<EE: EvaluationEngineTrait<E>> VerifierKey<EE> {
  fn new(
    num_cons: usize,
    num_vars: usize,
    S_comm: ZKR1CSShapeSparkCommitment,
    vk_ee: EE::VerifierKey,
  ) -> Self {
    let scalar_gen = EE::get_scalar_gen_vk(vk_ee.clone());

    Self {
      num_cons,
      num_vars,
      S_comm,
      vk_ee,
      sumcheck_gens: SumcheckGens::new(b"gens_s", &scalar_gen),
      digest: Default::default(),
    }
  }
}
impl<EE: EvaluationEngineTrait<E>> DigestHelperTrait<E> for VerifierKey<EE> {
  /// Returns the digest of the verifier's key
  fn digest(&self) -> <E as Engine>::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc = DigestComputer::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure to retrieve digest!")
  }
}

impl<EE: EvaluationEngineTrait<E>> RelaxedR1CSSNARKTrait<E> for RelaxedR1CSSNARK<EE> {
  type ProverKey = ProverKey<EE>;
  type VerifierKey = VerifierKey<EE>;

  fn ck_floor() -> Box<dyn for<'a> Fn(&'a R1CSShape<E>) -> usize> {
    Box::new(|shape: &R1CSShape<E>| -> usize {
      // the commitment key should be large enough to commit to the R1CS matrices
      shape.A.len() + shape.B.len() + shape.C.len()
    })
  }

  fn setup(
    ck: Arc<CommitmentKey<E>>,
    S: &R1CSShape<E>,
  ) -> Result<(Self::ProverKey, Self::VerifierKey), NovaError> {
    // check the provided commitment key meets minimal requirements
    if ck.length() < Self::ck_floor()(S) {
      return Err(NovaError::InvalidCommitmentKeyLength);
    }
    let (pk_ee, vk_ee) = EE::setup(ck.clone());

    // pad the R1CS matrices
    let S = S.pad();

    let S_repr = R1CSShapeSparkRepr::new(&S);
    let S_comm = S_repr.commit(&*ck);

    let vk = VerifierKey::new(S.num_cons, S.num_vars, S_comm.clone(), vk_ee);

    let scalar_gen: crate::provider::zk_pedersen::CommitmentKey<Bn256EngineZKPedersen> = EE::get_scalar_gen_pk(pk_ee.clone());
    let pk = ProverKey {
      pk_ee,
      sumcheck_gens: SumcheckGens::new(b"gens_s", &scalar_gen),
      S_repr,
      S_comm,
      vk_digest: vk.digest(),
    };

    Ok((pk, vk))
  }

  /// produces a succinct proof of satisfiability of a `RelaxedR1CS` instance
  #[tracing::instrument(skip_all, name = "ZKPPSNARK::prove")]
  fn prove(
    ck: &CommitmentKey<E>,
    pk: &Self::ProverKey,
    S: &R1CSShape<E>,
    U: &RelaxedR1CSInstance<E>,
    W: &ZKRelaxedR1CSWitness<E>,
  ) -> Result<Self, NovaError> {
    // pad the R1CSShape
    let S = S.pad();
    // sanity check that R1CSShape has all required size characteristics
    assert!(S.is_regular_shape());

    let W = W.pad(&S); // pad the witness
    let mut transcript = <E as Engine>::TE::new(b"RelaxedR1CSSNARK");

    // append the verifier key (which includes commitment to R1CS matrices) and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"vk", &pk.vk_digest);
    transcript.absorb(b"U", U);

    // compute the full satisfying assignment by concatenating W.W, U.u, and U.X
    let z = [W.W.clone(), vec![U.u], U.X.clone()].concat();

    // compute Az, Bz, Cz
    let (mut Az, mut Bz, mut Cz) = S.multiply_vec(&z)?;

    let blind_poly_Az = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let blind_eval_Az = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let blind_poly_Bz = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let blind_eval_Bz = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let blind_poly_Cz = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let blind_eval_Cz = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    // commit to Az, Bz, Cz
    let (comm_Az, (comm_Bz, comm_Cz)) = rayon::join(
      || <E as Engine>::CE::zkcommit(ck, &Az, &blind_poly_Az),
      || rayon::join(|| <E as Engine>::CE::zkcommit(ck, &Bz, &blind_poly_Bz), || <E as Engine>::CE::zkcommit(ck, &Cz, &blind_poly_Cz)),
    );

    transcript.absorb(b"c", &[comm_Az, comm_Bz, comm_Cz].as_slice());

    // number of rounds of sum-check
    let num_rounds_sc = pk.S_repr.N.log_2();
    let tau = transcript.squeeze(b"t")?;
    let tau_coords = PowPolynomial::new(&tau, num_rounds_sc).coordinates();

    // (1) send commitments to Az, Bz, and Cz along with their evaluations at tau
    let (Az, Bz, Cz, W, E) = {
      Az.resize(pk.S_repr.N, <E as Engine>::Scalar::ZERO);
      Bz.resize(pk.S_repr.N, <E as Engine>::Scalar::ZERO);
      Cz.resize(pk.S_repr.N, <E as Engine>::Scalar::ZERO);
      let E = padded(&W.E, pk.S_repr.N, &<E as Engine>::Scalar::ZERO);
      let W = padded(&W.W, pk.S_repr.N, &<E as Engine>::Scalar::ZERO);

      (Az, Bz, Cz, W, E)
    };

    let chis_taus = EqPolynomial::evals_from_points(&tau_coords);
    let (eval_Az_at_tau, eval_Bz_at_tau, eval_Cz_at_tau) = {
      let evals_at_tau = [&Az, &Bz, &Cz]
        .into_par_iter()
        .map(|p| MultilinearPolynomial::evaluate_with_chis(p, &chis_taus))
        .collect::<Vec<<E as Engine>::Scalar>>();
      (evals_at_tau[0], evals_at_tau[1], evals_at_tau[2])
    };

    let blind_eval_Az_at_tau = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_Az_at_tau = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_Az_at_tau],
      &blind_eval_Az_at_tau,
    )
    .compress();

    let blind_eval_Bz_at_tau = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_Bz_at_tau = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_Bz_at_tau],
      &blind_eval_Bz_at_tau,
    )
    .compress();

    let blind_eval_Cz_at_tau = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_Cz_at_tau = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_Cz_at_tau],
      &blind_eval_Cz_at_tau,
    )
    .compress();

    // (2) send commitments to the following two oracles
    // L_row(i) = eq(tau, row(i)) for all i
    // L_col(i) = z(col(i)) for all i
    let (mem_row, mem_col, L_row, L_col) = pk.S_repr.evaluation_oracles(&S, &tau, &z);
    
    let blind_L_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let blind_L_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let (comm_L_row, comm_L_col) =
      rayon::join(|| <E as Engine>::CE::zkcommit(ck, &L_row, &blind_L_row), || <E as Engine>::CE::zkcommit(ck, &L_col, &blind_L_col));

    // since all the three polynomials are opened at tau,
    // we can combine them into a single polynomial opened at tau
    let eval_vec = vec![eval_Az_at_tau, eval_Bz_at_tau, eval_Cz_at_tau];

    // absorb the claimed evaluations into the transcript
    transcript.absorb(b"e", &eval_vec.as_slice());
    // absorb commitments to L_row and L_col in the transcript
    transcript.absorb(b"e", &vec![comm_L_row, comm_L_col].as_slice());
    let comm_vec = vec![comm_Az, comm_Bz, comm_Cz];
    let poly_vec = vec![&Az, &Bz, &Cz];
    let c = transcript.squeeze(b"c")?;
    let w: PolyEvalWitness<E> = PolyEvalWitness::batch(&poly_vec, &c);
    let u: PolyEvalInstance<E> =
      PolyEvalInstance::batch(&comm_vec, tau_coords.clone(), &eval_vec, &c);

    // we now need to prove four claims
    // (1) 0 = \sum_x poly_tau(x) * (poly_Az(x) * poly_Bz(x) - poly_uCz_E(x)), and eval_Az_at_tau + r * eval_Bz_at_tau + r^2 * eval_Cz_at_tau = (Az+r*Bz+r^2*Cz)(tau)
    // (2) eval_Az_at_tau + c * eval_Bz_at_tau + c^2 * eval_Cz_at_tau = \sum_y L_row(y) * (val_A(y) + c * val_B(y) + c^2 * val_C(y)) * L_col(y)
    // (3) L_row(i) = eq(tau, row(i)) and L_col(i) = z(col(i))
    // (4) Check that the witness polynomial W is well-formed e.g., it is padded with only zeros
    let gamma = transcript.squeeze(b"g")?;
    let r = transcript.squeeze(b"r")?;

    let ((mut outer_sc_inst, mut inner_sc_inst), mem_res) = rayon::join(
      || {
        // a sum-check instance to prove the first claim
        let outer_sc_inst = OuterSumcheckInstance::new(
          PowPolynomial::new(&tau, num_rounds_sc).evals(),
          Az.clone(),
          Bz.clone(),
          (0..Cz.len())
            .map(|i| U.u * Cz[i] + E[i])
            .collect::<Vec<<E as Engine>::Scalar>>(),
          w.p.clone(), // Mz = Az + r * Bz + r^2 * Cz
          &u.e,        // eval_Az_at_tau + r * eval_Az_at_tau + r^2 * eval_Cz_at_tau
        );

        // a sum-check instance to prove the second claim
        let val = zip_with!(
          par_iter,
          (pk.S_repr.val_A, pk.S_repr.val_B, pk.S_repr.val_C),
          |v_a, v_b, v_c| *v_a + c * *v_b + c * c * *v_c
        )
        .collect::<Vec<<E as Engine>::Scalar>>();
        let inner_sc_inst = InnerSumcheckInstance {
          claim: eval_Az_at_tau + c * eval_Bz_at_tau + c * c * eval_Cz_at_tau,
          poly_L_row: MultilinearPolynomial::new(L_row.clone()),
          poly_L_col: MultilinearPolynomial::new(L_col.clone()),
          poly_val: MultilinearPolynomial::new(val),
        };

        (outer_sc_inst, inner_sc_inst)
      },
      || {
        // a third sum-check instance to prove the read-only memory claim
        // we now need to prove that L_row and L_col are well-formed

        // hash the tuples of (addr,val) memory contents and read responses into a single field element using `hash_func`

        let (comm_mem_oracles, mem_oracles, mem_aux) =
          MemorySumcheckInstance::<E>::compute_oracles(
            ck,
            &r,
            &gamma,
            &mem_row,
            &pk.S_repr.row,
            &L_row,
            &pk.S_repr.ts_row,
            &mem_col,
            &pk.S_repr.col,
            &L_col,
            &pk.S_repr.ts_col,
          )?;
        // absorb the commitments
        transcript.absorb(b"l", &comm_mem_oracles.as_slice());

        let rho = transcript.squeeze(b"r")?;
        let poly_eq = MultilinearPolynomial::new(PowPolynomial::new(&rho, num_rounds_sc).evals());

        Ok::<_, NovaError>((
          MemorySumcheckInstance::new(
            mem_oracles.clone(),
            mem_aux,
            poly_eq.Z,
            pk.S_repr.ts_row.clone(),
            pk.S_repr.ts_col.clone(),
          ),
          comm_mem_oracles,
          mem_oracles,
        ))
      },
    );

    let (mut mem_sc_inst, comm_mem_oracles, mem_oracles) = mem_res?;

    let mut witness_sc_inst = WitnessBoundSumcheck::new(tau, W.clone(), S.num_vars);

    let (sc, rand_sc, claims_mem, claims_outer, claims_inner, claims_witness, _, _) = Self::prove_helper(
      ck,
      &mut mem_sc_inst,
      &mut outer_sc_inst,
      &mut inner_sc_inst,
      &mut witness_sc_inst,
      &mut transcript,
    )?;

    // claims from the end of the sum-check
    let eval_Az = claims_outer[0][0];
    let eval_Bz = claims_outer[0][1];

    let eval_L_row = claims_inner[0][0];
    let blind_eval_L_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_L_row = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_L_row],
    //   &blind_eval_L_row,
    // )
    // .compress();

    let eval_L_col = claims_inner[0][1];
    let blind_eval_L_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_L_col = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_L_col],
    //   &blind_eval_L_col,
    // )
    // .compress();

    let blind_prod_eval_L_row_eval_L_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_L_row_eval_L_col, comm_eval_L_row, comm_eval_L_col, comm_prod_eval_L_row_eval_L_col) = {
      let prod = eval_L_row * eval_L_col;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_L_row,
        &blind_eval_L_row,
        &eval_L_col,
        &blind_eval_L_col,
        &prod,
        &blind_prod_eval_L_row_eval_L_col,
      )
    }?;



    let eval_t_plus_r_inv_row = claims_mem[0][0];
    let blind_eval_t_plus_r_inv_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_t_plus_r_inv_row = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_t_plus_r_inv_row],
      &blind_eval_t_plus_r_inv_row,
    )
    .compress();

    let eval_w_plus_r_inv_row = claims_mem[0][1];
    let blind_eval_w_plus_r_inv_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_w_plus_r_inv_row = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_w_plus_r_inv_row],
    //   &blind_eval_w_plus_r_inv_row,
    // )
    // .compress();

    


    let eval_ts_row = claims_mem[0][2];
    let blind_eval_ts_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_ts_row = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_ts_row],
      &blind_eval_ts_row,
    )
    .compress();

    let eval_t_plus_r_inv_col = claims_mem[1][0];


    let eval_w_plus_r_inv_col = claims_mem[1][1];
    let blind_eval_w_plus_r_inv_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_w_plus_r_inv_col = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_w_plus_r_inv_col],
    //   &blind_eval_w_plus_r_inv_col,
    // )
    // .compress();

    let blind_prod_eval_w_plus_r_inv_col_eval_L_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_w_plus_r_inv_col_eval_L_col, comm_eval_w_plus_r_inv_col, _, comm_prod_eval_w_plus_r_inv_col_eval_L_col) = {
      let prod = eval_w_plus_r_inv_col * eval_L_col;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_w_plus_r_inv_col,
        &blind_eval_w_plus_r_inv_col,
        &eval_L_col,
        &blind_eval_L_col,
        &prod,
        &blind_prod_eval_w_plus_r_inv_col_eval_L_col,
      )
    }?;



    let eval_ts_col = claims_mem[1][2];
    let blind_eval_ts_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_ts_col = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_ts_col],
      &blind_eval_ts_col,
    )
    .compress();

    let eval_W = claims_witness[0][0];

    // compute the remaining claims that did not come for free from the sum-check prover
    let (eval_Cz, eval_E, eval_val_A, eval_val_B, eval_val_C, eval_row, eval_col) = {
      let e = [
        &Cz,
        &E,
        &pk.S_repr.val_A,
        &pk.S_repr.val_B,
        &pk.S_repr.val_C,
        &pk.S_repr.row,
        &pk.S_repr.col,
      ]
      .into_par_iter()
      .map(|p| MultilinearPolynomial::evaluate_with(p, &rand_sc))
      .collect::<Vec<<E as Engine>::Scalar>>();
      (e[0], e[1], e[2], e[3], e[4], e[5], e[6])
    };

    let blind_eval_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_row = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_row],
    //   &blind_eval_row,
    // )
    // .compress();


    let blind_prod_eval_row_eval_w_plus_r_inv_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_row_eval_w_plus_r_inv_row, comm_eval_row, comm_eval_w_plus_r_inv_row, comm_prod_eval_row_eval_w_plus_r_inv_row) = {
      let prod = eval_row * eval_w_plus_r_inv_row;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_row,
        &blind_eval_row,
        &eval_w_plus_r_inv_row,
        &blind_eval_w_plus_r_inv_row,
        &prod,
        &blind_prod_eval_row_eval_w_plus_r_inv_row,
      )
    }?;


    let blind_eval_val_A = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_val_A = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_val_A],
    //   &blind_eval_val_A,
    // )
    // .compress();

    let blind_eval_val_B = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_val_B = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_val_B],
    //   &blind_eval_val_B,
    // )
    // .compress();

    let blind_eval_val_C = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_val_C = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_val_C],
    //   &blind_eval_val_C,
    // )
    // .compress();

    let blind_prod_eval_L_row_eval_L_col_eval_val_A = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_L_row_eval_L_col_eval_val_A, _, comm_eval_val_A, comm_prod_eval_L_row_eval_L_col_eval_val_A) = {
      let eval_L_row_eval_L_col = eval_L_row * eval_L_col;
      let prod = eval_L_row_eval_L_col * eval_val_A;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_L_row_eval_L_col,
        &blind_prod_eval_L_row_eval_L_col,
        &eval_val_A,
        &blind_eval_val_A,
        &prod,
        &blind_prod_eval_L_row_eval_L_col_eval_val_A,
      )
    }?;

    let blind_prod_eval_L_row_eval_L_col_eval_val_B = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_L_row_eval_L_col_eval_val_B, _, comm_eval_val_B, comm_prod_eval_L_row_eval_L_col_eval_val_B) = {
      let eval_L_row_eval_L_col = eval_L_row * eval_L_col;
      let prod = eval_L_row_eval_L_col * eval_val_B;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_L_row_eval_L_col,
        &blind_prod_eval_L_row_eval_L_col,
        &eval_val_B,
        &blind_eval_val_B,
        &prod,
        &blind_prod_eval_L_row_eval_L_col_eval_val_B,
      )
    }?;

    let blind_prod_eval_L_row_eval_L_col_eval_val_C = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_L_row_eval_L_col_eval_val_C, _, comm_eval_val_C, comm_prod_eval_L_row_eval_L_col_eval_val_C) = {
      let eval_L_row_eval_L_col = eval_L_row * eval_L_col;
      let prod = eval_L_row_eval_L_col * eval_val_C;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_L_row_eval_L_col,
        &blind_prod_eval_L_row_eval_L_col,
        &eval_val_C,
        &blind_eval_val_C,
        &prod,
        &blind_prod_eval_L_row_eval_L_col_eval_val_C,
      )
    }?;

    let blind_prod_eval_L_row_eval_w_plus_r_inv_row = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_L_row_eval_w_plus_r_inv_row, _, _, comm_prod_eval_L_row_eval_w_plus_r_inv_row) = {
      let prod = eval_L_row * eval_w_plus_r_inv_row;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_L_row,
        &blind_eval_L_row,
        &eval_w_plus_r_inv_row,
        &blind_eval_w_plus_r_inv_row,
        &prod,
        &blind_prod_eval_L_row_eval_w_plus_r_inv_row,
      )
    }?;

    let blind_eval_W = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_W = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_W],
      &blind_eval_W,
    )
    .compress();

    let eval_W_X = {
        // rand_sc was padded, so we now remove the padding
        let (factor, rand_sc_unpad) = {
          let l = pk.S_comm.N.log_2() - (2 * S.num_vars).log_2();
          let mut factor = <Bn256EngineZKPedersen as traits::Engine>::Scalar::ONE;
          for r_p in rand_sc.iter().take(l) {
            factor *= <Bn256EngineZKPedersen as traits::Engine>::Scalar::ONE - r_p
          }
          let rand_sc_unpad = rand_sc[l..].to_vec();
          (factor, rand_sc_unpad)
        };
        let eval_X = {
          // public IO is (u, X)
          let X = vec![U.u]
            .into_iter()
            .chain(U.X.iter().cloned())
            .collect::<Vec<<Bn256EngineZKPedersen as traits::Engine>::Scalar>>();
          // evaluate the sparse polynomial at rand_sc_unpad[1..]
          let poly_X = SparsePolynomial::new(rand_sc_unpad.len() - 1, X);
          poly_X.evaluate(&rand_sc_unpad[1..])
        };
        eval_W + factor * rand_sc_unpad[0] * eval_X
    };

    let blind_eval_W_X = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_W_X = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_W_X],
    //   &blind_eval_W_X,
    // )
    // .compress();

    let blind_eval_t_plus_r_inv_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_t_plus_r_inv_col = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_t_plus_r_inv_col],
    //   &blind_eval_t_plus_r_inv_col,
    // )
    // .compress();

    let blind_prod_eval_t_plus_r_inv_col_eval_W_X = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_t_plus_r_inv_col_eval_W_X, comm_eval_t_plus_r_inv_col, comm_eval_W_X, comm_prod_eval_t_plus_r_inv_col_eval_W_X) = {
      let prod = eval_t_plus_r_inv_col * eval_W_X;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_t_plus_r_inv_col,
        &blind_eval_t_plus_r_inv_col,
        &eval_W_X,
        &blind_eval_W_X,
        &prod,
        &blind_prod_eval_t_plus_r_inv_col_eval_W_X,
      )
    }?;

    let blind_eval_Az = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_Az = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_Az],
    //   &blind_eval_Az,
    // )
    // .compress();

    let blind_eval_Bz = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_Bz = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_Bz],
    //   &blind_eval_Bz,
    // )
    // .compress();

    let blind_prod_eval_Az_eval_Bz = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_Az_eval_Bz, comm_eval_Az, comm_eval_Bz, comm_prod_eval_Az_eval_Bz) = {
      let prod = eval_Az * eval_Bz;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_Az,
        &blind_eval_Az,
        &eval_Bz,
        &blind_eval_Bz,
        &prod,
        &blind_prod_eval_Az_eval_Bz,
      )
    }?;

    let blind_eval_Cz = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_Cz = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_Cz],
      &blind_eval_Cz,
    )
    .compress();

    let blind_eval_E = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_eval_E = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[eval_E],
      &blind_eval_E,
    )
    .compress();


    let blind_eval_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    // let comm_eval_col = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
    //   &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
    //   &[eval_col],
    //   &blind_eval_col,
    // )
    // .compress();

    let blind_prod_eval_w_plus_r_inv_col_eval_col = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let (proof_prod_eval_w_plus_r_inv_col_eval_col, _, comm_eval_col, comm_prod_eval_w_plus_r_inv_col_eval_col) = {
      let prod = eval_w_plus_r_inv_col * eval_col;
      ProductProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &eval_w_plus_r_inv_col,
        &blind_eval_w_plus_r_inv_col,
        &eval_col,
        &blind_eval_col,
        &prod,
        &blind_prod_eval_w_plus_r_inv_col_eval_col,
      )
    }?;

    let num_rounds_sc = pk.S_comm.N.log_2();
    let tau = transcript.squeeze(b"t")?;
    let tau_coords = PowPolynomial::new(&tau, num_rounds_sc).coordinates();

    // add claims about Az, Bz, and Cz to be checked later
    // since all the three polynomials are opened at tau,
    // we can combine them into a single polynomial opened at tau
    let eval_vec = vec![
      eval_Az_at_tau,
      eval_Bz_at_tau,
      eval_Cz_at_tau,
    ];

    transcript.absorb(b"e", &eval_vec.as_slice());

    transcript.absorb(b"e", &vec![comm_L_row, comm_L_col].as_slice());
    let comm_vec = vec![comm_Az, comm_Bz, comm_Cz];
    let c = transcript.squeeze(b"c")?;
    let u: PolyEvalInstance<E> =
      PolyEvalInstance::batch(&comm_vec, tau_coords.clone(), &eval_vec, &c);
    let claim = u.e;

    let blind_claim = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let comm_claim = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
      &[claim],
      &blind_claim,
    )
    .compress();
  
    // all the evaluations are at rand_sc, we can fold them into one claim
    let eval_vec = vec![
      eval_W,
      eval_Az,
      eval_Bz,
      eval_Cz,
      eval_E,
      eval_L_row,
      eval_L_col,
      eval_val_A,
      eval_val_B,
      eval_val_C,
      eval_t_plus_r_inv_row,
      eval_row,
      eval_w_plus_r_inv_row,
      eval_ts_row,
      eval_t_plus_r_inv_col,
      eval_col,
      eval_w_plus_r_inv_col,
      eval_ts_col,
    ];

    let comm_vec = [
      U.comm_W,
      comm_Az,
      comm_Bz,
      comm_Cz,
      U.comm_E,
      comm_L_row,
      comm_L_col,
      pk.S_comm.comm_val_A,
      pk.S_comm.comm_val_B,
      pk.S_comm.comm_val_C,
      comm_mem_oracles[0],
      pk.S_comm.comm_row,
      comm_mem_oracles[1],
      pk.S_comm.comm_ts_row,
      comm_mem_oracles[2],
      pk.S_comm.comm_col,
      comm_mem_oracles[3],
      pk.S_comm.comm_ts_col,
    ];
    // let poly_vec = [
    //   &W,
    //   &Az,
    //   &Bz,
    //   &Cz,
    //   &E,
    //   &L_row,
    //   &L_col,
    //   &pk.S_repr.val_A,
    //   &pk.S_repr.val_B,
    //   &pk.S_repr.val_C,
    //   mem_oracles[0].as_ref(),
    //   &pk.S_repr.row,
    //   mem_oracles[1].as_ref(),
    //   &pk.S_repr.ts_row,
    //   mem_oracles[2].as_ref(),
    //   &pk.S_repr.col,
    //   mem_oracles[3].as_ref(),
    //   &pk.S_repr.ts_col,
    // ];

    let poly_vec = [
      W,
      Az,
      Bz,
      Cz,
      E,
      L_row,
      L_col,
      pk.S_repr.val_A.clone(),
      pk.S_repr.val_B.clone(),
      pk.S_repr.val_C.clone(),
      mem_oracles[0].clone(),
      pk.S_repr.row.clone(),
      mem_oracles[1].clone(),
      pk.S_repr.ts_row.clone(),
      mem_oracles[2].clone(),
      pk.S_repr.col.clone(),
      mem_oracles[3].clone(),
      pk.S_repr.ts_col.clone(),
    ];

    let blind_poly_vec = vec![];
    let points = vec![];
    let blind_eval_vec = vec![];
    let comm_eval_vec = vec![];

    transcript.absorb(b"e", &eval_vec.as_slice()); // comm_vec is already in the transcript
    // let c = transcript.squeeze(b"c")?;
    // let w: PolyEvalWitness<E> = PolyEvalWitness::batch(&poly_vec, &c);
    // let u: PolyEvalInstance<E> = PolyEvalInstance::batch(&comm_vec, rand_sc.clone(), &eval_vec, &c);

    // let eval_arg = EE::prove_batch(ck, &pk.pk_ee, &mut transcript, &u.c, &w.p, &blind_polys, &rand_sc, &u.e, &blind_evals, comm_evals)?;


    let eval_arg = EE::prove_batch(
      ck,
      &pk.pk_ee,
      &mut transcript,
      &comm_vec,
      &poly_vec.as_slice(),
      &blind_poly_vec,
      &points,
      &eval_vec,
      &blind_eval_vec,
      &comm_eval_vec,
    )?;



    Ok(Self {
      comm_Az: comm_Az.compress(),
      comm_Bz: comm_Bz.compress(),
      comm_Cz: comm_Cz.compress(),
      comm_L_row: comm_L_row.compress(),
      comm_L_col: comm_L_col.compress(),

      comm_t_plus_r_inv_row: comm_mem_oracles[0].compress(),
      comm_w_plus_r_inv_row: comm_mem_oracles[1].compress(),
      comm_t_plus_r_inv_col: comm_mem_oracles[2].compress(),
      comm_w_plus_r_inv_col: comm_mem_oracles[3].compress(),

      comm_eval_Az_at_tau,
      comm_eval_Bz_at_tau,
      comm_eval_Cz_at_tau,

      sc,

      comm_eval_Az,
      comm_eval_Bz,
      comm_eval_Cz,
      comm_eval_E,
      comm_eval_L_row,
      comm_eval_L_col,
      comm_eval_val_A,
      comm_eval_val_B,
      comm_eval_val_C,

      comm_eval_W,
      comm_eval_W_X,

      comm_eval_t_plus_r_inv_row,
      comm_eval_row,
      comm_eval_w_plus_r_inv_row,
      comm_eval_ts_row,

      comm_eval_col,
      comm_eval_t_plus_r_inv_col,
      comm_eval_w_plus_r_inv_col,
      comm_eval_ts_col,

      proof_prod_eval_Az_eval_Bz,
      comm_prod_eval_Az_eval_Bz,

      proof_prod_eval_L_row_eval_L_col,
      comm_prod_eval_L_row_eval_L_col,

      proof_prod_eval_L_row_eval_L_col_eval_val_A,
      comm_prod_eval_L_row_eval_L_col_eval_val_A,

      proof_prod_eval_L_row_eval_L_col_eval_val_B,
      comm_prod_eval_L_row_eval_L_col_eval_val_B,

      proof_prod_eval_L_row_eval_L_col_eval_val_C,
      comm_prod_eval_L_row_eval_L_col_eval_val_C,

      proof_prod_eval_t_plus_r_inv_col_eval_W_X,
      comm_prod_eval_t_plus_r_inv_col_eval_W_X,

      proof_prod_eval_row_eval_w_plus_r_inv_row,
      comm_prod_eval_row_eval_w_plus_r_inv_row,

      proof_prod_eval_L_row_eval_w_plus_r_inv_row,
      comm_prod_eval_L_row_eval_w_plus_r_inv_row,

      proof_prod_eval_w_plus_r_inv_col_eval_col,
      comm_prod_eval_w_plus_r_inv_col_eval_col,

      proof_prod_eval_w_plus_r_inv_col_eval_L_col,
      comm_prod_eval_w_plus_r_inv_col_eval_L_col,

      comm_claim,

      eval_arg,
    })
  }

  /// verifies a proof of satisfiability of a `RelaxedR1CS` instance
  fn verify(&self, vk: &Self::VerifierKey, U: &RelaxedR1CSInstance<E>) -> Result<(), NovaError> {
    let mut transcript = <E as Engine>::TE::new(b"RelaxedR1CSSNARK");

    // append the verifier key (including commitment to R1CS matrices) and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"vk", &vk.digest());
    transcript.absorb(b"U", U);

    let comm_Az = Commitment::<E>::decompress(&self.comm_Az)?;
    let comm_Bz = Commitment::<E>::decompress(&self.comm_Bz)?;
    let comm_Cz = Commitment::<E>::decompress(&self.comm_Cz)?;
    let comm_L_row = Commitment::<E>::decompress(&self.comm_L_row)?;
    let comm_L_col = Commitment::<E>::decompress(&self.comm_L_col)?;
    let comm_t_plus_r_inv_row = Commitment::<E>::decompress(&self.comm_t_plus_r_inv_row)?;
    let comm_w_plus_r_inv_row = Commitment::<E>::decompress(&self.comm_w_plus_r_inv_row)?;
    let comm_t_plus_r_inv_col = Commitment::<E>::decompress(&self.comm_t_plus_r_inv_col)?;
    let comm_w_plus_r_inv_col = Commitment::<E>::decompress(&self.comm_w_plus_r_inv_col)?;

    let comm_eval_t_plus_r_inv_row: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_t_plus_r_inv_row)?;
    let comm_eval_w_plus_r_inv_row: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_w_plus_r_inv_row)?;
    let comm_eval_t_plus_r_inv_col: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_t_plus_r_inv_col)?;
    let comm_eval_w_plus_r_inv_col: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_w_plus_r_inv_col)?;

    let comm_eval_ts_row: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_ts_row)?;
    let comm_eval_ts_col: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_ts_col)?;

    let comm_eval_Az: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_Az)?;
    let comm_eval_Bz: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_Bz)?;
    let comm_eval_Cz: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_Cz)?;
    let comm_eval_E: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_E)?;
    // let comm_eval_L_row: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_L_row)?;
    // let comm_eval_L_col: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_L_col)?;
    // let comm_eval_val_A: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_val_A)?;
    // let comm_eval_val_B: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_val_B)?;
    // let comm_eval_val_C: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_val_C)?;

    // let comm_eval_W_X: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_eval_W_X)?;

    let comm_claim: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_claim)?;

    let comm_prod_eval_Az_eval_Bz: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_Az_eval_Bz)?;

    self.proof_prod_eval_Az_eval_Bz.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_eval_Az,
        &self.comm_eval_Bz,
        &self.comm_prod_eval_Az_eval_Bz,
    )?;

    // let comm_prod_eval_L_row_eval_L_col: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_L_row_eval_L_col)?;

    self.proof_prod_eval_L_row_eval_L_col.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_eval_L_row,
        &self.comm_eval_L_col,
        &self.comm_prod_eval_L_row_eval_L_col,
    )?;

    let comm_prod_eval_L_row_eval_L_col_eval_val_A: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_L_row_eval_L_col_eval_val_A)?;

    self.proof_prod_eval_L_row_eval_L_col_eval_val_A.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_prod_eval_L_row_eval_L_col,
        &self.comm_eval_val_A,
        &self.comm_prod_eval_L_row_eval_L_col_eval_val_A,
    )?;

    let comm_prod_eval_L_row_eval_L_col_eval_val_B: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_L_row_eval_L_col_eval_val_B)?;

    self.proof_prod_eval_L_row_eval_L_col_eval_val_B.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_prod_eval_L_row_eval_L_col,
        &self.comm_eval_val_B,
        &self.comm_prod_eval_L_row_eval_L_col_eval_val_B,
    )?;


    let comm_prod_eval_L_row_eval_L_col_eval_val_C: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_L_row_eval_L_col_eval_val_C)?;

    self.proof_prod_eval_L_row_eval_L_col_eval_val_C.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_prod_eval_L_row_eval_L_col,
        &self.comm_eval_val_C,
        &self.comm_prod_eval_L_row_eval_L_col_eval_val_C,
    )?;

    let comm_prod_eval_t_plus_r_inv_col_eval_W_X: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_t_plus_r_inv_col_eval_W_X)?;

    self.proof_prod_eval_t_plus_r_inv_col_eval_W_X.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_eval_t_plus_r_inv_col,
        &self.comm_eval_W_X,
        &self.comm_prod_eval_t_plus_r_inv_col_eval_W_X,
    )?;

    let comm_prod_eval_row_eval_w_plus_r_inv_row: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_row_eval_w_plus_r_inv_row)?;

    self.proof_prod_eval_row_eval_w_plus_r_inv_row.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_eval_row,
        &self.comm_eval_w_plus_r_inv_row,
        &self.comm_prod_eval_row_eval_w_plus_r_inv_row,
    )?;

    let comm_prod_eval_L_row_eval_w_plus_r_inv_row: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_L_row_eval_w_plus_r_inv_row)?;

    self.proof_prod_eval_L_row_eval_w_plus_r_inv_row.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_eval_L_row,
        &self.comm_eval_w_plus_r_inv_row,
        &self.comm_prod_eval_L_row_eval_w_plus_r_inv_row,
    )?;

    let comm_prod_eval_w_plus_r_inv_col_eval_col: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_w_plus_r_inv_col_eval_col)?;

    self.proof_prod_eval_w_plus_r_inv_col_eval_col.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_eval_w_plus_r_inv_col,
        &self.comm_eval_col,
        &self.comm_prod_eval_w_plus_r_inv_col_eval_col,
    )?;

    let comm_prod_eval_w_plus_r_inv_col_eval_L_col: crate::provider::zk_pedersen::Commitment<Bn256EngineZKPedersen> = Commitment::<E>::decompress(&self.comm_prod_eval_w_plus_r_inv_col_eval_L_col)?;

    self.proof_prod_eval_w_plus_r_inv_col_eval_L_col.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &self.comm_eval_w_plus_r_inv_col,
        &self.comm_eval_L_col,
        &self.comm_prod_eval_w_plus_r_inv_col_eval_L_col,
    )?;

    transcript.absorb(b"c", &[comm_Az, comm_Bz, comm_Cz].as_slice());

    let num_rounds_sc = vk.S_comm.N.log_2();
    let tau = transcript.squeeze(b"t")?;
    // let tau_coords = PowPolynomial::new(&tau, num_rounds_sc).coordinates();

    // // add claims about Az, Bz, and Cz to be checked later
    // // since all the three polynomials are opened at tau,
    // // we can combine them into a single polynomial opened at tau
    // let eval_vec = vec![
    //   self.eval_Az_at_tau,
    //   self.eval_Bz_at_tau,
    //   self.eval_Cz_at_tau,
    // ];

    // transcript.absorb(b"e", &eval_vec.as_slice());

    // transcript.absorb(b"e", &vec![comm_L_row, comm_L_col].as_slice());
    // let comm_vec = vec![comm_Az, comm_Bz, comm_Cz];
    let c = transcript.squeeze(b"c")?;
    // let u: PolyEvalInstance<E> =
    //   PolyEvalInstance::batch(&comm_vec, tau_coords.clone(), &eval_vec, &c);
    // let claim = u.e;

    let gamma = transcript.squeeze(b"g")?;

    let r = transcript.squeeze(b"r")?;

    transcript.absorb(
      b"l",
      &vec![
        comm_t_plus_r_inv_row,
        comm_w_plus_r_inv_row,
        comm_t_plus_r_inv_col,
        comm_w_plus_r_inv_col,
      ]
      .as_slice(),
    );

    let rho = transcript.squeeze(b"r")?;

    let num_claims = 10;
    let s = transcript.squeeze(b"r")?;
    let coeffs = powers(&s, num_claims);
    let comm_claim = comm_claim * (coeffs[7] + coeffs[8]); // rest are zeros

    // verify sc
    // let (claim_sc_final, rand_sc) = self.sc.verify(claim, num_rounds_sc, 3, &mut transcript)?;

    // let comm_claim =
    // <Bn256EngineZKPedersen as Engine>::CE::zkcommit(&vk.sumcheck_gens.ck_1, &[claim], &<Bn256EngineZKPedersen as Engine>::Scalar::ZERO).compress();


    let (claim_sc_final, rand_sc) = self.sc.verify(
        &comm_claim.compress(),
        num_rounds_sc,
        3,
        &vk.sumcheck_gens.ck_1,
        &vk.sumcheck_gens.ck_4,
        &mut transcript,
    )?;

    // verify claim_sc_final
    let claim_sc_final_expected = {
      let rand_eq_bound_rand_sc = PowPolynomial::new(&rho, num_rounds_sc).evaluate(&rand_sc);
      let eq_tau: EqPolynomial<_> = PowPolynomial::new(&tau, num_rounds_sc).into();

      let taus_bound_rand_sc = eq_tau.evaluate(&rand_sc);
      let taus_masked_bound_rand_sc =
        MaskedEqPolynomial::new(&eq_tau, vk.num_vars.log_2()).evaluate(&rand_sc);

      let eval_t_plus_row = {
        let eval_addr_row = IdentityPolynomial::new(num_rounds_sc).evaluate(&rand_sc);
        let eval_val_row = taus_bound_rand_sc;
        let eval_t = eval_addr_row + gamma * eval_val_row;
        eval_t
      };

      // let eval_w_plus_row = {
      //   let eval_addr_row = self.eval_row;
      //   let eval_val_row = self.eval_L_row;
      //   let eval_w = eval_addr_row + gamma * eval_val_row;
      //   eval_w
      // };

      let eval_addr_col_t = IdentityPolynomial::new(num_rounds_sc).evaluate(&rand_sc);


      // let eval_t_plus_col = {
      //   // memory contents is z, so we compute eval_Z from eval_W and eval_X
      //   // let eval_val_col = {
      //   //   // rand_sc was padded, so we now remove the padding
      //   //   let (factor, rand_sc_unpad) = {
      //   //     let l = vk.S_comm.N.log_2() - (2 * vk.num_vars).log_2();

      //   //     let mut factor = E::Scalar::ONE;
      //   //     for r_p in rand_sc.iter().take(l) {
      //   //       factor *= E::Scalar::ONE - r_p
      //   //     }

      //   //     let rand_sc_unpad = rand_sc[l..].to_vec();

      //   //     (factor, rand_sc_unpad)
      //   //   };

      //   //   let eval_X = {
      //   //     // public IO is (u, X)
      //   //     let X = vec![U.u]
      //   //       .into_iter()
      //   //       .chain(U.X.iter().cloned())
      //   //       .collect::<Vec<E::Scalar>>();

      //   //     // evaluate the sparse polynomial at rand_sc_unpad[1..]
      //   //     let poly_X = SparsePolynomial::new(rand_sc_unpad.len() - 1, X);
      //   //     poly_X.evaluate(&rand_sc_unpad[1..])
      //   //   };

      //   //   self.eval_W + factor * rand_sc_unpad[0] * eval_X
      //   // };
      //   let eval_t = comm_eval_W_X *  gamma;
      //   eval_t
      // };

      // let eval_w_plus_col = {
      //   let eval_addr_col = self.eval_col;
      //   let eval_val_col = self.eval_L_col;
      //   let eval_w = eval_addr_col + gamma * eval_val_col;
      //   eval_w
      // };

      let claim_one =
      <Bn256EngineZKPedersen as Engine>::CE::zkcommit(&vk.sumcheck_gens.ck_1, &[<Bn256EngineZKPedersen as Engine>::Scalar::ONE], &<Bn256EngineZKPedersen as Engine>::Scalar::ZERO);


      let claim_mem_final_expected = (comm_eval_t_plus_r_inv_row - comm_eval_w_plus_r_inv_row) 
        * coeffs[0]
        + (comm_eval_t_plus_r_inv_col - comm_eval_w_plus_r_inv_col) * coeffs[1]
        + ((comm_eval_t_plus_r_inv_row * eval_t_plus_row + comm_eval_t_plus_r_inv_row * r - comm_eval_ts_row) * rand_eq_bound_rand_sc) * coeffs[2]
        + ((comm_prod_eval_row_eval_w_plus_r_inv_row + comm_prod_eval_L_row_eval_w_plus_r_inv_row * gamma + comm_eval_w_plus_r_inv_row * r - claim_one) * rand_eq_bound_rand_sc) * coeffs[3]
        + ((comm_prod_eval_t_plus_r_inv_col_eval_W_X * gamma + comm_eval_t_plus_r_inv_col * eval_addr_col_t + comm_eval_t_plus_r_inv_col * r - comm_eval_ts_col) * rand_eq_bound_rand_sc) * coeffs[4]
        + ((comm_prod_eval_w_plus_r_inv_col_eval_col + comm_prod_eval_w_plus_r_inv_col_eval_L_col * gamma + comm_eval_w_plus_r_inv_col * r - claim_one) * rand_eq_bound_rand_sc) * coeffs[5];

      let claim_outer_final_expected = (comm_prod_eval_Az_eval_Bz - comm_eval_Cz * U.u - comm_eval_E) * coeffs[6]
        * taus_bound_rand_sc 
        + (comm_eval_Az + comm_eval_Bz * c + comm_eval_Cz * c * c) * coeffs[7] * taus_bound_rand_sc;
      let claim_inner_final_expected = (comm_prod_eval_L_row_eval_L_col_eval_val_A + comm_prod_eval_L_row_eval_L_col_eval_val_B * c + comm_prod_eval_L_row_eval_L_col_eval_val_C * c * c) * coeffs[8];

      let claim_witness_final_expected = Commitment::<E>::decompress(&self.comm_eval_W)? * coeffs[9] * taus_masked_bound_rand_sc;

      claim_mem_final_expected
        + claim_outer_final_expected
        + claim_inner_final_expected
        + claim_witness_final_expected
    };

    if claim_sc_final_expected != Commitment::<E>::decompress(&claim_sc_final)? {
      return Err(NovaError::InvalidSumcheckProof);
    }

    // let eval_vec = vec![
    //   self.eval_W,
    //   self.eval_Az,
    //   self.eval_Bz,
    //   self.eval_Cz,
    //   self.eval_E,
    //   self.eval_L_row,
    //   self.eval_L_col,
    //   self.eval_val_A,
    //   self.eval_val_B,
    //   self.eval_val_C,
    //   self.eval_t_plus_r_inv_row,
    //   self.eval_row,
    //   self.eval_w_plus_r_inv_row,
    //   self.eval_ts_row,
    //   self.eval_t_plus_r_inv_col,
    //   self.eval_col,
    //   self.eval_w_plus_r_inv_col,
    //   self.eval_ts_col,
    // ];

    let comm_vec = [
      U.comm_W,
      comm_Az,
      comm_Bz,
      comm_Cz,
      U.comm_E,
      comm_L_row,
      comm_L_col,
      vk.S_comm.comm_val_A,
      vk.S_comm.comm_val_B,
      vk.S_comm.comm_val_C,
      comm_t_plus_r_inv_row,
      vk.S_comm.comm_row,
      comm_w_plus_r_inv_row,
      vk.S_comm.comm_ts_row,
      comm_t_plus_r_inv_col,
      vk.S_comm.comm_col,
      comm_w_plus_r_inv_col,
      vk.S_comm.comm_ts_col,
    ];
    // transcript.absorb(b"e", &eval_vec.as_slice()); // comm_vec is already in the transcript
    // let c = transcript.squeeze(b"c")?;
    // let u: PolyEvalInstance<E> = PolyEvalInstance::batch(&comm_vec, rand_sc.clone(), &eval_vec, &c);

    let mut points = Vec::with_capacity(18);
    points.resize(18, rand_sc);

    // verify
    EE::verify_batch(
      &vk.vk_ee,
      &mut transcript,
      &comm_vec,
      &points,
      &self.eval_arg,
    )?;

    Ok(())
  }
}
