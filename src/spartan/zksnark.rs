//! This module implements RelaxedR1CSSNARKTrait using Spartan that is generic
//! over the polynomial commitment and evaluation argument (i.e., a PCS)

use crate::{
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  r1cs::{R1CSShape, RelaxedR1CSInstance, ZKRelaxedR1CSWitness},
  spartan::{
    compute_eval_table_sparse,
    nizk::{EqualityProof, KnowledgeProof, ProductProof},
    polys::{eq::EqPolynomial, multilinear::MultilinearPolynomial, multilinear::SparsePolynomial},
    zksumcheck::ZKSumcheckProof,
    SparseMatrix,
  },
  traits::{
    zkevaluation::EvaluationEngineTrait,
    zksnark::{DigestHelperTrait, RelaxedR1CSSNARKTrait},
    Engine, TranscriptEngineTrait,
  },
  Commitment, CommitmentKey, CompressedCommitment, provider::Bn256EngineZKPedersen, CommitmentTrait
};
use once_cell::sync::OnceCell;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use crate::traits::commitment::ZKCommitmentEngineTrait;
use rayon::prelude::*;
use crate::traits::zkevaluation::GetEvalCommitmentsTrait;

use ff::Field;

///A type that represents generators for commitments used in sumcheck
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SumcheckGens {
  /// 1 Generator
  pub ck_1: CommitmentKey<Bn256EngineZKPedersen>,
  /// 3 Generators
  pub ck_3: CommitmentKey<Bn256EngineZKPedersen>,
  /// 4 Generators
  pub ck_4: CommitmentKey<Bn256EngineZKPedersen>,
}

impl SumcheckGens {
  /// Creates new generators for sumcheck
  pub fn new(label: &'static [u8], scalar_gen: &CommitmentKey<Bn256EngineZKPedersen>) -> Self {
    let ck_1 = scalar_gen.clone();
    let ck_3 = <Bn256EngineZKPedersen as Engine>::CE::setup_exact_with_blinding(label, 3, &<Bn256EngineZKPedersen as Engine>::CE::get_blinding_gen(&ck_1));
    let ck_4 = <Bn256EngineZKPedersen as Engine>::CE::setup_exact_with_blinding(label, 4, &<Bn256EngineZKPedersen as Engine>::CE::get_blinding_gen(&ck_1));

    Self { ck_1, ck_3, ck_4 }
  }
}

/// A type that represents the prover's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<EE>
where
  EE: EvaluationEngineTrait<Bn256EngineZKPedersen>,
{
  pk_ee: EE::ProverKey,
  sumcheck_gens: SumcheckGens,
  vk_digest: <Bn256EngineZKPedersen as Engine>::Scalar, // digest of the verifier's key
}

/// A type that represents the verifier's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifierKey<EE>
where
  EE: EvaluationEngineTrait<Bn256EngineZKPedersen>,
{
  vk_ee: EE::VerifierKey,
  sumcheck_gens: SumcheckGens,
  S: R1CSShape<Bn256EngineZKPedersen>,
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<<Bn256EngineZKPedersen as Engine>::Scalar>,
}

impl<EE> SimpleDigestible for VerifierKey<EE>
where
  EE: EvaluationEngineTrait<Bn256EngineZKPedersen>,
{
}

impl<EE> VerifierKey<EE>
where
  EE: EvaluationEngineTrait<Bn256EngineZKPedersen>,
{
  fn new(shape: R1CSShape<Bn256EngineZKPedersen>, vk_ee: EE::VerifierKey) -> Self {
    let scalar_gen = EE::get_scalar_gen_vk(vk_ee.clone());

    VerifierKey {
      vk_ee,
      sumcheck_gens: SumcheckGens::new(b"gens_s", &scalar_gen),
      S: shape,
      digest: OnceCell::new(),
    }
  }
}

impl<EE> DigestHelperTrait<Bn256EngineZKPedersen> for VerifierKey<EE>
where
  EE: EvaluationEngineTrait<Bn256EngineZKPedersen>,
{
  /// Returns the digest of the verifier's key.
  fn digest(&self) -> <Bn256EngineZKPedersen as Engine>::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc = DigestComputer::<<Bn256EngineZKPedersen as Engine>::Scalar, _>::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure to retrieve digest!")
  }
}

/// A succinct proof of knowledge of a witness to a relaxed R1CS instance
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RelaxedR1CSSNARK<EE>
where
  EE: EvaluationEngineTrait<Bn256EngineZKPedersen>,
{
  sc_proof_outer: ZKSumcheckProof,
  claims_outer: (
    CompressedCommitment<Bn256EngineZKPedersen>,
    CompressedCommitment<Bn256EngineZKPedersen>,
    CompressedCommitment<Bn256EngineZKPedersen>,
    CompressedCommitment<Bn256EngineZKPedersen>,
  ),
  sc_proof_inner: ZKSumcheckProof,
  pok_claims_inner: (KnowledgeProof, ProductProof),
  proof_eq_sc_outer: EqualityProof,
  proof_eq_sc_inner: EqualityProof,
  eval_arg: EE::EvaluationArgument,
}

impl<EE> RelaxedR1CSSNARKTrait<Bn256EngineZKPedersen> for RelaxedR1CSSNARK<EE>
where
  EE: EvaluationEngineTrait<Bn256EngineZKPedersen>,
{
  type ProverKey = ProverKey<EE>;
  type VerifierKey = VerifierKey<EE>;

  #[allow(dead_code)]
  fn setup(
    ck: Arc<CommitmentKey<Bn256EngineZKPedersen>>,
    S: &R1CSShape<Bn256EngineZKPedersen>,
  ) -> Result<(Self::ProverKey, Self::VerifierKey), crate::errors::NovaError> {
    let (pk_ee, vk_ee) = EE::setup(ck);

    let S = S.pad();

    let vk: VerifierKey<EE> = VerifierKey::new(S, vk_ee);

    let scalar_gen = EE::get_scalar_gen_pk(pk_ee.clone());
    let pk = ProverKey {
      pk_ee,
      sumcheck_gens: SumcheckGens::new(b"gens_s", &scalar_gen),
      vk_digest: vk.digest(),
    };

    Ok((pk, vk))
  }

  /// produces a succinct proof of satisfiability of a RelaxedR1CS instance
  #[allow(dead_code)]
  fn prove(
    ck: &CommitmentKey<Bn256EngineZKPedersen>,
    pk: &Self::ProverKey,
    S: &R1CSShape<Bn256EngineZKPedersen>,
    U: &RelaxedR1CSInstance<Bn256EngineZKPedersen>,
    W: &ZKRelaxedR1CSWitness<Bn256EngineZKPedersen>,
  ) -> Result<Self, NovaError>{
    
    // pad the R1CSShape
    let S = S.pad();
    // sanity check that R1CSShape has all required size characteristics
    assert!(S.is_regular_shape());

    let W = W.pad(&S); // pad the witness
    let mut transcript = <Bn256EngineZKPedersen as Engine>::TE::new(b"RelaxedR1CSSNARK");

    // append the digest of vk (which includes R1CS matrices) and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"vk", &pk.vk_digest);
    transcript.absorb(b"U", U);
    
    
    // compute the full satisfying assignment by concatenating W.W, U.u, and U.X
    let mut z = [W.W.clone(), vec![U.u], U.X.clone()].concat();

    let (num_rounds_x, num_rounds_y) = (
      (S.num_cons as f64).log2() as usize,
      ((S.num_vars as f64).log2() as usize + 1),
    );

    // outer sum-check
    let tau = (0..num_rounds_x)
      .map(|_i| transcript.squeeze(b"t"))
      .collect::<Result<EqPolynomial<_>, NovaError>>()?;

    let mut poly_tau = MultilinearPolynomial::new(tau.evals());

    let (mut poly_Az, mut poly_Bz, poly_Cz, mut poly_uCz_E) = {
      let (poly_Az, poly_Bz, poly_Cz) = S.multiply_vec(&z)?;
      let poly_uCz_E = (0..S.num_cons)
        .map(|i| U.u * poly_Cz[i] + W.E[i])
        .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>();
      (
        MultilinearPolynomial::new(poly_Az),
        MultilinearPolynomial::new(poly_Bz),
        MultilinearPolynomial::new(poly_Cz),
        MultilinearPolynomial::new(poly_uCz_E),
      )
    };

    let comb_func_outer =
      |poly_A_comp: &<Bn256EngineZKPedersen as Engine>::Scalar,
       poly_B_comp: &<Bn256EngineZKPedersen as Engine>::Scalar,
       poly_C_comp: &<Bn256EngineZKPedersen as Engine>::Scalar,
       poly_D_comp: &<Bn256EngineZKPedersen as Engine>::Scalar|
       -> <Bn256EngineZKPedersen as Engine>::Scalar { *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp) };

    let (sc_proof_outer, r_x, _claims_outer, blind_claim_post_outer) =
      ZKSumcheckProof::prove_cubic_with_additive_term(
        &<Bn256EngineZKPedersen as Engine>::Scalar::ZERO, // claim is zero
        &<Bn256EngineZKPedersen as Engine>::Scalar::ZERO, // blind for claim is also zero
        num_rounds_x,
        &mut poly_tau,
        &mut poly_Az,
        &mut poly_Bz,
        &mut poly_uCz_E,
        comb_func_outer,
        &pk.sumcheck_gens.ck_1,
        &pk.sumcheck_gens.ck_4,
        &mut transcript,
      )?;

      assert_eq!(poly_tau.len(), 1);
      assert_eq!(poly_Az.len(), 1);
      assert_eq!(poly_Bz.len(), 1);
      assert_eq!(poly_uCz_E.len(), 1);

      let (tau_claim, Az_claim, Bz_claim) = (&poly_tau[0], &poly_Az[0], &poly_Bz[0]);

      let Cz_claim = poly_Cz.evaluate(&r_x);

      let (Az_blind, Bz_blind, Cz_blind, prod_Az_Bz_blind) = (
        <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng),
        <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng),
        <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng),
        <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng),
      );

      let (pok_Cz_claim, comm_Cz_claim) = {
        KnowledgeProof::prove(
          &pk.sumcheck_gens.ck_1,
          &mut transcript,
          &Cz_claim,
          &Cz_blind,
        )
      }?;

      let (proof_prod, comm_Az_claim, comm_Bz_claim, comm_prod_Az_Bz_claims) = {
        let prod = *Az_claim * *Bz_claim;
        ProductProof::prove(
          &pk.sumcheck_gens.ck_1,
          &mut transcript,
          Az_claim,
          &Az_blind,
          Bz_claim,
          &Bz_blind,
          &prod,
          &prod_Az_Bz_blind,
        )
      }?;

      
      // prove the final step of sumcheck outer
      let taus_bound_rx = tau_claim;

      // Evaluate E at r_x. We do this to compute blind and claim of outer sumcheck
      let eval_E = MultilinearPolynomial::new(W.E.clone()).evaluate(&r_x);
      let blind_eval_E = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
      let comm_eval_E = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
        &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
        &[eval_E],
        &blind_eval_E,
      )
      .compress();
      transcript.absorb(b"comm_eval_E", &comm_eval_E);

      let blind_expected_claim_outer =
        *taus_bound_rx * (prod_Az_Bz_blind - (U.u * Cz_blind + blind_eval_E));
      let claim_post_outer = *taus_bound_rx * (*Az_claim * *Bz_claim - (U.u * Cz_claim + eval_E));

      let (proof_eq_sc_outer, _C1, _C2) = EqualityProof::prove(
        &pk.sumcheck_gens.ck_1,
        &mut transcript,
        &claim_post_outer,
        &blind_expected_claim_outer,
        &claim_post_outer,
        &blind_claim_post_outer,
      )?;


      // Combine the three claims into a single claim
      let r: <Bn256EngineZKPedersen as Engine>::Scalar = transcript.squeeze(b"r")?;
      let claim_inner_joint = *Az_claim + r * Bz_claim + r * r * Cz_claim;
      let blind_claim_inner_joint = Az_blind + r * Bz_blind + r * r * Cz_blind;

      let poly_ABC = {
        // compute the initial evaluation table for R(\tau, x)
        let evals_rx = EqPolynomial::evals_from_points(&r_x.clone());

        let (evals_A, evals_B, evals_C) = compute_eval_table_sparse(&S, &evals_rx);

        assert_eq!(evals_A.len(), evals_B.len());
        assert_eq!(evals_A.len(), evals_C.len());
        (0..evals_A.len())
          .into_par_iter()
          .map(|i| evals_A[i] + r * evals_B[i] + r * r * evals_C[i])
          .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>()
      };

      let poly_z = {
        z.resize(S.num_vars * 2, <Bn256EngineZKPedersen as Engine>::Scalar::ZERO);
        z
      };

      let comb_func = |poly_A_comp: &<Bn256EngineZKPedersen as Engine>::Scalar, poly_B_comp: &<Bn256EngineZKPedersen as Engine>::Scalar| -> <Bn256EngineZKPedersen as Engine>::Scalar {
        *poly_A_comp * *poly_B_comp
      };

      let (sc_proof_inner, r_y, claims_inner, blind_claim_postsc_inner) =
        ZKSumcheckProof::prove_quad(
          &claim_inner_joint,
          &blind_claim_inner_joint,
          num_rounds_y,
          &mut MultilinearPolynomial::new(poly_z),
          &mut MultilinearPolynomial::new(poly_ABC),
          comb_func,
          &pk.sumcheck_gens.ck_1,
          &pk.sumcheck_gens.ck_3,
          &mut transcript,
        )?;

      let eval_W = MultilinearPolynomial::new(W.W.clone()).evaluate(&r_y[1..]);
      let blind_eval_W = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
      let comm_eval_W = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
        &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
        &[eval_W],
        &blind_eval_W,
      )
      .compress();
      transcript.absorb(b"comm_eval_W", &comm_eval_W);

      // prove the final step of inner sumcheck
      let blind_eval_Z_at_ry = (<Bn256EngineZKPedersen as Engine>::Scalar::ONE - r_y[0]) * blind_eval_W;
      let blind_expected_claim_post_inner = claims_inner[1] * blind_eval_Z_at_ry;
      let claim_post_inner = claims_inner[0] * claims_inner[1];

      let (proof_eq_sc_inner, _C1, _C2) = EqualityProof::prove(
        &EE::get_scalar_gen_pk(pk.pk_ee.clone()),
        &mut transcript,
        &claim_post_inner,
        &blind_expected_claim_post_inner,
        &claim_post_inner,
        &blind_claim_postsc_inner,
      )?;

      // prove the correctness of eval_E and eval_W
      let eval_arg = EE::prove_batch(
        ck,
        &pk.pk_ee,
        &mut transcript,
        &[U.comm_E, U.comm_W],
        &[W.E.clone(), W.W.clone()],
        &[W.r_E, W.r_W],
        &[r_x, r_y[1..].to_vec()],
        &[eval_E, eval_W],
        &[blind_eval_E, blind_eval_W],
        &[comm_eval_E, comm_eval_W],
      )?;

      Ok(RelaxedR1CSSNARK {
        sc_proof_outer,
        claims_outer: (
          comm_Az_claim,
          comm_Bz_claim,
          comm_Cz_claim,
          comm_prod_Az_Bz_claims,
        ),
        sc_proof_inner,
        pok_claims_inner: (pok_Cz_claim, proof_prod),
        proof_eq_sc_outer,
        proof_eq_sc_inner,
        eval_arg,
      })
  }

  /// verifies a proof of satisfiability of a RelaxedR1CS instance
  fn verify(&self, vk: &Self::VerifierKey, U: &RelaxedR1CSInstance<Bn256EngineZKPedersen>) -> Result<(), NovaError> {
    let mut transcript = <Bn256EngineZKPedersen as Engine>::TE::new(b"RelaxedR1CSSNARK");

    // append the digest of vk (which includes R1CS matrices) and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"vk", &vk.digest());
    transcript.absorb(b"U", U);

    let (num_rounds_x, num_rounds_y) = (
        (vk.S.num_cons as f64).log2() as usize,
        ((vk.S.num_vars as f64).log2() as usize + 1),
    );

    // derive the verifier's challenge tau
    let tau = (0..num_rounds_x)
        .map(|_i| transcript.squeeze(b"t"))
        .collect::<Result<EqPolynomial<_>, NovaError>>()?;

    // outer sum-check
    let claim_outer_comm =
        <Bn256EngineZKPedersen as Engine>::CE::zkcommit(&vk.sumcheck_gens.ck_1, &[<Bn256EngineZKPedersen as Engine>::Scalar::ZERO], &<Bn256EngineZKPedersen as Engine>::Scalar::ZERO).compress();

    let (comm_claim_post_outer, r_x) = self.sc_proof_outer.verify(
        &claim_outer_comm,
        num_rounds_x,
        3,
        &vk.sumcheck_gens.ck_1,
        &vk.sumcheck_gens.ck_4,
        &mut transcript,
    )?;

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) = &self.claims_outer;
    let (pok_Cz_claim, proof_prod) = &self.pok_claims_inner;

    pok_Cz_claim.verify(&vk.sumcheck_gens.ck_1, &mut transcript, comm_Cz_claim)?;

    proof_prod.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        comm_Az_claim,
        comm_Bz_claim,
        comm_prod_Az_Bz_claims,
    )?;

    let comm_eval_E = self.eval_arg.get_eval_commitment(0);
    transcript.absorb(b"comm_eval_E", &comm_eval_E);

    let taus_bound_rx = tau.evaluate(&r_x);
    let comm_expected_claim_post_outer = ((Commitment::<Bn256EngineZKPedersen>::decompress(comm_prod_Az_Bz_claims)?
        - (Commitment::<Bn256EngineZKPedersen>::decompress(comm_Cz_claim)? * U.u
            + Commitment::<Bn256EngineZKPedersen>::decompress(&comm_eval_E)?))
        * taus_bound_rx)
        .compress();

    // verify proof that expected_claim_post_outer == claim_post_outer
    self.proof_eq_sc_outer.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &comm_expected_claim_post_outer,
        &comm_claim_post_outer,
    )?;

    // inner sum-check

    // derive three public challenges and then derive a joint claim
    let r: <Bn256EngineZKPedersen as Engine>::Scalar = transcript.squeeze(b"r")?;

    // comm_Az_claim + r * comm_Bz_claim + r * r * comm_Cz_claim;
    let comm_claim_inner = (Commitment::<Bn256EngineZKPedersen>::decompress(comm_Az_claim)?
        + Commitment::<Bn256EngineZKPedersen>::decompress(comm_Bz_claim)? * r
        + Commitment::<Bn256EngineZKPedersen>::decompress(comm_Cz_claim)? * r * r)
        .compress();

    // verify the joint claim with a sum-check protocol
    let (comm_claim_post_inner, r_y) = self.sc_proof_inner.verify(
        &comm_claim_inner,
        num_rounds_y,
        2,
        &vk.sumcheck_gens.ck_1,
        &vk.sumcheck_gens.ck_3,
        &mut transcript,
    )?;

    let comm_eval_W = self.eval_arg.get_eval_commitment(1);
    transcript.absorb(b"comm_eval_W", &comm_eval_W);

    
    // verify claim_inner_final
    let comm_eval_Z = {
        let eval_X = {
            // constant term
            let mut poly_X = vec![(0, U.u)];
            //remaining inputs
            poly_X.extend(
                (0..U.X.len())
                    .map(|i| (i + 1, U.X[i]))
                    .collect::<Vec<(usize, <Bn256EngineZKPedersen as Engine>::Scalar)>>(),
            );
            SparsePolynomial::new_zk((vk.S.num_vars as f64).log2() as usize, poly_X.iter().map(|(_, x)| *x).collect())
            .evaluate(&r_y[1..])
        };


        Commitment::<Bn256EngineZKPedersen>::decompress(&comm_eval_W)? * (<Bn256EngineZKPedersen as Engine>::Scalar::ONE - r_y[0])
            + <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
                &EE::get_scalar_gen_vk(vk.vk_ee.clone()),
                &[eval_X],
                &<Bn256EngineZKPedersen as Engine>::Scalar::ZERO,
            ) * r_y[0]
    };

    
    // perform the final check in the second sum-check protocol

    let evaluate_as_sparse_polynomial = |S: &R1CSShape<Bn256EngineZKPedersen>,
                                        r_x: &[<Bn256EngineZKPedersen as Engine>::Scalar],
                                        r_y: &[<Bn256EngineZKPedersen as Engine>::Scalar]|
    -> (<Bn256EngineZKPedersen as Engine>::Scalar, <Bn256EngineZKPedersen as Engine>::Scalar, <Bn256EngineZKPedersen as Engine>::Scalar) {
        let evaluate_with_table =
            |M: &SparseMatrix<<Bn256EngineZKPedersen as Engine>::Scalar>, T_x: &[<Bn256EngineZKPedersen as Engine>::Scalar], T_y: &[<Bn256EngineZKPedersen as Engine>::Scalar]| -> <Bn256EngineZKPedersen as Engine>::Scalar {
                M.indptr
                    .par_windows(2)
                    .enumerate()
                    .map(|(row_idx, ptrs)| {
                        M.get_row_unchecked(ptrs.try_into().unwrap())
                            .map(|(val, col_idx)| T_x[row_idx] * T_y[*col_idx] * val)
                            .sum::<<Bn256EngineZKPedersen as Engine>::Scalar>()
                    })
                    .sum()
            };

        let T_x = EqPolynomial::new(r_x.to_vec()).evals();
        let T_y = EqPolynomial::new(r_y.to_vec()).evals();
        let eval_A_r = evaluate_with_table(&S.A, &T_x, &T_y);
        let eval_B_r = evaluate_with_table(&S.B, &T_x, &T_y);
        let eval_C_r = evaluate_with_table(&S.C, &T_x, &T_y);
        (eval_A_r, eval_B_r, eval_C_r)
    };

    let (eval_A_r, eval_B_r, eval_C_r) = evaluate_as_sparse_polynomial(&vk.S, &r_x, &r_y);

    let claim_inner_final_expected =
        (comm_eval_Z * (eval_A_r + r * eval_B_r + r * r * eval_C_r)).compress();

    // verify proof that claim_inner_final_expected == claim_post_inner
    self.proof_eq_sc_inner.verify(
        &vk.sumcheck_gens.ck_1,
        &mut transcript,
        &claim_inner_final_expected,
        &comm_claim_post_inner,
    )?;

    // verify eval_W and eval_E
    EE::verify_batch(
        &vk.vk_ee,
        &mut transcript,
        &[U.comm_E, U.comm_W],
        &[r_x, r_y[1..].to_vec()],
        &self.eval_arg,
    )?;

    Ok(())
  }
}