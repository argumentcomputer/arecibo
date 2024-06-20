#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use super::nizk::DotProductProof;
use crate::errors::NovaError;
use crate::spartan::polys::{multilinear::MultilinearPolynomial, univariate::UniPoly};
use crate::traits::{
  commitment::{ZKCommitmentEngineTrait, CommitmentTrait, Len},
  TranscriptEngineTrait,
};
use crate::{Commitment, CommitmentKey, CompressedCommitment, provider::Bn256EngineZKPedersen};
use ff::Field;
use rand::rngs::OsRng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use crate::Engine;

pub(in crate::spartan) mod engine;

#[derive(Serialize, Deserialize, Debug)]
pub(crate) struct ZKSumcheckProof {
  comm_polys: Vec<CompressedCommitment<Bn256EngineZKPedersen>>,
  comm_evals: Vec<CompressedCommitment<Bn256EngineZKPedersen>>,
  proofs: Vec<DotProductProof>,
}

impl ZKSumcheckProof {
  #[allow(dead_code)]
  pub fn new(
    comm_polys: Vec<CompressedCommitment<Bn256EngineZKPedersen>>,
    comm_evals: Vec<CompressedCommitment<Bn256EngineZKPedersen>>,
    proofs: Vec<DotProductProof>,
  ) -> Self {
    Self {
      comm_polys,
      comm_evals,
      proofs,
    }
  }

  #[allow(dead_code)]
  pub fn verify(
    &self,
    comm_claim: &CompressedCommitment<Bn256EngineZKPedersen>,
    num_rounds: usize,
    degree_bound: usize,
    ck_1: &CommitmentKey<Bn256EngineZKPedersen>, // generator of size 1
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>, // generators of size n
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
  ) -> Result<(CompressedCommitment<Bn256EngineZKPedersen>, Vec<<Bn256EngineZKPedersen as Engine>::Scalar>), NovaError> {
    // verify degree bound
    if ck_n.length() != degree_bound + 1 {
      return Err(NovaError::InvalidSumcheckProof);
    }

    // verify that there is a univariate polynomial for each round
    if self.comm_polys.len() != num_rounds || self.comm_evals.len() != num_rounds {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let mut r = Vec::new();

    for i in 0..self.comm_polys.len() {
      let comm_poly = &self.comm_polys[i];

      // append the prover's polynomial to the transcript
      transcript.absorb(b"comm_poly", comm_poly);

      //derive the verifier's challenge for the next round
      let r_i = transcript.squeeze(b"challenge_nextround")?;

      // verify the proof of sum-check and evals

      let res = {
        let comm_claim_per_round = if i == 0 {
          comm_claim
        } else {
          &self.comm_evals[i - 1]
        };

        let comm_eval = &self.comm_evals[i];

        // add two claims to transcript
        transcript.absorb(b"comm_claim_per_round", comm_claim_per_round);
        transcript.absorb(b"comm_eval", comm_eval);

        // produce two weights
        let w0 = transcript.squeeze(b"combine_two_claims_to_one_0")?;
        let w1 = transcript.squeeze(b"combine_two_claims_to_one_1")?;

        let decompressed_comm_claim_per_round = Commitment::<Bn256EngineZKPedersen>::decompress(comm_claim_per_round)?;
        let decompressed_comm_eval = Commitment::<Bn256EngineZKPedersen>::decompress(comm_eval)?;

        // compute a weighted sum of the RHS
        let comm_target = decompressed_comm_claim_per_round * w0 + decompressed_comm_eval * w1;
        let compressed_comm_target = comm_target.compress();

        let a = {
          // the vector to use for decommit for sum-check test
          let a_sc = {
            let mut a = vec![<Bn256EngineZKPedersen as Engine>::Scalar::ONE; degree_bound + 1];
            a[0] += <Bn256EngineZKPedersen as Engine>::Scalar::ONE;
            a
          };

          // the vector to use to decommit for evaluation
          let a_eval = {
            let mut a = vec![<Bn256EngineZKPedersen as Engine>::Scalar::ONE; degree_bound + 1];
            for j in 1..a.len() {
              a[j] = a[j - 1] * r_i;
            }
            a
          };

          // take weighted sum of the two vectors using w
          assert_eq!(a_sc.len(), a_eval.len());
          (0..a_sc.len())
            .map(|i| w0 * a_sc[i] + w1 * a_eval[i])
            .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>()
        };

        self.proofs[i]
          .verify(
            ck_1,
            ck_n,
            transcript,
            &a,
            &self.comm_polys[i],
            &compressed_comm_target,
          )
          .is_ok()
      };

      if !res {
        return Err(NovaError::InvalidSumcheckProof);
      }

      r.push(r_i);
    }

    Ok((self.comm_evals[self.comm_evals.len() - 1].clone(), r))
  }

  #[allow(dead_code)]
  pub fn prove_quad<F>(
    claim: &<Bn256EngineZKPedersen as Engine>::Scalar,
    blind_claim: &<Bn256EngineZKPedersen as Engine>::Scalar,
    num_rounds: usize,
    poly_A: &mut MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_B: &mut MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    comb_func: F,
    ck_1: &CommitmentKey<Bn256EngineZKPedersen>, // generator of size 1
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>, // generators of size n
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
) -> Result<(ZKSumcheckProof, Vec<<Bn256EngineZKPedersen as Engine>::Scalar>, Vec<<Bn256EngineZKPedersen as Engine>::Scalar>, <Bn256EngineZKPedersen as Engine>::Scalar), NovaError>
where
    F: Fn(&<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar) -> <Bn256EngineZKPedersen as Engine>::Scalar,
{
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

    let mut claim_per_round = *claim;
    let mut comm_claim_per_round =
        <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[claim_per_round], blind_claim).compress();

    let mut r = Vec::new();
    let mut comm_polys = Vec::new();
    let mut comm_evals = Vec::new();
    let mut proofs = Vec::new();

    for j in 0..num_rounds {
      let (poly, comm_poly) = {
          let mut eval_point_0 = <Bn256EngineZKPedersen as Engine>::Scalar::ZERO;
          let mut eval_point_2 = <Bn256EngineZKPedersen as Engine>::Scalar::ZERO;

          let len = poly_A.len() / 2;
          for i in 0..len {
              // eval 0: bound_func is A(low)
              eval_point_0 += comb_func(&poly_A[i], &poly_B[i]);

              // eval 2: bound_func is -A(low) + 2*A(high)
              let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
              let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
              eval_point_2 += comb_func(&poly_A_bound_point, &poly_B_bound_point);
          }

          let evals = vec![eval_point_0, claim_per_round - eval_point_0, eval_point_2];
          let poly = UniPoly::from_evals(&evals);
          let comm_poly = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &poly.coeffs, &blinds_poly[j]).compress();
          (poly, comm_poly)
      };

      // append the prover's message to the transcript
      transcript.absorb(b"comm_poly", &comm_poly);
      comm_polys.push(comm_poly);

      // derive the verifier's challenge for the next round
      let r_j = transcript.squeeze(b"challenge_nextround")?;

      // bound all tables to the verifier's challenge
      poly_A.bind_poly_var_top(&r_j);
      poly_B.bind_poly_var_top(&r_j);

      // produce a proof of sum-check an of evaluation
      let (proof, claim_next_round, comm_claim_next_round) = {
          let eval = poly.evaluate(&r_j);
          let comm_eval = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[eval], &blinds_evals[j]).compress();

          // we need to prove the following under homomorphic commitments:
          // (1) poly(0) + poly(1) = claim_per_round
          // (2) poly(r_j) = eval

          // Our technique is to leverage dot product proofs:
          // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
          // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
          // for efficiency we batch them using random weights

          // add two claims to transcript
          transcript.absorb(b"comm_claim_per_round", &comm_claim_per_round);
          transcript.absorb(b"comm_eval", &comm_eval);

          // produce two weights
          let w0 = transcript.squeeze(b"combine_two_claims_to_one_0")?;
          let w1 = transcript.squeeze(b"combine_two_claims_to_one_1")?;

          // compute a weighted sum of the RHS
          let target = w0 * claim_per_round + w1 * eval;
          let decompressed_comm_claim_per_round = Commitment::<Bn256EngineZKPedersen>::decompress(&comm_claim_per_round)?;
          let decompressed_comm_eval = Commitment::<Bn256EngineZKPedersen>::decompress(&comm_eval)?;

          let comm_target =
              (decompressed_comm_claim_per_round * w0 + decompressed_comm_eval * w1).compress();

          let blind = {
              let blind_sc = if j == 0 {
                  blind_claim
              } else {
                  &blinds_evals[j - 1]
              };

              let blind_eval = &blinds_evals[j];

              w0 * blind_sc + w1 * blind_eval
          };

          assert_eq!(
              <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[target], &blind).compress(),
              comm_target
          );

          let a = {
              // the vector to use to decommit for sum-check test
              let a_sc = {
                  let mut a = vec![<Bn256EngineZKPedersen as Engine>::Scalar::ONE; poly.degree() + 1];
                  a[0] += <Bn256EngineZKPedersen as Engine>::Scalar::ONE;
                  a
              };

              // the vector to use to decommit for evaluation
              let a_eval = {
                  let mut a = vec![<Bn256EngineZKPedersen as Engine>::Scalar::ONE; poly.degree() + 1];
                  for j in 1..a.len() {
                      a[j] = a[j - 1] * r_j;
                  }
                  a
              };

              // take a weighted sum of the two vectors using w
              assert_eq!(a_sc.len(), a_eval.len());
              (0..a_sc.len())
                  .map(|i| w0 * a_sc[i] + w1 * a_eval[i])
                  .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>()
          };

          let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
              ck_1,
              ck_n,
              transcript,
              &poly.coeffs,
              &blinds_poly[j],
              &a,
              &target,
              &blind,
          )?;

          (proof, eval, comm_eval)
      };

      claim_per_round = claim_next_round;
      comm_claim_per_round = comm_claim_next_round;

      proofs.push(proof);
      r.push(r_j);
      comm_evals.push(comm_claim_per_round.clone());
    }

    Ok((
        ZKSumcheckProof::new(comm_polys, comm_evals, proofs),
        r,
        vec![poly_A[0], poly_B[0]],
        blinds_evals[num_rounds - 1],
    ))
  }

  #[allow(dead_code)]
  #[inline]
  fn compute_eval_points_cubic<F>(
    poly_A: &MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_B: &MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_C: &MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    comb_func: &F,
  ) -> (<Bn256EngineZKPedersen as Engine>::Scalar, <Bn256EngineZKPedersen as Engine>::Scalar, <Bn256EngineZKPedersen as Engine>::Scalar)
  where
    F: Fn(&<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar) -> <Bn256EngineZKPedersen as Engine>::Scalar + Sync,
  {
    let len = poly_A.len() / 2;
    (0..len)
      .into_par_iter()
      .map(|i| {
        // eval 0: bound_func is A(low)
        let eval_point_0 = comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);

        let poly_A_right_term = poly_A[len + i] - poly_A[i];
        let poly_B_right_term = poly_B[len + i] - poly_B[i];
        let poly_C_right_term = poly_C[len + i] - poly_C[i];

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = poly_A[len + i] + poly_A_right_term;
        let poly_B_bound_point = poly_B[len + i] + poly_B_right_term;
        let poly_C_bound_point = poly_C[len + i] + poly_C_right_term;
        let eval_point_2 = comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = poly_A_bound_point + poly_A_right_term;
        let poly_B_bound_point = poly_B_bound_point + poly_B_right_term;
        let poly_C_bound_point = poly_C_bound_point + poly_C_right_term;
        let eval_point_3 = comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );
        (eval_point_0, eval_point_2, eval_point_3)
      })
      .reduce(
        || (<Bn256EngineZKPedersen as Engine>::Scalar::ZERO, <Bn256EngineZKPedersen as Engine>::Scalar::ZERO, <Bn256EngineZKPedersen as Engine>::Scalar::ZERO),
        |a, b| (a.0 + b.0, a.1 + b.1, a.2 + b.2),
      )
  }

  #[allow(dead_code)]
  #[inline]
  fn compute_eval_points_cubic_with_additive_term<F>(
    poly_A: &MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_B: &MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_C: &MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_D: &MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    comb_func: &F,
  ) -> (<Bn256EngineZKPedersen as Engine>::Scalar, <Bn256EngineZKPedersen as Engine>::Scalar, <Bn256EngineZKPedersen as Engine>::Scalar)
  where
    F: Fn(&<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar) -> <Bn256EngineZKPedersen as Engine>::Scalar + Sync,
  {
    let len = poly_A.len() / 2;
    (0..len)
      .into_par_iter()
      .map(|i| {
        // eval 0: bound_func is A(low)
        let eval_point_0 = comb_func(&poly_A[i], &poly_B[i], &poly_C[i], &poly_D[i]);

        let poly_A_right_term = poly_A[len + i] - poly_A[i];
        let poly_B_right_term = poly_B[len + i] - poly_B[i];
        let poly_C_right_term = poly_C[len + i] - poly_C[i];
        let poly_D_right_term = poly_D[len + i] - poly_D[i];

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = poly_A[len + i] + poly_A_right_term;
        let poly_B_bound_point = poly_B[len + i] + poly_B_right_term;
        let poly_C_bound_point = poly_C[len + i] + poly_C_right_term;
        let poly_D_bound_point = poly_D[len + i] + poly_D_right_term;
        let eval_point_2 = comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
          &poly_D_bound_point,
        );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = poly_A_bound_point + poly_A_right_term;
        let poly_B_bound_point = poly_B_bound_point + poly_B_right_term;
        let poly_C_bound_point = poly_C_bound_point + poly_C_right_term;
        let poly_D_bound_point = poly_D_bound_point + poly_D_right_term;
        let eval_point_3 = comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
          &poly_D_bound_point,
        );
        (eval_point_0, eval_point_2, eval_point_3)
      })
      .reduce(
        || (<Bn256EngineZKPedersen as Engine>::Scalar::ZERO, <Bn256EngineZKPedersen as Engine>::Scalar::ZERO, <Bn256EngineZKPedersen as Engine>::Scalar::ZERO),
        |a, b| (a.0 + b.0, a.1 + b.1, a.2 + b.2),
      )
  }

  #[allow(dead_code)]
  pub fn prove_cubic_with_additive_term<F>(
    claim: &<Bn256EngineZKPedersen as Engine>::Scalar,
    blind_claim: &<Bn256EngineZKPedersen as Engine>::Scalar,
    num_rounds: usize,
    poly_A: &mut MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_B: &mut MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_C: &mut MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    poly_D: &mut MultilinearPolynomial<<Bn256EngineZKPedersen as Engine>::Scalar>,
    comb_func: F,
    ck_1: &CommitmentKey<Bn256EngineZKPedersen>, // generator of size 1
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>, // generators of size n
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
  ) -> Result<(ZKSumcheckProof, Vec<<Bn256EngineZKPedersen as Engine>::Scalar>, Vec<<Bn256EngineZKPedersen as Engine>::Scalar>, <Bn256EngineZKPedersen as Engine>::Scalar), NovaError>
  where
      F: Fn(&<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar, &<Bn256EngineZKPedersen as Engine>::Scalar) -> <Bn256EngineZKPedersen as Engine>::Scalar,
  {
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

    let mut claim_per_round = *claim;
    let mut comm_claim_per_round =
        <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[claim_per_round], blind_claim).compress();

    let mut r = Vec::new();
    let mut comm_polys = Vec::new();
    let mut comm_evals = Vec::new();
    let mut proofs = Vec::new();

    for j in 0..num_rounds {
        let (poly, comm_poly) = {
            let mut eval_point_0 = <Bn256EngineZKPedersen as Engine>::Scalar::ZERO;
            let mut eval_point_2 = <Bn256EngineZKPedersen as Engine>::Scalar::ZERO;
            let mut eval_point_3 = <Bn256EngineZKPedersen as Engine>::Scalar::ZERO;

            let len = poly_A.len() / 2;

            for i in 0..len {
                // eval 0: bound_func is A(low)
                eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i], &poly_D[i]);

                // eval 2: bound_func is -A(low) + 2*A(high)
                let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
                let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
                let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
                let poly_D_bound_point = poly_D[len + i] + poly_D[len + i] - poly_D[i];

                eval_point_2 += comb_func(
                    &poly_A_bound_point,
                    &poly_B_bound_point,
                    &poly_C_bound_point,
                    &poly_D_bound_point,
                );

                // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func
                // applied to eval(2)
                let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
                let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
                let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];
                let poly_D_bound_point = poly_D_bound_point + poly_D[len + i] - poly_D[i];

                eval_point_3 += comb_func(
                    &poly_A_bound_point,
                    &poly_B_bound_point,
                    &poly_C_bound_point,
                    &poly_D_bound_point,
                );
            }

            let evals = vec![
                eval_point_0,
                claim_per_round - eval_point_0,
                eval_point_2,
                eval_point_3,
            ];

            let poly = UniPoly::from_evals(&evals);
            let comm_poly = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &poly.coeffs, &blinds_poly[j]).compress();
            (poly, comm_poly)
        };

        // append the prover's message to the transcript
        transcript.absorb(b"comm_poly", &comm_poly);
        comm_polys.push(comm_poly);

        // derive the verifier's challenge for the next round
        let r_j = transcript.squeeze(b"challenge_nextround")?;

        // bound all tables to the verifier's challenge
        poly_A.bind_poly_var_top(&r_j);
        poly_B.bind_poly_var_top(&r_j);
        poly_C.bind_poly_var_top(&r_j);
        poly_D.bind_poly_var_top(&r_j);

        // produce a proof of sum-check and of evaluation
        let (proof, claim_next_round, comm_claim_next_round) = {
          let eval = poly.evaluate(&r_j);
          let comm_eval = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[eval], &blinds_evals[j]).compress();

          // we need to prove the following under homomorphic commitments:
          // (1) poly(0) + poly(1) = claim_per_round
          // (2) poly(r_j) = eval

          // Our technique is to leverage dot product proofs:
          // (1) we can prove: <poly_in_coeffs_form, (2, 1, 1, 1)> = claim_per_round
          // (2) we can prove: <poly_in_coeffs_form, (1, r_j, r^2_j, ..) = eval
          // for efficiency we batch them using random weights

          // add two claims to transcript
          transcript.absorb(b"comm_claim_per_round", &comm_claim_per_round);
          transcript.absorb(b"comm_eval", &comm_eval);

          // produce two weights
          let w0 = transcript.squeeze(b"combine_two_claims_to_one_0")?;
          let w1 = transcript.squeeze(b"combine_two_claims_to_one_1")?;

          let decompressed_comm_claim_per_round = Commitment::<Bn256EngineZKPedersen>::decompress(&comm_claim_per_round)?;
          let decompressed_comm_eval = Commitment::<Bn256EngineZKPedersen>::decompress(&comm_eval)?;

          // compute a weighted sum of the RHS
          let target = claim_per_round * w0 + eval * w1;
          let comm_target =
              (decompressed_comm_claim_per_round * w0 + decompressed_comm_eval * w1).compress();

          let blind = {
              let blind_sc = if j == 0 {
                  blind_claim
              } else {
                  &blinds_evals[j - 1]
              };

              let blind_eval = &blinds_evals[j];

              w0 * blind_sc + w1 * blind_eval
          };

          assert_eq!(
              <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[target], &blind).compress(),
              comm_target
          );

          let a = {
              // the vector to use to decommit for sum-check test
              let a_sc = {
                  let mut a = vec![<Bn256EngineZKPedersen as Engine>::Scalar::ONE; poly.degree() + 1];
                  a[0] += <Bn256EngineZKPedersen as Engine>::Scalar::ONE;
                  a
              };

              // the vector to use to decommit for evaluation
              let a_eval = {
                  let mut a = vec![<Bn256EngineZKPedersen as Engine>::Scalar::ONE; poly.degree() + 1];
                  for j in 1..a.len() {
                      a[j] = a[j - 1] * r_j;
                  }
                  a
              };

              // take weighted sum of the two vectors using w
              assert_eq!(a_sc.len(), a_eval.len());

              (0..a_sc.len())
                  .map(|i| w0 * a_sc[i] + w1 * a_eval[i])
                  .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>()
          };

          let (proof, _comm_poly, _comm_sc_eval) = DotProductProof::prove(
              ck_1,
              ck_n,
              transcript,
              &poly.coeffs,
              &blinds_poly[j],
              &a,
              &target,
              &blind,
          )?;

          (proof, eval, comm_eval)
        };

        proofs.push(proof);
        claim_per_round = claim_next_round;
        comm_claim_per_round = comm_claim_next_round;
        r.push(r_j);
        comm_evals.push(comm_claim_per_round.clone());
    }

    Ok((
        ZKSumcheckProof::new(comm_polys, comm_evals, proofs),
        r,
        vec![poly_A[0], poly_B[0], poly_C[0], poly_D[0]],
        blinds_evals[num_rounds - 1],
    ))
  }
}