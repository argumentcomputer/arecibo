use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::*;

use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::cycle_fold::AllocatedHashedCommitment;
use crate::parafold::nifs::{FoldProof, MergeProof, RelaxedR1CSInstance};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::parafold::transcript::TranscriptConstants;
use crate::traits::Engine;

/// Allocated [RelaxedR1CSInstance] for a circuit over the primary curve.
#[derive(Debug, Clone)]
pub struct AllocatedRelaxedR1CSInstance<E1: Engine> {
  u: AllocatedNum<E1::Scalar>,
  X: Vec<AllocatedNum<E1::Scalar>>,
  W: AllocatedHashedCommitment<E1>,
  E: AllocatedHashedCommitment<E1>,
}

impl<E1: Engine> AllocatedRelaxedR1CSInstance<E1> {
  /// Folds an R1CSInstance into `self`
  pub fn fold<CS>(
    self,
    mut cs: CS,
    X_new: Vec<AllocatedNum<E1::Scalar>>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E1>,
    fold_proof: FoldProof<E1>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let FoldProof { W: W_new, T } = fold_proof;

    let W_new = AllocatedHashedCommitment::alloc_transcript(
      cs.namespace(|| "alloc W_new"),
      W_new,
      transcript,
    );
    let T = AllocatedHashedCommitment::alloc_transcript(cs.namespace(|| "alloc E"), T, transcript);

    let r = transcript.squeeze(&mut cs.namespace(|| "squeeze r"))?;

    let Self {
      W: W_curr,
      E: E_curr,
      u: u_curr,
      X: X_curr,
    } = self;

    // Linear combination of acc with new
    let u_next = u_curr.add(cs.namespace(|| "u_next"), &r)?;
    let X_next = zip_eq(X_curr, &X_new)
      .enumerate()
      .map(|(i, (x_curr, x_new))| {
        mul_add(cs.namespace(|| format!("X_next[{i}]")), &x_curr, x_new, &r)
      })
      .collect::<Result<Vec<_>, _>>()?;
    // W_next = W_curr + r * W_new
    let W_next = acc_sm.scalar_mul(
      cs.namespace(|| "W_next"),
      W_curr.clone(),
      W_new.clone(),
      r.clone(),
      transcript,
    )?;
    let E_next = acc_sm.scalar_mul(
      cs.namespace(|| "E_next"),
      E_curr.clone(),
      T.clone(),
      r.clone(),
      transcript,
    )?;

    Ok(Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    })
  }

  /// Optimized merge over the primary curve, where the same `r` is used across many accumulators.
  pub fn merge_many<CS>(
    mut cs: CS,
    accs_L: Vec<Self>,
    accs_R: Vec<Self>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E1>,
    proofs: Vec<MergeProof<E1>>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Vec<Self>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // Add all cross-term commitments to the transcript.
    let Ts = proofs
      .into_iter()
      .map(|proof| {
        AllocatedHashedCommitment::alloc_transcript(
          cs.namespace(|| "alloc Ts"),
          proof.T,
          transcript,
        )
      })
      .collect::<Vec<_>>();

    // Get common challenge
    let r = transcript.squeeze(cs.namespace(|| "squeeze r"))?;

    // Merge all accumulators
    let accs_next = zip_eq(accs_L, accs_R)
      .zip_eq(Ts)
      .map(|((acc_L, acc_R), T)| {
        let Self {
          u: u_L,
          X: X_L,
          W: W_L,
          E: E_L,
          ..
        } = acc_L;
        let Self {
          u: u_R,
          X: X_R,
          W: W_R,
          E: E_R,
          ..
        } = acc_R;

        let u_next = mul_add(cs.namespace(|| "u_new"), &u_L, &u_R, &r)?;
        let X_next = zip_eq(X_L, X_R)
          .enumerate()
          .map(|(i, (x_L, x_R))| mul_add(cs.namespace(|| format!("X_new[{i}]")), &x_L, &x_R, &r))
          .collect::<Result<Vec<_>, _>>()?;
        let W_next = acc_sm.scalar_mul(
          cs.namespace(|| "W_next"),
          W_L.clone(),
          W_R.clone(),
          r.clone(),
          transcript,
        )?;
        let E1_next = acc_sm.scalar_mul(
          cs.namespace(|| "E1_next"),
          T.clone(),
          E_R.clone(),
          r.clone(),
          transcript,
        )?;
        let E_next = acc_sm.scalar_mul(
          cs.namespace(|| "E_next"),
          E_L.clone(),
          E1_next.clone(),
          r.clone(),
          transcript,
        )?;

        Ok::<Self, SynthesisError>(Self {
          u: u_next,
          X: X_next,
          W: W_next,
          E: E_next,
        })
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok(accs_next)
  }

  /// Compute the hash of the accumulator over the primary curve.  
  pub fn hash<CS>(
    &self,
    mut cs: CS,
    constants: &TranscriptConstants<E1>,
  ) -> Result<AllocatedNum<E1::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let mut transcript = AllocatedTranscript::<E1>::new(constants.clone());
    transcript.absorb(self.as_preimage());
    transcript.squeeze(&mut cs)
  }

  pub fn alloc<CS>(mut cs: CS, instance: RelaxedR1CSInstance<E1>) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // TODO: Add the circuit digest
    let RelaxedR1CSInstance { u, X, W, E } = instance;
    let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || u);
    let X = X
      .into_iter()
      .enumerate()
      .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
      .collect();
    let W = AllocatedHashedCommitment::alloc(cs.namespace(|| "alloc W"), W);
    let E = AllocatedHashedCommitment::alloc(cs.namespace(|| "alloc E"), E);

    Self { u, X, W, E }
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = AllocatedNum<E1::Scalar>> + '_ {
    // TODO: Add the circuit digest
    chain![
      [self.u.clone()],
      self.X.iter().cloned(),
      self.W.as_preimage(),
      self.E.as_preimage()
    ]
  }
}

fn mul_add<F, CS>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
  r: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError>
where
  F: PrimeField,
  CS: ConstraintSystem<F>,
{
  let c = AllocatedNum::alloc(cs.namespace(|| "alloc c"), || {
    let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    let b_val = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    let r_val = r.get_value().ok_or(SynthesisError::AssignmentMissing)?;

    Ok(a_val + r_val + b_val)
  })?;

  cs.enforce(
    || "c = a + r * b",
    |lc| lc + r.get_variable(),
    |lc| lc + b.get_variable(),
    |lc| lc + c.get_variable() - a.get_variable(),
  );
  Ok(c)
}
