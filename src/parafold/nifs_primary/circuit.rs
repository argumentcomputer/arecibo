use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::*;

use crate::parafold::cycle_fold::circuit::{
  AllocatedHashedCommitment, AllocatedScalarMulAccumulator, AllocatedScalarMulFoldProof,
};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::Engine;

/// Allocated [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub struct AllocatedRelaxedR1CSInstance<E1: Engine> {
  pub u: AllocatedNum<E1::Scalar>,
  pub X: Vec<AllocatedNum<E1::Scalar>>,
  pub W: AllocatedHashedCommitment<E1>,
  pub E: AllocatedHashedCommitment<E1>,
}

/// An allocated Nova folding proof, for either folding an [R1CSInstance] or a [RelaxedR1CSInstance] into
/// another [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub struct AllocatedFoldProof<E1: Engine, E2: Engine> {
  pub W: AllocatedHashedCommitment<E1>,
  pub T: AllocatedHashedCommitment<E1>,
  pub W_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
  pub E_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
}

#[derive(Debug, Clone)]
pub struct AllocatedMergeProof<E1: Engine, E2: Engine> {
  T: AllocatedHashedCommitment<E1>,
  W_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
  E1_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
  E2_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
}

impl<E1: Engine> AllocatedRelaxedR1CSInstance<E1> {
  /// Folds an R1CSInstance into `self`
  pub fn fold<CS, E2: Engine<Base = E1::Scalar>>(
    self,
    mut cs: CS,
    X_new: Vec<AllocatedNum<E1::Scalar>>,
    acc_sm: AllocatedScalarMulAccumulator<E1, E2>,
    fold_proof: AllocatedFoldProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(Self, AllocatedScalarMulAccumulator<E1, E2>), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let AllocatedFoldProof {
      W: W_new,
      T,
      W_sm_proof,
      E_sm_proof,
    } = fold_proof;

    transcript.absorb(&W_new);
    transcript.absorb(&T);

    let r = transcript.squeeze(cs.namespace(|| "squeeze r"))?;

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
    let (acc_sm, W_next) = acc_sm.scalar_mul(
      cs.namespace(|| "W_next"),
      W_curr.clone(),
      W_new.clone(),
      r.clone(),
      W_sm_proof,
      transcript,
    )?;
    let (acc_sm, E_next) = acc_sm.scalar_mul(
      cs.namespace(|| "E_next"),
      E_curr.clone(),
      T.clone(),
      r.clone(),
      E_sm_proof,
      transcript,
    )?;

    let acc_next = Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    };

    Ok((acc_next, acc_sm))
  }

  pub fn merge_many<CS, E2: Engine<Base = E1::Scalar>>(
    mut cs: CS,
    accs_L: Vec<Self>,
    accs_R: Vec<Self>,
    acc_sm: AllocatedScalarMulAccumulator<E1, E2>,
    merge_proofs: Vec<AllocatedMergeProof<E1, E2>>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(Vec<Self>, AllocatedScalarMulAccumulator<E1, E2>), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let (nifs_proofs, sm_proofs): (Vec<_>, Vec<_>) = merge_proofs
      .into_iter()
      .map(|merge_proof| {
        let AllocatedMergeProof {
          T,
          W_sm_proof,
          E1_sm_proof,
          E2_sm_proof,
        } = merge_proof;
        (T, [W_sm_proof, E1_sm_proof, E2_sm_proof])
      })
      .unzip();

    for nifs_proof in &nifs_proofs {
      transcript.absorb(nifs_proof);
    }

    let r = transcript.squeeze(cs.namespace(|| "squeeze r"))?;

    let mut acc_sm_next = acc_sm;

    let accs_next = zip_eq(accs_L, accs_R)
      .zip_eq(zip_eq(nifs_proofs, sm_proofs))
      .map(|((acc_L, acc_R), (T, sm_proof))| {
        let Self {
          u: u_L,
          X: X_L,
          W: W_L,
          E: E_L,
        } = acc_L;
        let Self {
          u: u_R,
          X: X_R,
          W: W_R,
          E: E_R,
        } = acc_R;
        let acc_sm = acc_sm_next.clone();

        let [W_sm_proof, E1_sm_proof, E2_sm_proof] = sm_proof;

        let u_next = mul_add(cs.namespace(|| "u_new"), &u_L, &u_R, &r)?;
        let X_next = zip_eq(X_L, X_R)
          .enumerate()
          .map(|(i, (x_L, x_R))| mul_add(cs.namespace(|| format!("X_new[{i}]")), &x_L, &x_R, &r))
          .collect::<Result<Vec<_>, _>>()?;
        let (acc_sm, W_next) = acc_sm.scalar_mul(
          cs.namespace(|| "W_next"),
          W_L.clone(),
          W_R.clone(),
          r.clone(),
          W_sm_proof,
          transcript,
        )?;
        let (acc_sm, E1_next) = acc_sm.scalar_mul(
          cs.namespace(|| "E1_next"),
          T.clone(),
          E_R.clone(),
          r.clone(),
          E1_sm_proof,
          transcript,
        )?;
        let (acc_sm, E_next) = acc_sm.scalar_mul(
          cs.namespace(|| "E2_next"),
          E_L.clone(),
          E1_next.clone(),
          r.clone(),
          E2_sm_proof,
          transcript,
        )?;

        acc_sm_next = acc_sm;

        Ok::<Self, SynthesisError>(Self {
          W: W_next,
          E: E_next,
          u: u_next,
          X: X_next,
        })
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok((accs_next, acc_sm_next))
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
