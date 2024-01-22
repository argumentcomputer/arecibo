use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::*;

use crate::parafold::cycle_fold::AllocatedScalarMulAccumulator;
use crate::parafold::nifs_primary::{
  AllocatedFoldProof, AllocatedMergeProof, AllocatedRelaxedR1CSInstance,
};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::Engine;

impl<E1: Engine> AllocatedRelaxedR1CSInstance<E1> {
  /// Folds an R1CSInstance into `self`
  pub fn fold<CS, E2: Engine<Base = E1::Scalar>>(
    &mut self,
    mut cs: CS,
    X_new: Vec<AllocatedNum<E1::Scalar>>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E1, E2>,
    fold_proof: AllocatedFoldProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(), SynthesisError>
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
    let W_next = acc_sm.scalar_mul(
      cs.namespace(|| "W_next"),
      W_curr.clone(),
      W_new.clone(),
      r.clone(),
      W_sm_proof,
      transcript,
    )?;
    let E_next = acc_sm.scalar_mul(
      cs.namespace(|| "E_next"),
      E_curr.clone(),
      T.clone(),
      r.clone(),
      E_sm_proof,
      transcript,
    )?;

    *self = Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    };

    Ok(())
  }

  pub fn merge_many<CS, E2: Engine<Base = E1::Scalar>>(
    mut cs: CS,
    accs_L: Vec<Self>,
    accs_R: Vec<Self>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E1, E2>,
    merge_proofs: Vec<AllocatedMergeProof<E1, E2>>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Vec<Self>, SynthesisError>
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

        let [W_sm_proof, E1_sm_proof, E2_sm_proof] = sm_proof;

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
          W_sm_proof,
          transcript,
        )?;
        let E1_next = acc_sm.scalar_mul(
          cs.namespace(|| "E1_next"),
          T.clone(),
          E_R.clone(),
          r.clone(),
          E1_sm_proof,
          transcript,
        )?;
        let E_next = acc_sm.scalar_mul(
          cs.namespace(|| "E2_next"),
          E_L.clone(),
          E1_next.clone(),
          r.clone(),
          E2_sm_proof,
          transcript,
        )?;

        Ok::<Self, SynthesisError>(Self {
          W: W_next,
          E: E_next,
          u: u_next,
          X: X_next,
        })
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok(accs_next)
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
