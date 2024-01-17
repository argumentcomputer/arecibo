use crate::parafold::cycle_fold::circuit::{
  AllocatedGroupElement, AllocatedScalarMulAccumulator, AllocatedScalarMulFoldProof,
};
use crate::parafold::nifs_primary::prover::{FoldProof, RelaxedR1CSInstance};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::Engine;
use crate::zip_with;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::*;

/// Allocated [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub struct AllocatedRelaxedR1CSInstance<E: Engine> {
  u: AllocatedNum<E::Scalar>,
  X: Vec<AllocatedNum<E::Scalar>>,
  W: AllocatedGroupElement<E>,
  E: AllocatedGroupElement<E>,
}

/// An allocated Nova folding proof, for either folding an [R1CSInstance] or a [RelaxedR1CSInstance] into
/// another [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub struct AllocatedFoldProof<E: Engine> {
  W: AllocatedGroupElement<E>,
  T: AllocatedGroupElement<E>,
  W_sm_proof: AllocatedScalarMulFoldProof<E>,
  E_sm_proof: AllocatedScalarMulFoldProof<E>,
}

#[derive(Debug, Clone)]
pub struct AllocatedMergeProof<E: Engine> {
  T: AllocatedGroupElement<E>,
  W_sm_proof: AllocatedScalarMulFoldProof<E>,
  E1_sm_proof: AllocatedScalarMulFoldProof<E>,
  E2_sm_proof: AllocatedScalarMulFoldProof<E>,
}

impl<E: Engine> AllocatedFoldProof<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, fold_proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> FoldProof<E>,
  {
    let FoldProof {
      W,
      T,
      W_sm_proof,
      E_sm_proof,
    } = fold_proof();
    let W = AllocatedGroupElement::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let T = AllocatedGroupElement::alloc_infallible(cs.namespace(|| "alloc T"), || T);
    let W_sm_proof =
      AllocatedScalarMulFoldProof::alloc_infallible(cs.namespace(|| "alloc W_sm_proof"), || {
        W_sm_proof
      });
    let E_sm_proof =
      AllocatedScalarMulFoldProof::alloc_infallible(cs.namespace(|| "alloc E_sm_proof"), || {
        E_sm_proof
      });
    Self {
      W,
      T,
      W_sm_proof,
      E_sm_proof,
    }
  }
}

impl<E: Engine> AllocatedRelaxedR1CSInstance<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, instance: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> RelaxedR1CSInstance<E>,
  {
    let RelaxedR1CSInstance { u, X, W, E } = instance();
    let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || u);
    let X = X
      .into_iter()
      .enumerate()
      .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
      .collect();
    let W = AllocatedGroupElement::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let E = AllocatedGroupElement::alloc_infallible(cs.namespace(|| "alloc E"), || E);

    Self { u, X, W, E }
  }

  /// Folds an R1CSInstance into `self`
  pub fn fold<CS>(
    self,
    mut cs: CS,
    X_new: Vec<AllocatedNum<E::Scalar>>,
    mut acc_sm: AllocatedScalarMulAccumulator<E>,
    fold_proof: AllocatedFoldProof<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Self, AllocatedScalarMulAccumulator<E>), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let AllocatedFoldProof {
      W: W_new,
      T,
      W_sm_proof,
      E_sm_proof,
    } = fold_proof;

    transcript.absorb(cs.namespace(|| "absorb W_new"), &W_new)?;
    transcript.absorb(cs.namespace(|| "absorb T"), &T)?;

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

    let acc_next = Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    };

    Ok((acc_next, acc_sm))
  }

  pub fn merge_many<CS>(
    mut cs: CS,
    accs_L: Vec<Self>,
    accs_R: Vec<Self>,
    mut acc_sm: AllocatedScalarMulAccumulator<E>,
    merge_proofs: Vec<AllocatedMergeProof<E>>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Vec<Self>, AllocatedScalarMulAccumulator<E>), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
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

    for (i, nifs_proof) in nifs_proofs.iter().enumerate() {
      transcript.absorb(
        cs.namespace(|| format!("absorb nifs_proof[{i}]")),
        nifs_proof,
      )?;
    }

    let r = transcript.squeeze(cs.namespace(|| "squeeze r"))?;

    let accs_next = zip_with!(
      (
        accs_L.into_iter(),
        accs_R.into_iter(),
        nifs_proofs.into_iter(),
        sm_proofs.into_iter()
      ),
      |acc_L, acc_R, T, sm_proof| {
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
      }
    )
    .collect::<Result<Vec<_>, _>>()?;

    Ok((accs_next, acc_sm))
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
