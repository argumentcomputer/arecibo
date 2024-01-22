use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::cycle_fold::{AllocatedHashedCommitment, AllocatedScalarMulFoldProof};
use crate::parafold::nifs_primary::{
  AllocatedFoldProof, AllocatedMergeProof, AllocatedRelaxedR1CSInstance,
};
use crate::parafold::nifs_primary::{FoldProof, MergeProof, RelaxedR1CSInstance};
use crate::traits::Engine;

impl<E1: Engine> AllocatedRelaxedR1CSInstance<E1> {
  pub fn alloc_infallible<CS, FI>(mut cs: CS, instance: FI) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FI: FnOnce() -> RelaxedR1CSInstance<E1>,
  {
    let RelaxedR1CSInstance { u, X, W, E } = instance();
    let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || u);
    let X = X
      .into_iter()
      .enumerate()
      .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
      .collect();
    let W = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let E = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc E"), || E);

    Self { u, X, W, E }
  }

  pub fn to_native(&self) -> Result<RelaxedR1CSInstance<E1>, SynthesisError> {
    let u = self
      .u
      .get_value()
      .ok_or(SynthesisError::AssignmentMissing)?;
    let X = self
      .X
      .iter()
      .map(|x| x.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;
    let W = self.W.to_native()?;
    let E = self.E.to_native()?;

    Ok(RelaxedR1CSInstance { u, X, W, E })
  }
}

impl<E1, E2> AllocatedFoldProof<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FP>(mut cs: CS, fold_proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> FoldProof<E1, E2>,
  {
    let FoldProof {
      W,
      T,
      W_sm_proof,
      E_sm_proof,
    } = fold_proof();
    let W = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let T = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc T"), || T);
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

impl<E1, E2> AllocatedMergeProof<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FP>(mut cs: CS, merge_proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> MergeProof<E1, E2>,
  {
    let MergeProof {
      T,
      W_sm_proof,
      E1_sm_proof,
      E2_sm_proof,
    } = merge_proof();
    let T = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc T"), || T);
    let W_sm_proof =
      AllocatedScalarMulFoldProof::alloc_infallible(cs.namespace(|| "alloc W_sm_proof"), || {
        W_sm_proof
      });
    let E1_sm_proof =
      AllocatedScalarMulFoldProof::alloc_infallible(cs.namespace(|| "alloc E1_sm_proof"), || {
        E1_sm_proof
      });
    let E2_sm_proof =
      AllocatedScalarMulFoldProof::alloc_infallible(cs.namespace(|| "alloc E2_sm_proof"), || {
        E2_sm_proof
      });
    Self {
      T,
      W_sm_proof,
      E1_sm_proof,
      E2_sm_proof,
    }
  }
}
