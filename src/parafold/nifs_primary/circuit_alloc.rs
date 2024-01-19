use crate::parafold::cycle_fold::circuit::{
  AllocatedHashedCommitment, AllocatedScalarMulFoldProof,
};
use crate::parafold::nifs_primary::circuit::{AllocatedFoldProof, AllocatedRelaxedR1CSInstance};
use crate::parafold::nifs_primary::prover::{FoldProof, RelaxedR1CSInstance};
use crate::traits::Engine;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::ConstraintSystem;

impl<E1: Engine, E2: Engine> AllocatedFoldProof<E1, E2> {
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
}
