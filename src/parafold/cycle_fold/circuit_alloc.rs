use bellpepper_core::ConstraintSystem;

use crate::parafold::cycle_fold::circuit::{
  AllocatedHashedCommitment, AllocatedScalarMulAccumulator, AllocatedScalarMulFoldProof,
  AllocatedScalarMulMergeProof,
};
use crate::parafold::cycle_fold::prover::{
  HashedCommitment, ScalarMulAccumulatorInstance, ScalarMulFoldProof, ScalarMulMergeProof,
};
use crate::traits::Engine;

impl<E1: Engine, E2: Engine> AllocatedScalarMulAccumulator<E1, E2> {
  pub fn alloc_infallible<CS, FA>(/*mut*/ _cs: CS, _acc: FA) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FA: FnOnce() -> ScalarMulAccumulatorInstance<E1, E2>,
  {
    todo!()
  }
}

impl<E1: Engine> AllocatedHashedCommitment<E1> {
  pub fn alloc_infallible<CS, FH>(/*mut*/ _cs: CS, _hashed_commitment: FH) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FH: FnOnce() -> HashedCommitment<E1>,
  {
    todo!()
  }

  // pub fn get_value(&self) -> Option<E::GE> {
  //   todo!()
  // }
}

impl<E1: Engine, E2: Engine> AllocatedScalarMulFoldProof<E1, E2> {
  pub fn alloc_infallible<CS, FF>(/*mut*/ _cs: CS, _proof: FF) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FF: FnOnce() -> ScalarMulFoldProof<E1, E2>,
  {
    todo!()
  }
}

impl<E1: Engine, E2: Engine> AllocatedScalarMulMergeProof<E1, E2> {
  pub fn alloc_infallible<CS, FP>(/*mut*/ _cs: CS, _proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> ScalarMulMergeProof<E1, E2>,
  {
    todo!()
  }
}
