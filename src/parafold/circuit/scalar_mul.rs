use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;

use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::traits::Engine;
use crate::Commitment;
use crate::parafold::prover::cyclefold::{ScalarMulAccumulatorInstance, ScalarMulFoldProof, ScalarMulMergeProof};

/// TODO:
/// - This will be a non-native hash.
/// - The 0 value will represent the identity
/// - Should store the native value as well
#[derive(Clone)]
pub struct AllocatedCommitment<E: Engine> {
  x: AllocatedNum<E::Scalar>,
  y: AllocatedNum<E::Scalar>,
}

impl<E: Engine> AllocatedCommitment<E> {
  pub(crate) fn get_value(&self) -> Option<E::GE> {
    todo!()
  }
}

impl<E: Engine> AllocatedCommitment<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, _commitment: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> Commitment<E>,
  {
    let x = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc x"), || E::Scalar::ZERO);
    let y = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc y"), || E::Scalar::ZERO);
    Self { x, y }
  }
}

pub struct AllocatedScalarMulFoldProof<E: Engine> {
  //
}

impl<E: Engine> AllocatedScalarMulFoldProof<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _proof: F) -> Self
    where
        CS: ConstraintSystem<E::Scalar>,
        F: FnOnce() -> ScalarMulFoldProof<E>,
  {
    Self{}
  }
}

pub struct AllocatedScalarMulMergeProof<E: Engine> {
  //
}

impl<E: Engine> AllocatedScalarMulMergeProof<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _proof: F) -> Self
    where
        CS: ConstraintSystem<E::Scalar>,
        F: FnOnce() -> ScalarMulMergeProof<E>,
  {
    Self{}
  }
}

pub struct AllocatedScalarMulAccumulator<E: Engine> {
  //
}

impl<E: Engine> AllocatedScalarMulAccumulator<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _acc: F) -> Self
    where
        CS: ConstraintSystem<E::Scalar>,
        F: FnOnce() -> ScalarMulAccumulatorInstance<E>,
  {
    Self{}
  }
  
  pub fn scalar_mul<CS>(
    &mut self,
    /*mut*/ _cs: CS,
    _A: AllocatedCommitment<E>,
    _B: AllocatedCommitment<E>,
    _r: AllocatedNum<E::Scalar>,
    _proof: AllocatedScalarMulFoldProof<E>,
    _transcript: &mut AllocatedTranscript<E>,
  ) -> Result<AllocatedCommitment<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    todo!()
  }

  pub fn merge<CS>(
    self,
    /*mut*/ _cs: CS,
    _other: Self,
    _proof: AllocatedScalarMulMergeProof<E>,
    _transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    todo!()
  }
}
