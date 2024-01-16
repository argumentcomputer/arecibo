use std::marker::PhantomData;

use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;

use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::scalar_mul::{
  ScalarMulAccumulatorInstance, ScalarMulFoldProof, ScalarMulMergeProof,
};
use crate::traits::Engine;
use crate::Commitment;

/// TODO:
/// - This will be a non-native hash.
/// - The 0 value will represent the identity
/// - Should store the native value as well
#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulFoldProof<E: Engine> {
  _marker: PhantomData<E>,
  //
}

impl<E: Engine> AllocatedScalarMulFoldProof<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> ScalarMulFoldProof<E>,
  {
    Self {
      _marker: PhantomData::default(),
    }
  }
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulMergeProof<E: Engine> {
  _marker: PhantomData<E>,
  //
}

impl<E: Engine> AllocatedScalarMulMergeProof<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> ScalarMulMergeProof<E>,
  {
    Self {
      _marker: PhantomData::default(),
    }
  }
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulAccumulator<E: Engine> {
  _marker: PhantomData<E>,
  //
}

impl<E: Engine> AllocatedScalarMulAccumulator<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _acc: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> ScalarMulAccumulatorInstance<E>,
  {
    Self {
      _marker: PhantomData::default(),
    }
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
