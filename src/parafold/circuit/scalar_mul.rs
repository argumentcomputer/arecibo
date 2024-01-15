use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;

use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::traits::Engine;
use crate::Commitment;

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

pub struct AllocatedScalarMulInstance<E: Engine> {
  A: AllocatedCommitment<E>,
  B: AllocatedCommitment<E>,
  r: AllocatedNum<E::Scalar>,
  C: AllocatedCommitment<E>,
}

impl<E: Engine> AllocatedScalarMulInstance<E> {
  pub fn new<CS>(
    mut cs: CS,
    A: AllocatedCommitment<E>,
    B: AllocatedCommitment<E>,
    r: AllocatedNum<E::Scalar>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(AllocatedCommitment<E>, Self), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let C_val = {
      let A_val = A.get_value()?;
      let B_val = B.get_value()?;
      let r_val = r.get_value()?;
      A_val + r_val * B_val
    };
    let C = AllocatedCommitment::alloc(cs.namespace(|| "alloc ScalarMulInstance"), || C_val)?;
    transcript.absorb(cs.namespace(|| "absorb C"), &C)?;
    Ok((C.clone(), Self { A, B, r, C }))
  }
}

pub struct AllocatedScalarMulFoldProof<E: Engine> {
  //
}
pub struct AllocatedScalarMulMergeProof<E: Engine> {
  //
}

pub struct AllocatedScalarMulAccumulator<E: Engine> {
  //
}

impl<E: Engine> AllocatedScalarMulAccumulator<E> {
  pub fn fold<CS>(
    self,
    /*mut*/ _cs: CS,
    _instances: impl IntoIterator<Item = AllocatedScalarMulInstance<E>>,
    _proofs: Vec<AllocatedScalarMulFoldProof<E>>,
    _transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // We do not need to re-hash the instances here since the inputs are derived from previously hashed elements,
    // and the outputs are automatically added
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
