use std::marker::PhantomData;

use crate::traits::Engine;
use crate::Commitment;

/// A proof for a non-native group operation C = A + x * B, where x is a native scalar
/// and A, B, C, are non-native group elements
///
#[derive(Debug, Clone)]
pub struct ScalarMulFoldProof<E: Engine> {
  // witness W
  // fold proof T
  _marker: PhantomData<E>,
}

#[derive(Debug, Clone)]
pub struct ScalarMulMergeProof<E: Engine> {
  // fold proof T
  _marker: PhantomData<E>,
}

#[derive(Debug)]
pub struct ScalarMulAccumulator<E: Engine> {
  // instance ScalarMulAccumulatorInstance
  // W: Vec<E::Base>
  // E: Vec<E::Base>
  _marker: PhantomData<E>,
}

impl<E: Engine> ScalarMulAccumulator<E> {
  ///
  pub fn scalar_mul(
    &mut self,
    _A: Commitment<E>,
    _B: Commitment<E>,
    _x: E::Scalar,
    _transcript: &mut E::TE,
  ) -> (Commitment<E>, ScalarMulFoldProof<E>) {
    // Compute C = A + x * B
    // Compute W proof of this operation
    // compute H(C) as the circuit representation of C, where H is Poseidon on the secondary curve
    // Add C,W to the transcript
    // Set X = [H(A), H(B), X, H(C)] and fold into self
    // return proof
    todo!()
  }

  /// Compute
  pub fn merge(self, _other: Self, _transcript: &mut E::TE) -> (Self, ScalarMulMergeProof<E>) {
    // self and other will not need to be added to the transcript since they are obtained from an accumulator
    // we need to compute the T cross term vector
    // add T to transcript
    // return linear combination of both accumulators
    todo!()
  }

  /// Return the succinct instance of the accumulator
  pub(crate) fn instance(&self) -> ScalarMulAccumulatorInstance<E> {
    todo!()
  }
}

#[derive(Debug, Clone)]
pub struct ScalarMulAccumulatorInstance<E: Engine> {
  _marker: PhantomData<E>,
  // u
  // X
  // W_comm
  // E_comm
}
