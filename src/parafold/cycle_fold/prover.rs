use crate::parafold::cycle_fold::{
  HashedCommitment, ScalarMulAccumulatorInstance, ScalarMulFoldProof, ScalarMulMergeProof,
};
use crate::parafold::transcript::prover::Transcript;
use crate::traits::Engine;

#[derive(Debug)]
pub struct ScalarMulAccumulator<E2: Engine> {
  // ro consts secondary?
  // used to hash the incoming point
  instance: ScalarMulAccumulatorInstance<E2>,
  W: Vec<E2::Scalar>,
  E: Vec<E2::Scalar>,
}

impl<E2: Engine> ScalarMulAccumulator<E2> {
  ///
  pub fn scalar_mul<E1: Engine<Scalar = E2::Base>>(
    &mut self,
    _A: &HashedCommitment<E1>,
    _B: &HashedCommitment<E1>,
    _x: &E1::Scalar,
    _transcript: &mut Transcript<E1>,
  ) -> (HashedCommitment<E1>, ScalarMulFoldProof<E1, E2>) {
    // Compute C = A + x * B
    // Compute W proof of this operation
    // compute H(C) as the circuit representation of C, where H is Poseidon on the secondary curve
    // Add C,W to the transcript
    // Set X = [H(A), H(B), X, H(C)] and fold into self
    // return proof
    todo!()
  }

  /// Compute
  pub fn merge<E1: Engine<Scalar = E2::Base>>(
    self,
    _other: Self,
    _transcript: &mut Transcript<E1>,
  ) -> (Self, ScalarMulMergeProof<E1, E2>) {
    // self and other will not need to be added to the transcript since they are obtained from an accumulator
    // we need to compute the T cross term vector
    // add T to transcript
    // return linear combination of both accumulators
    todo!()
  }

  /// Return the succinct instance of the accumulator
  pub(crate) fn instance(&self) -> ScalarMulAccumulatorInstance<E2> {
    self.instance.clone()
  }
}
