use std::marker::PhantomData;

use crate::parafold::transcript::prover::{Transcript, TranscriptRepresentable};
use crate::traits::Engine;
use crate::Commitment;

/// A native group element for the [Engine] is given by `point = (x, y)` where the coordinates are over the base field.
/// Inside a circuit, it is represented only as the hash `h = H(x, y)`, where `H` is a hash function with
/// efficient arithmetization over the base field. The identity element is represented by the zero `hash`.   
#[derive(Debug, Clone, Default)]
pub struct HashedCommitment<E1: Engine> {
  point: Commitment<E1>,
  hash: E1::Base,
  hash_limbs: Vec<E1::Scalar>,
}

impl<E1: Engine> HashedCommitment<E1> {
  pub fn new(_C: Commitment<E1>) -> Self {
    todo!()
  }
}

impl<E1: Engine> TranscriptRepresentable<E1::Scalar> for HashedCommitment<E1> {
  fn to_field_vec(&self) -> Vec<E1::Scalar> {
    // Since the scalar field F_r is smaller than the base field F_q, the circuit needs to decompose
    // `hash` into the appropriate number of limbs.
    // Decompose `hash` into `n` limbs over F_r

    todo!()
  }
}

/// A proof for a non-native group operation C = A + x * B, where x is a native scalar
/// and A, B, C, are non-native group elements
///
#[derive(Debug, Clone, Default)]
pub struct ScalarMulFoldProof<E1: Engine, E2: Engine> {
  output: HashedCommitment<E1>,
  W: Commitment<E2>,
  T: Commitment<E2>,
}

#[derive(Debug, Clone)]
pub struct ScalarMulMergeProof<E1: Engine, E2: Engine> {
  T: Commitment<E2>,
  _marker: PhantomData<E1>,
}

#[derive(Debug)]
pub struct ScalarMulAccumulator<E1: Engine, E2: Engine> {
  // ro consts secondary?
  // used to hash the incoming point
  instance: ScalarMulAccumulatorInstance<E1, E2>,
  W: Vec<E2::Scalar>,
  E: Vec<E2::Scalar>,
}

impl<E1: Engine, E2: Engine> ScalarMulAccumulator<E1, E2> {
  ///
  pub fn scalar_mul(
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
  pub fn merge(
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
  pub(crate) fn instance(&self) -> ScalarMulAccumulatorInstance<E1, E2> {
    self.instance.clone()
  }
}

#[derive(Debug, Clone)]
pub struct ScalarMulAccumulatorInstance<E1: Engine, E2: Engine> {
  u: E2::Scalar,
  X: Vec<E2::Scalar>,
  W_comm: Commitment<E2>,
  E_comm: Commitment<E2>,
  _marker: PhantomData<E1>,
}
