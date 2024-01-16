use crate::traits::Engine;
use crate::Commitment;

/// A proof containing the result of a non-native scalar multiplication performed on the cycle curve.
///
/// # Details
/// Given the three inputs (A,B,r), this struct contains the output C = A + r * B, and a witness
///
/// # TODO
/// - Implement conversion to R1CS instance
/// - Implement mapping from non-native point representation to suitable public inputs.
pub struct ScalarMulFoldProof<E: Engine> {
  // witness W
  // fold proof T
}

pub struct ScalarMulMergeProof<E: Engine> {
  // fold proof T
}

pub struct ScalarMulAccumulator<E: Engine> {
  // instance ScalarMulAccumulatorInstance
  // W
  // E
}

impl<E: Engine> ScalarMulAccumulator<E> {
  pub(crate) fn instance(&self) -> ScalarMulAccumulatorInstance<E> {
    todo!()
  }
}

impl<E: Engine> ScalarMulAccumulator<E> {
  pub fn scalar_mul(
    &mut self,
    _A: Commitment<E>,
    _B: Commitment<E>,
    _r: E::Scalar,
    _transcript: &mut E::TE,
  ) -> (Commitment<E>, ScalarMulFoldProof<E>) {
    todo!()
  }

  pub fn merge(self, _other: Self, _transcript: &mut E::TE) -> (Self, ScalarMulMergeProof<E>) {
    todo!()
  }
}

pub struct ScalarMulAccumulatorInstance<E: Engine> {
  // u
  // X
  // W_comm
  // E_comm
}
