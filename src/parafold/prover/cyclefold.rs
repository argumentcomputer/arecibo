use crate::traits::{Engine, TranscriptEngineTrait};
use crate::Commitment;

pub struct ScalarMulInstance<E: Engine> {
  A: Commitment<E>,
  B: Commitment<E>,
  r: E::Scalar,
  // C = A + r * B
  C: Commitment<E>,
}

impl<E: Engine> ScalarMulInstance<E> {
  pub fn new(
    A: Commitment<E>,
    B: Commitment<E>,
    r: E::Scalar,
    transcript: &mut E::TE,
  ) -> (Commitment<E>, Self) {
    let C = A + r * B;
    transcript.absorb(b"C", &C);
    (C.clone(), Self { A, B, r, C })
  }
}

/// A proof containing the result of a non-native scalar multiplication performed on the cycle curve.
///
/// # Details
/// Given the three inputs (A,B,r), this struct contains the output C = A + r * B, and a witness
///
/// # TODO
/// - Implement conversion to R1CS instance
/// - Implement mapping from non-native point representation to suitable public inputs.
pub struct ScalarMulProof<E: Engine> {
  // output
  // witness
}
