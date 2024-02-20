use crate::traits::Engine;
use crate::Commitment;
pub mod circuit;
pub mod circuit_secondary;
pub mod prover;

/// Instance of a Relaxed-R1CS accumulator for a circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelaxedR1CSInstance<E: Engine> {
  // TODO: Add pp_digest for this circuit.
  u: E::Scalar,
  X: Vec<E::Scalar>,
  W: Commitment<E>,
  E: Commitment<E>,
}

/// A proof for folding a statement X of a circuit C into a Relaxed-R1CS accumulator for the same circuit C
#[derive(Debug, Clone, Default)]
pub struct FoldProof<E: Engine> {
  W: Commitment<E>,
  T: Commitment<E>,
}

/// A proof for merging two valid Relaxed-R1CS accumulators for the same circuit C
#[derive(Debug, Clone)]
pub struct MergeProof<E: Engine> {
  T: Commitment<E>,
}
