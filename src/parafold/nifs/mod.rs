use crate::traits::Engine;
use crate::Commitment;
pub mod circuit;
pub mod circuit_secondary;
pub mod prover;

/// Instance of a Relaxed-R1CS accumulator for a circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelaxedR1CSInstance<E1: Engine> {
  // TODO: Add pp_digest for this circuit.
  u: E1::Scalar,
  X: Vec<E1::Scalar>,
  W: Commitment<E1>,
  E: Commitment<E1>,
}

/// A proof for folding a statement X of a circuit C into a Relaxed-R1CS circuit for the same circuit C
#[derive(Debug, Clone, Default)]
pub struct FoldProof<E1: Engine> {
  W: Commitment<E1>,
  T: Commitment<E1>,
}

/// A proof for merging two valid Relaxed-R1CS accumulators for the same circuit C
#[derive(Debug, Clone)]
pub struct MergeProof<E1: Engine> {
  T: Commitment<E1>,
}
