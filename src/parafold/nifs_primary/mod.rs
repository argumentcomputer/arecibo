use bellpepper_core::num::AllocatedNum;

use crate::parafold::cycle_fold::{AllocatedHashedCommitment, AllocatedScalarMulFoldProof};
use crate::parafold::cycle_fold::{HashedCommitment, ScalarMulFoldProof};
use crate::traits::Engine;

pub mod circuit;
mod circuit_alloc;
pub mod prover;

/// Instance of a Relaxed-R1CS accumulator for a circuit
#[derive(Debug, Clone, PartialEq)]
pub struct RelaxedR1CSInstance<E1: Engine> {
  u: E1::Scalar,
  X: Vec<E1::Scalar>,
  W: HashedCommitment<E1>,
  E: HashedCommitment<E1>,
}

/// Allocated [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub struct AllocatedRelaxedR1CSInstance<E1: Engine> {
  u: AllocatedNum<E1::Scalar>,
  X: Vec<AllocatedNum<E1::Scalar>>,
  W: AllocatedHashedCommitment<E1>,
  E: AllocatedHashedCommitment<E1>,
}

/// A proof for folding a statement X of a circuit C into a Relaxed-R1CS circuit for the same circuit C
#[derive(Debug, Clone, Default)]
pub struct FoldProof<E1: Engine, E2: Engine> {
  W: HashedCommitment<E1>,
  T: HashedCommitment<E1>,
  W_sm_proof: ScalarMulFoldProof<E1, E2>,
  E_sm_proof: ScalarMulFoldProof<E1, E2>,
}

/// An allocated Nova folding proof, for either folding an [R1CSInstance] or a [RelaxedR1CSInstance] into
/// another [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub struct AllocatedFoldProof<E1: Engine, E2: Engine> {
  pub W: AllocatedHashedCommitment<E1>,
  pub T: AllocatedHashedCommitment<E1>,
  pub W_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
  pub E_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
}

/// A proof for merging two valid Relaxed-R1CS accumulators for the same circuit C
#[derive(Debug, Clone)]
pub struct MergeProof<E1: Engine, E2: Engine> {
  T: HashedCommitment<E1>,
  W_sm_proof: ScalarMulFoldProof<E1, E2>,
  E1_sm_proof: ScalarMulFoldProof<E1, E2>,
  E2_sm_proof: ScalarMulFoldProof<E1, E2>,
}

#[derive(Debug, Clone)]
pub struct AllocatedMergeProof<E1: Engine, E2: Engine> {
  T: AllocatedHashedCommitment<E1>,
  W_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
  E1_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
  E2_sm_proof: AllocatedScalarMulFoldProof<E1, E2>,
}
