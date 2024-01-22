use crate::parafold::cycle_fold::{
  AllocatedScalarMulAccumulator, AllocatedScalarMulMergeProof, ScalarMulAccumulatorInstance,
  ScalarMulMergeProof,
};
use crate::parafold::nifs_primary::{
  AllocatedFoldProof, AllocatedMergeProof, AllocatedRelaxedR1CSInstance, FoldProof, MergeProof,
  RelaxedR1CSInstance,
};
use crate::traits::Engine;
use bellpepper_core::num::AllocatedNum;
use ff::PrimeField;

pub mod circuit;
mod circuit_alloc;
pub mod prover;

#[derive(Debug, Clone, PartialEq)]
pub struct NIVCIO<F> {
  pc_in: F,
  z_in: Vec<F>,
  pc_out: F,
  z_out: Vec<F>,
}

/// The input and output of a NIVC computation over one or more steps.
///
/// # Note
/// - An IO result is trivial if {pc, z}_in == {pc, z}_out
#[derive(Debug, Clone)]
pub struct AllocatedNIVCIO<F: PrimeField> {
  pc_in: AllocatedNum<F>,
  z_in: Vec<AllocatedNum<F>>,
  pc_out: AllocatedNum<F>,
  z_out: Vec<AllocatedNum<F>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct NIVCStateInstance<E1: Engine, E2: Engine> {
  hash_input: [E1::Scalar; 2],
  io: NIVCIO<E1::Scalar>,
  accs: Vec<RelaxedR1CSInstance<E1>>,
  acc_sm: ScalarMulAccumulatorInstance<E2>,
}

/// A representation of a NIVC state, where `io` represents the computations inputs and outputs,
/// and the `accs` are the accumulators for each step function that was used to produce this result.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCState<E1: Engine, E2: Engine> {
  hash_input: [AllocatedNum<E1::Scalar>; 2],
  io: AllocatedNIVCIO<E1::Scalar>,
  accs: Vec<AllocatedRelaxedR1CSInstance<E1>>,
  acc_sm: AllocatedScalarMulAccumulator<E1, E2>,
}

#[derive(Debug, Clone)]
pub struct NIVCUpdateProof<E1: Engine, E2: Engine> {
  state: NIVCStateInstance<E1, E2>,
  index: usize,
  nifs_fold_proof: FoldProof<E1, E2>,
}

/// A proved NIVC step for a particular step function. Can be folded into an existing [`AllocatedNIVCState'].
#[derive(Debug, Clone)]
pub struct AllocatedNIVCStateProof<E1: Engine, E2: Engine> {
  /// Output of the previous step
  state: AllocatedNIVCState<E1, E2>,
  /// Index of the circuits that produced `state`
  index: usize,
  /// Proof for folding the previous circuit into `state.accs[index_prev]`
  fold_proof: AllocatedFoldProof<E1, E2>,
}

#[derive(Debug, Clone)]
pub struct NIVCMergeProof<E1: Engine, E2: Engine> {
  nivc_update_proof_L: NIVCUpdateProof<E1, E2>,
  nivc_update_proof_R: NIVCUpdateProof<E1, E2>,
  sm_merge_proof: ScalarMulMergeProof<E1, E2>,
  nivc_merge_proof: Vec<MergeProof<E1, E2>>,
}

/// A proved NIVC step for a particular step function. Can be folded into an existing [`AllocatedNIVCState'].
#[derive(Debug, Clone)]
pub struct AllocatedNIVCMergeProof<E1: Engine, E2: Engine> {
  proof_L: AllocatedNIVCStateProof<E1, E2>,
  proof_R: AllocatedNIVCStateProof<E1, E2>,
  /// Proof for merging the scalar multiplication accumulators from two different states.
  sm_merge_proof: AllocatedScalarMulMergeProof<E1, E2>,
  /// Proofs for merging each accumulator in [AllocatedNIVCState.accs] from two different states
  nivc_merge_proofs: Vec<AllocatedMergeProof<E1, E2>>,
}
