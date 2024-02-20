use bellpepper_core::num::AllocatedNum;
use ff::PrimeField;

use crate::parafold::nifs::{FoldProof, MergeProof, RelaxedR1CSInstance};
use crate::traits::Engine;

pub mod circuit;
pub mod prover;

/// The input and output of a NIVC computation over one or more steps.
///
/// # Note
/// - An IO result is trivial if {pc, z}_in == {pc, z}_out
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NIVCIO<F> {
  pc_in: F,
  z_in: Vec<F>,
  pc_out: F,
  z_out: Vec<F>,
}

/// The input and output of a NIVC computation over one or more steps.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCIO<F: PrimeField> {
  pc_in: AllocatedNum<F>,
  z_in: Vec<AllocatedNum<F>>,
  pc_out: AllocatedNum<F>,
  z_out: Vec<AllocatedNum<F>>,
}

/// Succinct representation of the recursive NIVC state that is known
#[derive(Clone, Debug)]
pub struct NIVCStateInstance<E1: Engine, E2: Engine> {
  io: NIVCIO<E1::Scalar>,
  accs_hash: Vec<E1::Scalar>,
  acc_cf: RelaxedR1CSInstance<E2>,
}

/// A proof for loading a previous NIVC output inside a circuit.
#[derive(Debug, Clone)]
pub struct NIVCUpdateProof<E1: Engine, E2: Engine> {
  transcript_init: E1::Scalar,

  state: NIVCStateInstance<E1, E2>,

  acc_prev: RelaxedR1CSInstance<E1>,
  index_prev: Option<usize>,
  nifs_fold_proof: FoldProof<E1>,

  sm_fold_proofs: [FoldProof<E2>; 2],
}

#[derive(Debug, Clone)]
pub struct NIVCMergeProof<E1: Engine, E2: Engine> {
  accs_L: Vec<RelaxedR1CSInstance<E1>>,
  accs_R: Vec<RelaxedR1CSInstance<E1>>,
  nivc_merge_proof: Vec<MergeProof<E1>>,

  cf_merge_proof: MergeProof<E2>,

  sm_fold_proofs: Vec<FoldProof<E2>>,
}
