use bellpepper_core::num::AllocatedNum;
use ff::PrimeField;

use crate::parafold::nifs::{FoldProof, MergeProof, RelaxedR1CSInstance};
use crate::traits::CurveCycleEquipped;

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
pub struct NIVCStateInstance<E: CurveCycleEquipped> {
  io: NIVCIO<E::Scalar>,
  accs_hash: Vec<E::Scalar>,
  acc_cf: RelaxedR1CSInstance<E::Secondary>,
}

/// A proof for loading a previous NIVC output inside a circuit.
#[derive(Debug, Clone)]
pub struct NIVCUpdateProof<E: CurveCycleEquipped> {
  transcript_init: E::Scalar,

  state: NIVCStateInstance<E>,

  acc_prev: RelaxedR1CSInstance<E>,
  index_prev: Option<usize>,
  nifs_fold_proof: FoldProof<E>,

  sm_fold_proofs: [FoldProof<E::Secondary>; 2],
}

#[derive(Debug, Clone)]
pub struct NIVCMergeProof<E: CurveCycleEquipped> {
  accs_L: Vec<RelaxedR1CSInstance<E>>,
  accs_R: Vec<RelaxedR1CSInstance<E>>,
  nivc_merge_proof: Vec<MergeProof<E>>,

  cf_merge_proof: MergeProof<E::Secondary>,

  sm_fold_proofs: Vec<FoldProof<E::Secondary>>,
}
