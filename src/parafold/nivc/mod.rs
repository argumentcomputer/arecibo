use bellpepper_core::num::AllocatedNum;
use neptune::generic_array::typenum::U24;
use neptune::poseidon::PoseidonConstants;

use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CSInstance;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::transcript::TranscriptElement;
use crate::traits::{CurveCycleEquipped, Engine};

pub mod circuit;
pub mod prover;

/// The input and output of a NIVC computation over one or more steps.
///
/// # Note
/// - An IO result is trivial if {pc, z}_in == {pc, z}_out
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NIVCIO<E: CurveCycleEquipped> {
  pc_in: E::Scalar,
  z_in: Vec<E::Scalar>,
  pc_out: E::Scalar,
  z_out: Vec<E::Scalar>,
}

/// The input and output of a NIVC computation over one or more steps.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCIO<E: CurveCycleEquipped> {
  pc_in: AllocatedNum<E::Scalar>,
  z_in: Vec<AllocatedNum<E::Scalar>>,
  pc_out: AllocatedNum<E::Scalar>,
  z_out: Vec<AllocatedNum<E::Scalar>>,
}

type NIVCPoseidonConstants<E> = PoseidonConstants<<E as Engine>::Scalar, U24>;

/// Succinct representation of the recursive NIVC state that is known
#[derive(Clone, Debug)]
pub struct NIVCStateInstance<E: CurveCycleEquipped> {
  transcript_state: E::Scalar,
  io: NIVCIO<E>,
  accs_hash: Vec<E::Scalar>,
  acc_cf: RelaxedSecondaryR1CSInstance<E>,
}

/// A proof for loading a previous NIVC output inside a circuit.
#[derive(Debug, Clone)]
pub struct NIVCUpdateProof<E: CurveCycleEquipped> {
  transcript_buffer: Vec<TranscriptElement<E>>,

  state: NIVCStateInstance<E>,

  acc_prev: RelaxedR1CSInstance<E>,
  index_prev: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct NIVCMergeProof<E: CurveCycleEquipped> {
  transcript_buffer: Vec<E::Scalar>,
  accs_L: Vec<RelaxedR1CSInstance<E>>,
  accs_R: Vec<RelaxedR1CSInstance<E>>,
}
