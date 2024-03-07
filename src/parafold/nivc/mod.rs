use bellpepper_core::num::AllocatedNum;
use ff::Field;
use neptune::generic_array::typenum::U16;
use neptune::poseidon::PoseidonConstants;

use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CSInstance;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::transcript::{TranscriptConstants, TranscriptElement};
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

type NIVCPoseidonConstants<E> = PoseidonConstants<<E as Engine>::Scalar, U16>;

/// Succinct representation of the recursive NIVC state that is known
#[derive(Clone, Debug, PartialEq)]
pub struct NIVCStateInstance<E: CurveCycleEquipped> {
  transcript_state: E::Scalar,
  pub io: NIVCIO<E>,
  pub accs_hash: Vec<E::Scalar>,
  pub acc_cf: RelaxedSecondaryR1CSInstance<E>,
}

#[derive(Debug, Clone)]
pub struct NIVCCircuitInput<E: CurveCycleEquipped> {
  pub instance: NIVCStateInstance<E>,
  pub proof: NIVCStateProof<E>,
}

impl<E: CurveCycleEquipped> NIVCCircuitInput<E> {
  pub fn dummy(
    ro_consts: TranscriptConstants<E::Scalar>,
    arity: usize,
    num_circuits: usize,
  ) -> Self {
    let instance = NIVCStateInstance::dummy(arity, num_circuits);

    let transcript = instance.simulate_update(ro_consts);

    let (_, transcript_buffer) = transcript.seal();

    let proof = NIVCStateProof {
      transcript_buffer,
      acc: RelaxedR1CSInstance::dummy(),
      index: None,
    };

    Self { instance, proof }
  }
}

/// A proof for loading a previous NIVC output inside a circuit.
#[derive(Debug, Clone)]
pub struct NIVCStateProof<E: CurveCycleEquipped> {
  pub transcript_buffer: Vec<TranscriptElement<E>>,
  pub acc: RelaxedR1CSInstance<E>,
  pub index: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct NIVCMergeProof<E: CurveCycleEquipped> {
  pub transcript_buffer: Vec<TranscriptElement<E>>,
  pub accs_L: Vec<RelaxedR1CSInstance<E>>,
  pub accs_R: Vec<RelaxedR1CSInstance<E>>,
}

impl<E: CurveCycleEquipped> NIVCMergeProof<E> {
  pub fn dummy(ro_consts: TranscriptConstants<E::Scalar>, num_circuits: usize) -> Self {
    let dummy_transcript = E::Scalar::ZERO;

    let transcript = NIVCStateInstance::simulate_merge(
      dummy_transcript,
      dummy_transcript,
      num_circuits,
      ro_consts,
    );
    let (_, transcript_buffer) = transcript.seal();
    Self {
      transcript_buffer,
      accs_L: vec![RelaxedR1CSInstance::<E>::dummy(); num_circuits],
      accs_R: vec![RelaxedR1CSInstance::<E>::dummy(); num_circuits],
    }
  }
}

#[cfg(test)]
mod tests {
  use bellpepper_core::test_cs::TestConstraintSystem;
  use bellpepper_core::ConstraintSystem;

  use crate::parafold::nivc::circuit::AllocatedNIVCState;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;

  type CS = TestConstraintSystem<Scalar>;

  #[test]
  fn test_verify() {
    let mut cs = CS::new();

    let ro_consts = TranscriptConstants::<Scalar>::new();
    let dummy_input = NIVCCircuitInput::<E>::dummy(ro_consts.clone(), 0, 1);

    let _state = AllocatedNIVCState::init(cs.namespace(|| "alloc"), ro_consts, &dummy_input);

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_hash() {
    let mut cs = CS::new();

    let state = NIVCStateInstance::<E>::dummy(4, 4);
    let (allocated_state, _) =
      AllocatedNIVCState::<E>::alloc_unverified(cs.namespace(|| "alloc state"), &state);

    let state_hash = state.hash();
    let allocated_state_hash = allocated_state.hash(cs.namespace(|| "hash")).unwrap();

    assert_eq!(state_hash, allocated_state_hash.get_value().unwrap());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
