use std::sync::Arc;

use digest::consts::U16;
use ff::Field;
use neptune::hash_type::HashType;
use neptune::poseidon::PoseidonConstants;
use neptune::Strength;

use crate::parafold::hash::HashElement;
use crate::parafold::nifs::{
  new_primary_r1cs_constants, PrimaryR1CSConstants, RelaxedR1CSInstance,
};
use crate::parafold::transcript::{new_transcript_constants, TranscriptConstants};
use crate::r1cs::R1CSShape;
use crate::traits::{CurveCycleEquipped, Engine};
use crate::CommitmentKey;

mod verifier;

mod cycle_fold;

mod nifs;

#[allow(unused)]
pub mod prover;

mod gadgets;
mod hash;
mod io;
mod nifs_secondary;
#[cfg(test)]
mod test;
mod transcript;

pub struct ProvingKey<E: CurveCycleEquipped> {
  // public params
  pub(crate) ck: Arc<CommitmentKey<E>>,
  pub(crate) ck_cf: Arc<CommitmentKey<E::Secondary>>,
  // Shapes for each augmented StepCircuit. The last shape is for the merge circuit.
  pub(crate) arity: usize,
  pub(crate) shapes: Vec<R1CSShape<E>>,
  pub(crate) shape_cf: R1CSShape<E::Secondary>,
  #[allow(unused)]
  pub(crate) constants: NIVCPoseidonConstants<E>,
}

/// The input and output of a NIVC computation over one or more steps.
///
/// # Note
/// - An IO result is trivial if {pc, z}_in == {pc, z}_out
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepCircuitIO<E: CurveCycleEquipped> {
  pc_in: E::Scalar,
  z_in: Vec<E::Scalar>,
  pc_out: E::Scalar,
  z_out: Vec<E::Scalar>,
}

/// A proof for loading a previous NIVC output inside a circuit.
#[derive(Debug, Clone)]
pub struct StepProof<E: CurveCycleEquipped> {
  pub transcript_buffer: Option<Vec<HashElement<E>>>,
  pub acc: RelaxedR1CSInstance<E>,
  pub index: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct MergeProof<E: CurveCycleEquipped> {
  step_proof_L: StepProof<E>,
  step_proof_R: StepProof<E>,
  pub transcript_buffer: Option<Vec<HashElement<E>>>,
  pub accs_L: Vec<RelaxedR1CSInstance<E>>,
  pub accs_R: Vec<RelaxedR1CSInstance<E>>,
}

type VerifierStateArity = U16;
pub type VerifierStateConstants<E> = PoseidonConstants<<E as Engine>::Scalar, VerifierStateArity>;

pub fn new_verifier_state_constants<E: Engine>() -> VerifierStateConstants<E> {
  VerifierStateConstants::<E>::new_with_strength_and_type(Strength::Standard, HashType::Sponge)
}

pub struct NIVCPoseidonConstants<E: Engine> {
  primary_r1cs: PrimaryR1CSConstants<E>,
  verifier_state: VerifierStateConstants<E>,
  transcript: TranscriptConstants<E>,
}

impl<E: Engine> NIVCPoseidonConstants<E> {
  pub fn new() -> Self {
    Self {
      primary_r1cs: new_primary_r1cs_constants::<E>(),
      verifier_state: new_verifier_state_constants::<E>(),
      transcript: new_transcript_constants::<E>(),
    }
  }
}

impl<E: CurveCycleEquipped> StepProof<E> {
  fn dummy() -> Self {
    Self {
      transcript_buffer: None,
      acc: RelaxedR1CSInstance::init(E::Scalar::ZERO),
      index: None,
    }
  }
}

impl<E: CurveCycleEquipped> MergeProof<E> {
  pub fn dummy(num_circuits: usize) -> Self {
    Self {
      step_proof_L: StepProof::dummy(),
      step_proof_R: StepProof::dummy(),
      transcript_buffer: None,
      accs_L: vec![RelaxedR1CSInstance::init(E::Scalar::ZERO); num_circuits],
      accs_R: vec![RelaxedR1CSInstance::init(E::Scalar::ZERO); num_circuits],
    }
  }
}

#[cfg(test)]
mod tests {
  use bellpepper_core::test_cs::TestConstraintSystem;
  use bellpepper_core::ConstraintSystem;

  use crate::parafold::hash::{AllocatedHashWriter, HashWriter};
  use crate::parafold::verifier::{AllocatedVerifierState, VerifierState};
  use crate::parafold::{NIVCPoseidonConstants, StepProof};
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  type Scalar = <E as Engine>::Scalar;

  type CS = TestConstraintSystem<Scalar>;

  #[test]
  fn test_verify() {
    let mut cs = CS::new();

    let constants = NIVCPoseidonConstants::<E>::new();

    let instance = VerifierState::<E>::dummy(0, 1, &constants);
    let proof = StepProof::<E>::dummy();

    let _state =
      AllocatedVerifierState::init(cs.namespace(|| "alloc"), &instance, proof, &constants);

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_hash() {
    let mut cs = CS::new();

    let constants = NIVCPoseidonConstants::<E>::new();
    let state = VerifierState::<E>::dummy(4, 4, &constants);
    let state_hash = state.hash(&constants.verifier_state);
    let allocated_state =
      AllocatedVerifierState::<E>::alloc_unverified(cs.namespace(|| "alloc state"), &state);

    let allocated_state_hash = allocated_state
      .hash(cs.namespace(|| "hash"), &constants.verifier_state)
      .unwrap();

    assert_eq!(state_hash, allocated_state_hash.get_value().unwrap());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
