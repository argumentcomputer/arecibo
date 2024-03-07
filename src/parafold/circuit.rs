use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::nivc::circuit::AllocatedNIVCState;
use crate::parafold::nivc::{NIVCCircuitInput, NIVCMergeProof, NIVCIO};
use crate::parafold::transcript::TranscriptConstants;
use crate::supernova::StepCircuit;
use crate::traits::CurveCycleEquipped;

pub fn synthesize_step<E, CS, SF>(
  mut cs: CS,
  input: &NIVCCircuitInput<E>,
  ro_consts: TranscriptConstants<E::Scalar>,
  step_circuit: &SF,
) -> Result<Option<NIVCIO<E>>, SynthesisError>
where
  E: CurveCycleEquipped,
  CS: ConstraintSystem<E::Scalar>,
  SF: StepCircuit<E::Scalar>,
{
  let mut state = AllocatedNIVCState::init(cs.namespace(|| "alloc state"), ro_consts, input)?;

  let io = state.update_io(cs.namespace(|| "step"), step_circuit)?;

  state.inputize(cs.namespace(|| "inputize state"))?;

  Ok(io)
}

///Circuit
#[allow(unused)]
pub fn synthesize_merge<E, CS>(
  mut cs: CS,
  input_L: &NIVCCircuitInput<E>,
  input_R: &NIVCCircuitInput<E>,
  merge_proof: NIVCMergeProof<E>,
  ro_consts: TranscriptConstants<E::Scalar>,
) -> Result<Option<NIVCIO<E>>, SynthesisError>
where
  E: CurveCycleEquipped,
  CS: ConstraintSystem<E::Scalar>,
{
  // Verify L
  let mut state_L = AllocatedNIVCState::init(
    cs.namespace(|| "alloc state_L"),
    ro_consts.clone(),
    &input_L,
  )?;

  // Verify L
  let mut state_R = AllocatedNIVCState::init(
    cs.namespace(|| "alloc state_R"),
    ro_consts.clone(),
    &input_R,
  )?;

  // Merge states
  let (state, io_native) = AllocatedNIVCState::merge(
    cs.namespace(|| "merge"),
    state_L,
    state_R,
    merge_proof,
    ro_consts,
  )?;

  state.inputize(cs.namespace(|| "inputize state"))?;

  Ok(io_native)
}
