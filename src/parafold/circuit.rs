use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::nivc::circuit::AllocatedNIVCState;
use crate::parafold::nivc::{NIVCMergeProof, NIVCUpdateProof, NIVCIO};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::parafold::transcript::TranscriptConstants;
use crate::traits::circuit_supernova::EnforcingStepCircuit;
use crate::traits::Engine;

pub fn synthesize_step<E1, E2, CS, SF>(
  mut cs: CS,
  ro_consts: &TranscriptConstants<E1>,
  proof: NIVCUpdateProof<E1, E2>,
  step_circuit: &SF,
) -> Result<NIVCIO<E1::Scalar>, SynthesisError>
where
  E1: Engine,
  E2: Engine<Scalar = E1::Base, Base = E1::Scalar>,
  CS: ConstraintSystem<E1::Scalar>,
  SF: EnforcingStepCircuit<E1::Scalar>,
{
  // Fold proof for previous state
  let (mut state, transcript) =
    AllocatedNIVCState::from_proof(cs.namespace(|| "verify self"), ro_consts, proof)?;

  let io = state.update_io(cs.namespace(|| "step"), step_circuit);

  transcript.inputize(cs.namespace(|| "inputize transcript"))?;
  state.inputize(cs.namespace(|| "inputize state"))?;

  io
}
/// Circuit
pub fn synthesize_merge<E1, E2, CS>(
  mut cs: CS,
  ro_consts: &TranscriptConstants<E1>,
  proof_L: NIVCUpdateProof<E1, E2>,
  proof_R: NIVCUpdateProof<E1, E2>,
  proof_merge: NIVCMergeProof<E1, E2>,
) -> Result<NIVCIO<E1::Scalar>, SynthesisError>
where
  E1: Engine,
  E2: Engine<Scalar = E1::Base, Base = E1::Scalar>,
  CS: ConstraintSystem<E1::Scalar>,
{
  // Verify L
  let (self_L, transcript_L) =
    AllocatedNIVCState::from_proof(cs.namespace(|| "verify proof_L"), ro_consts, proof_L)?;
  // Verify R
  let (self_R, transcript_R) =
    AllocatedNIVCState::from_proof(cs.namespace(|| "verify proof_R"), ro_consts, proof_R)?;
  // Merge transcripts
  let mut transcript = AllocatedTranscript::merge(transcript_L, transcript_R);

  // Merge states
  let (state, io_native) = AllocatedNIVCState::merge(
    cs.namespace(|| "merge"),
    self_L,
    self_R,
    ro_consts,
    proof_merge,
    &mut transcript,
  )?;

  transcript.inputize(cs.namespace(|| "inputize transcript"))?;
  state.inputize(cs.namespace(|| "inputize state"))?;

  Ok(io_native)
}
