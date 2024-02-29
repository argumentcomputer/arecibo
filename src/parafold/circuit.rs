use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::nivc::circuit::AllocatedNIVCState;
use crate::parafold::nivc::{NIVCUpdateProof, NIVCIO};
use crate::parafold::transcript::TranscriptConstants;
use crate::supernova::StepCircuit;
use crate::traits::CurveCycleEquipped;

pub fn synthesize_step<E, CS, SF>(
  mut cs: CS,
  ro_consts: &TranscriptConstants<E::Scalar>,
  proof: NIVCUpdateProof<E>,
  step_circuit: &SF,
) -> Result<NIVCIO<E>, SynthesisError>
where
  E: CurveCycleEquipped,
  CS: ConstraintSystem<E::Scalar>,
  SF: StepCircuit<E::Scalar>,
{
  // Fold proof for previous state
  let mut state = AllocatedNIVCState::from_proof(cs.namespace(|| "verify self"), ro_consts, proof)?;

  let io_native = state.update_io(cs.namespace(|| "step"), step_circuit);

  state.inputize(cs.namespace(|| "inputize state"))?;

  io_native
}

// /// Circuit
// pub fn synthesize_merge<E, CS>(
//   mut cs: CS,
//   ro_consts: &TranscriptConstants<E::Scalar>,
//   proof_L: NIVCUpdateProof<E>,
//   proof_R: NIVCUpdateProof<E>,
//   proof_merge: NIVCMergeProof<E>,
// ) -> Result<NIVCIO<E>, SynthesisError>
// where
//   E: CurveCycleEquipped,
//   CS: ConstraintSystem<E::Scalar>,
// {
//   // Verify L
//   let (self_L, transcript_L) =
//     AllocatedNIVCState::from_proof(cs.namespace(|| "verify proof_L"), ro_consts, proof_L)?;
//   // Verify R
//   let (self_R, transcript_R) =
//     AllocatedNIVCState::from_proof(cs.namespace(|| "verify proof_R"), ro_consts, proof_R)?;
//   // Merge transcripts
//   let mut transcript = AllocatedTranscript::merge(transcript_L, transcript_R);
//
//   // Merge states
//   let (state, io_native) = AllocatedNIVCState::merge(
//     cs.namespace(|| "merge"),
//     self_L,
//     self_R,
//     ro_consts,
//     proof_merge,
//     &mut transcript,
//   )?;
//
//   transcript.inputize(cs.namespace(|| "inputize transcript"))?;
//   state.inputize(cs.namespace(|| "inputize state"))?;
//
//   Ok(io_native)
// }
