use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::nivc::circuit::{AllocatedNIVCState, AllocatedNIVCStateProof, NIVCHasher};
use crate::parafold::nivc::prover::NIVCStateProof;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::circuit_supernova::StepCircuit;
use crate::traits::{Engine, ROConstantsCircuit};

pub fn step<
  C: StepCircuit<E1::Scalar>,
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
  CS: ConstraintSystem<E1::Scalar>,
>(
  cs: &mut CS,
  pp: E1::Scalar,
  ro_consts: ROConstantsCircuit<E1>,
  circuit: C,
  proof: NIVCStateProof<E1, E2>,
) -> Result<(), SynthesisError> {
  let arity = circuit.arity();
  let pp = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pp"), || pp);
  let hasher = NIVCHasher::new(ro_consts.clone(), pp, arity);
  let mut transcript = AllocatedTranscript::new(ro_consts);
  let proof = AllocatedNIVCStateProof::alloc_infallible(cs.namespace(|| "alloc proof"), || proof);
  let _state = AllocatedNIVCState::new_step(
    cs.namespace(|| ""),
    &hasher,
    proof,
    circuit,
    &mut transcript,
  )?;
  Ok(())
  // state.
}

// /// Given the state transition over the io
// ///   `self_state = (vk_self, vk_nivc, self_acc, nivc_acc, nivc_io)`
// /// self_io = {self_state_curr, self_state_next}
// pub struct StateTransitionCircuit<E: Engine> {
//   /// Random-oracle constants
//   ro_consts: ROConstantsCircuit<E>,
//
//   /// Hash of public parameters for IVC
//   pp: AllocatedNum<E::Scalar>,
//
//   state: AllocatedRecursionState<E>,
//
//   transcript: AllocatedTranscript<E::Scalar>,
// }
//
// impl<E: Engine> StateTransitionCircuit<E> {
//   pub fn new<CS>(
//     mut cs: CS,
//     pk: &ProvingKey<E>,
//     self_acc_prev: RelaxedR1CSInstance<E>,
//     nivc_acc_curr: impl IntoIterator<Item = Option<RelaxedR1CSInstance<E>>>,
//     nivc_state: NIVCState<E::Scalar>,
//   ) -> Result<Self, SynthesisError>
//   where
//     CS: ConstraintSystem<E::Scalar>,
//   {
//     let ro_consts = ROConstantsCircuit::<E>::default();
//
//     let pp_self = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pp_self"), || pk.pp);
//     let pp_nivc = pk
//       .nivc
//       .iter()
//       .enumerate()
//       .map(|(i, pk_nivc)| {
//         AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc pp_nivc[{i}]")), || {
//           pk_nivc.pp
//         })
//       })
//       .collect::<Vec<_>>();
//
//     let self_acc_prev = AllocatedRelaxedR1CSInstance::alloc_infallible(
//       cs.namespace(|| "alloc self_acc_prev"),
//       || self_acc_prev,
//     );
//
//     let nivc_acc_curr = nivc_acc_curr
//       .into_iter()
//       .enumerate()
//       .map(|(i, nivc_acc)| {
//         AllocatedRelaxedR1CSInstance::alloc_infallible(
//           cs.namespace(|| format!("alloc nivc_acc_prev[{i}]")),
//           || nivc_acc.unwrap_or(RelaxedR1CSInstance::default(&pk.nivc[i].shape)),
//         )
//       })
//       .collect::<Vec<_>>();
//
//     let nivc_state =
//       AllocatedNIVCIO::alloc_infallible(cs.namespace(|| "alloc nivc_state"), || nivc_state);
//
//     Ok(Self {
//       ro_consts,
//       pp_self,
//       pp_nivc,
//       self_acc: self_acc_prev,
//       nivc_acc: nivc_acc_curr,
//       nivc_state,
//       scalar_mul_instances: vec![],
//       transcript: AllocatedTranscript::new()?,
//     })
//   }
//
//   // pub(crate) fn finalize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
//   // where
//   //   CS: ConstraintSystem<E::Scalar>,
//   // {
//   //   let self_io_hash_next: AllocatedNum<E::Scalar> = Self::io_hash(
//   //     cs.namespace(|| "self_io_hash_next"),
//   //     &self.ro_consts,
//   //     &self.pp_self,
//   //     &self.pp_nivc,
//   //     &self.self_acc, // self_acc_curr
//   //     &self.nivc_acc, // self_acc_next
//   //     &self.nivc_state,
//   //   )?;
//   //
//   //   self_io_hash_next.inputize(cs.namespace(|| "inputize self_io_hash_curr"))
//   // }
//
//   // fn io_hash<CS>(
//   //   /*mut*/ _cs: CS,
//   //   _ro_consts: &ROConstantsCircuit<E>,
//   //   _pp_self: &AllocatedNum<E::Scalar>,
//   //   _pp_nivc: &[AllocatedNum<E::Scalar>],
//   //   _self_acc: &AllocatedRelaxedR1CSInstance<E>,
//   //   _nivc_acc: &[AllocatedRelaxedR1CSInstance<E>],
//   //   _nivc_state: &AllocatedNIVCIO<E::Scalar>,
//   // ) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
//   // where
//   //   CS: ConstraintSystem<E::Scalar>,
//   // {
//   //   todo!()
//   // }
// }
