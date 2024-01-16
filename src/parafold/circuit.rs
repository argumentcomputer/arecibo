use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};

use crate::gadgets::r1cs::AllocatedRelaxedR1CSInstance;
use crate::parafold::circuit::nivc::AllocatedNIVCIO;
use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::ProvingKey;
use crate::traits::{Engine, ROConstantsCircuit};

mod nifs;
mod nivc;
mod scalar_mul;
mod transcript;

/// Given the state transition over the io
///   `self_state = (vk_self, vk_nivc, self_acc, nivc_acc, nivc_io)`
/// self_io = {self_state_curr, self_state_next}
pub struct StateTransitionCircuit<E: Engine> {
  /// Random-oracle constants
  ro_consts: ROConstantsCircuit<E>,

  /// Hash of public parameters for IVC
  pp: AllocatedNum<E::Scalar>,

  state: AllocatedRecursionState<E>,

  transcript: AllocatedTranscript<E::Scalar>,
}

impl<E: Engine> StateTransitionCircuit<E> {
  pub fn new<CS>(
    mut cs: CS,
    pk: &ProvingKey<E>,
    self_acc_prev: RelaxedR1CSInstance<E>,
    nivc_acc_curr: impl IntoIterator<Item = Option<RelaxedR1CSInstance<E>>>,
    nivc_state: NIVCState<E::Scalar>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let ro_consts = ROConstantsCircuit::<E>::default();

    let pp_self = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pp_self"), || pk.pp);
    let pp_nivc = pk
      .nivc
      .iter()
      .enumerate()
      .map(|(i, pk_nivc)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc pp_nivc[{i}]")), || {
          pk_nivc.pp
        })
      })
      .collect::<Vec<_>>();

    let self_acc_prev = AllocatedRelaxedR1CSInstance::alloc_infallible(
      cs.namespace(|| "alloc self_acc_prev"),
      || self_acc_prev,
    );

    let nivc_acc_curr = nivc_acc_curr
      .into_iter()
      .enumerate()
      .map(|(i, nivc_acc)| {
        AllocatedRelaxedR1CSInstance::alloc_infallible(
          cs.namespace(|| format!("alloc nivc_acc_prev[{i}]")),
          || nivc_acc.unwrap_or(RelaxedR1CSInstance::default(&pk.nivc[i].shape)),
        )
      })
      .collect::<Vec<_>>();

    let nivc_state =
      AllocatedNIVCIO::alloc_infallible(cs.namespace(|| "alloc nivc_state"), || nivc_state);

    Ok(Self {
      ro_consts,
      pp_self,
      pp_nivc,
      self_acc: self_acc_prev,
      nivc_acc: nivc_acc_curr,
      nivc_state,
      scalar_mul_instances: vec![],
      transcript: AllocatedTranscript::new()?,
    })
  }

  // pub(crate) fn finalize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  // where
  //   CS: ConstraintSystem<E::Scalar>,
  // {
  //   let self_io_hash_next: AllocatedNum<E::Scalar> = Self::io_hash(
  //     cs.namespace(|| "self_io_hash_next"),
  //     &self.ro_consts,
  //     &self.pp_self,
  //     &self.pp_nivc,
  //     &self.self_acc, // self_acc_curr
  //     &self.nivc_acc, // self_acc_next
  //     &self.nivc_state,
  //   )?;
  //
  //   self_io_hash_next.inputize(cs.namespace(|| "inputize self_io_hash_curr"))
  // }

  // fn io_hash<CS>(
  //   /*mut*/ _cs: CS,
  //   _ro_consts: &ROConstantsCircuit<E>,
  //   _pp_self: &AllocatedNum<E::Scalar>,
  //   _pp_nivc: &[AllocatedNum<E::Scalar>],
  //   _self_acc: &AllocatedRelaxedR1CSInstance<E>,
  //   _nivc_acc: &[AllocatedRelaxedR1CSInstance<E>],
  //   _nivc_state: &AllocatedNIVCIO<E::Scalar>,
  // ) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  // where
  //   CS: ConstraintSystem<E::Scalar>,
  // {
  //   todo!()
  // }
}
