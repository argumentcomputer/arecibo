//! This module defines the Nova augmented circuit used for Cyclefold

use crate::{
  gadgets::{
    ecc::AllocatedPoint,
    r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
    utils::alloc_scalar_as_base,
  },
  r1cs::{R1CSInstance, RelaxedR1CSInstance},
  traits::{circuit::StepCircuit, commitment::CommitmentTrait, Engine, ROConstantsCircuit},
  Commitment,
};

use abomonation_derive::Abomonation;
use bellpepper::gadgets::{num::AllocatedNum, Assignment};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;
use serde::{Deserialize, Serialize};

use super::gadgets::emulated;
use super::gadgets::AllocatedFoldingData;

#[derive(Clone, PartialEq, Serialize, Deserialize, Abomonation)]
pub struct AugmentedCircuitParams {
  limb_width: usize,
  n_limbs: usize,
}

impl AugmentedCircuitParams {
  pub const fn new(limb_width: usize, n_limbs: usize) -> Self {
    Self {
      limb_width,
      n_limbs,
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub(crate) struct FoldingData<E: Engine> {
  U: RelaxedR1CSInstance<E>,
  u: R1CSInstance<E>,
  T: Commitment<E>,
}

impl<E: Engine> FoldingData<E> {
  pub fn new(U: RelaxedR1CSInstance<E>, u: R1CSInstance<E>, T: Commitment<E>) -> Self {
    Self { U, u, T }
  }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct AugmentedCircuitInputs<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  pp_digest: E1::Scalar,
  i: E1::Base,
  z0: Vec<E1::Base>,

  zi: Option<Vec<E1::Base>>,
  data_p: Option<FoldingData<E2>>,

  data_c_1: Option<FoldingData<E1>>,
  data_c_2: Option<FoldingData<E1>>,

  E_new: Option<Commitment<E2>>,
  W_new: Option<Commitment<E2>>,
}

impl<E1, E2> AugmentedCircuitInputs<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  pub fn new(
    pp_digest: E1::Scalar,
    i: E1::Base,
    z0: Vec<E1::Base>,
    zi: Option<Vec<E1::Base>>,
    data_p: Option<FoldingData<E2>>,
    data_c_1: Option<FoldingData<E1>>,
    data_c_2: Option<FoldingData<E1>>,
    E_new: Option<Commitment<E2>>,
    W_new: Option<Commitment<E2>>,
  ) -> Self {
    Self {
      pp_digest,
      i,
      z0,
      zi,
      data_p,
      data_c_1,
      data_c_2,
      E_new,
      W_new,
    }
  }
}
pub struct AugmentedCircuit<'a, E1, E2, SC>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  SC: StepCircuit<E2::Scalar>,
{
  params: &'a AugmentedCircuitParams,
  ro_consts: ROConstantsCircuit<E1>,
  inputs: Option<AugmentedCircuitInputs<E1, E2>>,
  step_circuit: &'a SC,
}

impl<'a, E1, E2, SC> AugmentedCircuit<'a, E1, E2, SC>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  SC: StepCircuit<E2::Scalar>,
{
  pub const fn new(
    params: &'a AugmentedCircuitParams,
    ro_consts: ROConstantsCircuit<E1>,
    inputs: Option<AugmentedCircuitInputs<E1, E2>>,
    step_circuit: &'a SC,
  ) -> Self {
    Self {
      params,
      ro_consts,
      inputs,
      step_circuit,
    }
  }

  fn alloc_witness<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    &self,
    mut cs: CS,
    arity: usize,
  ) -> Result<
    (
      AllocatedNum<E1::Base>,                 // pp_digest
      AllocatedNum<E1::Base>,                 // i
      Vec<AllocatedNum<E1::Base>>,            // z0
      Vec<AllocatedNum<E1::Base>>,            // zi
      emulated::AllocatedFoldingData<E1, E2>, //data_p
      AllocatedFoldingData<E1>,               // data_c_1
      AllocatedFoldingData<E1>,               // data_c_2
      emulated::AllocatedPoint<E1, E2>,       // E_new
      emulated::AllocatedPoint<E1, E2>,       // W_new
    ),
    SynthesisError,
  > {
    let pp_digest = alloc_scalar_as_base::<E1, _>(
      cs.namespace(|| "params"),
      self.inputs.as_ref().map(|inputs| inputs.pp_digest),
    )?;

    let i = AllocatedNum::alloc(cs.namespace(|| "i"), || {
      Ok(
        self
          .inputs
          .as_ref()
          .ok_or(SynthesisError::AssignmentMissing)?
          .i,
      )
    })?;

    let z_0 = (0..arity)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
          Ok(self.inputs.get()?.z0[i])
        })
      })
      .collect::<Result<Vec<AllocatedNum<E1::Base>>, _>>()?;

    // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
    let zero = vec![E1::Base::ZERO; arity];
    let z_i = (0..arity)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
          Ok(self.inputs.get()?.zi.as_ref().unwrap_or(&zero)[i])
        })
      })
      .collect::<Result<Vec<AllocatedNum<E1::Base>>, _>>()?;

    let data_p = emulated::AllocatedFoldingData::alloc(
      cs.namespace(|| "data_p"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_p.as_ref()),
    )?;

    let data_c_1 = AllocatedFoldingData::alloc(
      cs.namespace(|| "data_c_1"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_c_1.as_ref()),
    )?;

    let data_c_2 = AllocatedFoldingData::alloc(
      cs.namespace(|| "data_c_2"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_c_2.as_ref()),
    )?;

    let E_new = emulated::AllocatedPoint::alloc(
      cs.namespace(|| "E_new"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.E_new.as_ref())
        .map(|E_new| E_new.to_coordinates()),
    )?;

    let W_new = emulated::AllocatedPoint::alloc(
      cs.namespace(|| "W_new"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.W_new.as_ref())
        .map(|W_new| W_new.to_coordinates()),
    )?;

    Ok((
      pp_digest, i, z_0, z_i, data_p, data_c_1, data_c_2, E_new, W_new,
    ))
  }

  pub fn synthesize_base_case<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    todo!()
  }

  pub fn synthesize_non_base_case<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    // TODO: It's written down here https://hackmd.io/@mpenciak/HybHrnNFT
    todo!()
  }

  pub fn synthesize<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Base>>, SynthesisError> {
    // TODO: It's written down here https://hackmd.io/@mpenciak/HybHrnNFT
    todo!()
  }
}
