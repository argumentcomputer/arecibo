//! This module defines the Nova augmented circuit used for Cyclefold

// FIXME: Make an NIFS instance/proof struct to reduce input and output sizes

use crate::{
  gadgets::{
    ecc::AllocatedPoint,
    r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
  },
  r1cs::{R1CSInstance, RelaxedR1CSInstance},
  traits::{circuit::StepCircuit, Engine, ROConstantsCircuit},
  Commitment,
};

use abomonation_derive::Abomonation;
use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use serde::{Deserialize, Serialize};

/// TODO: docs
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
pub struct FoldingData<E: Engine> {
  U: RelaxedR1CSInstance<E>,
  u: R1CSInstance<E>,
  T: Commitment<E>,
}

impl<E: Engine> FoldingData<E> {
  pub fn new(U: RelaxedR1CSInstance<E>, u: R1CSInstance<E>, T: Commitment<E>) -> Self {
    Self { U, u, T }
  }
}

/// TODO: Docs
#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct AugmentedCircuitInputs<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  pp_digest: E1::Scalar,
  i: E1::Base,
  z0: Vec<E1::Scalar>,

  zi: Option<Vec<E1::Scalar>>,
  data_p: Option<FoldingData<E1>>,

  data_c_1: Option<FoldingData<E2>>,
  data_c_2: Option<FoldingData<E2>>,

  E_new: Option<Commitment<E1>>,
  W_new: Option<Commitment<E1>>,
}

impl<E1, E2> AugmentedCircuitInputs<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  pub fn new(
    pp_digest: E1::Scalar,
    i: E1::Base,
    z0: Vec<E1::Scalar>,
    zi: Option<Vec<E1::Scalar>>,
    data_p: Option<FoldingData<E1>>,
    data_c_1: Option<FoldingData<E2>>,
    data_c_2: Option<FoldingData<E2>>,
    E_new: Option<Commitment<E1>>,
    W_new: Option<Commitment<E1>>,
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
  SC: StepCircuit<E1::Scalar>,
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
  SC: StepCircuit<E1::Scalar>,
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

  // FIXME: Need to actually figure out how to encode wrong-field points and instances
  fn alloc_witness<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    &self,
    mut cs: CS,
    arity: usize,
  ) -> Result<
    (
      AllocatedNum<E1::Base>,           // pp_digest
      AllocatedNum<E1::Base>,           // i
      Vec<AllocatedNum<E1::Base>>,      // z0
      Vec<AllocatedNum<E1::Base>>,      // zi
      AllocatedRelaxedR1CSInstance<E2>, // U_p
      AllocatedR1CSInstance<E2>,        // u_p
      AllocatedPoint<E2>,               // T_p
      AllocatedRelaxedR1CSInstance<E1>, // U_c
      AllocatedR1CSInstance<E1>,        // u_c_1
      AllocatedPoint<E1>,               // T_c_1
      AllocatedRelaxedR1CSInstance<E1>, // U_c_1
      AllocatedR1CSInstance<E1>,        // u_c_2
      AllocatedPoint<E1>,               // T_c_2
      AllocatedPoint<E2>,               // E_new
      AllocatedPoint<E2>,               // W_new
    ),
    SynthesisError,
  > {
    todo!()
  }

  pub fn synthesize<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Scalar>>, SynthesisError> {
    // TODO: It's written down here https://hackmd.io/@mpenciak/HybHrnNFT
    todo!()
  }
}
