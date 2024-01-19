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
  z0: Vec<E1::Base>,

  zi: Option<Vec<E1::Base>>,
  U_p: Option<RelaxedR1CSInstance<E2>>,
  u_p: Option<R1CSInstance<E2>>,
  T_p: Option<Commitment<E2>>,

  U_c: Option<RelaxedR1CSInstance<E1>>,
  u_c_1: Option<R1CSInstance<E1>>,
  T_c_1: Option<Commitment<E1>>,

  U_c_1: Option<RelaxedR1CSInstance<E1>>,
  u_c_2: Option<R1CSInstance<E1>>,
  T_c_2: Option<Commitment<E1>>,

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
    U_p: Option<RelaxedR1CSInstance<E2>>,
    u_p: Option<R1CSInstance<E2>>,
    T_p: Option<Commitment<E2>>,
    U_c: Option<RelaxedR1CSInstance<E1>>,
    u_c_1: Option<R1CSInstance<E1>>,
    T_c_1: Option<Commitment<E1>>,
    U_c_1: Option<RelaxedR1CSInstance<E1>>,
    u_c_2: Option<R1CSInstance<E1>>,
    T_c_2: Option<Commitment<E1>>,
    E_new: Option<Commitment<E2>>,
    W_new: Option<Commitment<E2>>,
  ) -> Self {
    Self {
      pp_digest,
      i,
      z0,
      zi,
      U_p,
      u_p,
      T_p,
      U_c,
      u_c_1,
      T_c_1,
      U_c_1,
      u_c_2,
      T_c_2,
      E_new,
      W_new,
    }
  }
}

pub struct AugmentedCircuit<'a, E1, E2, SC>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  SC: StepCircuit<E1::Base>,
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
  SC: StepCircuit<E1::Base>,
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

  fn synthesize<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Base>>, SynthesisError> {
    // TODO: It's written down here https://hackmd.io/@mpenciak/HybHrnNFT
    todo!()
  }
}
