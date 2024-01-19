//! This module defines the Cyclefold `RecursiveSNARK` type
//!

use std::marker::PhantomData;

use crate::{
  bellpepper::{r1cs::NovaWitness, solver::SatisfyingAssignment},
  cyclefold::circuit::{CyclefoldCircuit, CyclefoldCircuitInputs},
  errors::NovaError,
  gadgets::utils::scalar_as_base,
  nifs::NIFS,
  r1cs::{CommitmentKeyHint, R1CSInstance, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{circuit::StepCircuit, commitment::CommitmentTrait, Engine, ROConstantsCircuit},
  Commitment, CommitmentKey, DigestComputer, R1CSWithArity, ROConstants, ResourceBuffer,
  SimpleDigestible,
};

use super::nova_circuit::{AugmentedCircuit, AugmentedCircuitInputs, AugmentedCircuitParams};

use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use ff::{PrimeField, PrimeFieldBits};
use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};

/// TODO: docs
#[derive(Clone, PartialEq, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  <E1::Scalar as PrimeField>::Repr: Abomonation,
  <E2::Scalar as PrimeField>::Repr: Abomonation,
)]
pub struct PublicParams<E1, E2, C1>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
{
  F_arity_primary: usize,
  ro_consts_primary: ROConstants<E1>,
  ro_consts_circuit_primary: ROConstantsCircuit<E2>,
  ck_primary: CommitmentKey<E1>,
  circuit_shape_primary: R1CSWithArity<E1>,
  augmented_circuit_params_primary: AugmentedCircuitParams,

  ro_consts_cyclefold: ROConstants<E2>,
  ck_cyclefold: CommitmentKey<E2>,
  circuit_shape_cyclefold: R1CSWithArity<E2>,
  #[abomonation_skip]
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<E1::Scalar>,
  _p: PhantomData<(E1, E2, C1)>,
}

impl<E1, E2, C1> PublicParams<E1, E2, C1>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
{
  /// TODO: docs
  pub fn setup(
    _c_primary: &C1,
    _ck_hint1: &CommitmentKeyHint<E1>,
    _ck_hint_cyclefold: &CommitmentKeyHint<E2>,
  ) -> Self {
    todo!()
  }

  /// TODO: docs
  pub fn digest(&self) -> E1::Scalar {
    self
      .digest
      .get_or_try_init(|| DigestComputer::new(self).digest())
      .cloned()
      .expect("Failure in retrieving digest")
  }

  /// TODO: docs
  pub const fn num_constraints(&self) -> usize {
    todo!()
  }

  /// TODO: docs
  pub const fn num_variables(&self) -> usize {
    todo!()
  }
}

impl<E1, E2, C1> SimpleDigestible for PublicParams<E1, E2, C1>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
{
}

/// TODO: docs
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RecursiveSNARK<E1, E2, C1>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
{
  // Input
  z0_primary: Vec<E1::Scalar>,

  // primary circuit data
  r_W_primary: RelaxedR1CSWitness<E1>,
  r_U_primary: RelaxedR1CSInstance<E1>,
  l_w_primary: R1CSWitness<E1>,
  l_u_primary: R1CSInstance<E1>,

  // cyclefold circuit data
  r_W_cyclefold: RelaxedR1CSWitness<E2>,
  r_U_cyclefold: RelaxedR1CSInstance<E2>,

  // memory buffers for folding steps
  buffer_primary: ResourceBuffer<E1>,
  buffer_cyclefold: ResourceBuffer<E2>,

  i: usize,
  zi_primary: Vec<E1::Scalar>,

  _p: PhantomData<C1>,
}

impl<E1, E2, C1> RecursiveSNARK<E1, E2, C1>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
{
  /// TODO: docs
  pub fn new(
    _pp: &PublicParams<E1, E2, C1>,
    _c_primary: &C1,
    _z0_primary: &[E1::Scalar],
  ) -> Result<Self, NovaError> {
    todo!()
  }

  /// TODO: docs
  pub fn prove_step(
    &mut self,
    pp: &PublicParams<E1, E2, C1>,
    c_primary: &C1,
  ) -> Result<(), NovaError> {
    if self.i == 0 {
      self.i = 1;
      return Ok(());
    }

    let (nifs_primary, r) = NIFS::prove_mut(
      &pp.ck_primary,
      &pp.ro_consts_primary,
      &pp.digest(),
      &pp.circuit_shape_primary.r1cs_shape,
      &mut self.r_U_primary,
      &mut self.r_W_primary,
      &self.l_u_primary,
      &self.l_w_primary,
      &mut self.buffer_primary.T,
      &mut self.buffer_primary.ABC_Z_1,
      &mut self.buffer_primary.ABC_Z_2,
    )?;

    let r_bools = r.to_le_bits().iter().map(|b| Some(*b)).collect::<Vec<_>>();

    let comm_T = Commitment::<E1>::decompress(&nifs_primary.comm_T)?;
    let E_new = self.r_U_primary.comm_E + comm_T * r;

    let W_new = self.l_u_primary.comm_W + self.r_U_primary.comm_W * r;

    let mut cs_cyclefold_E = SatisfyingAssignment::<E2>::with_capacity(
      pp.circuit_shape_cyclefold.r1cs_shape.num_io + 1,
      pp.circuit_shape_cyclefold.r1cs_shape.num_vars,
    );

    let inputs_cyclefold_E: CyclefoldCircuitInputs<E1> = CyclefoldCircuitInputs::new(
      Some(self.r_U_primary.comm_E),
      Some(comm_T),
      Some(E_new),
      r_bools.clone(),
    );

    let circuit_cyclefold_E: CyclefoldCircuit<E1> = CyclefoldCircuit::new(Some(inputs_cyclefold_E));

    let _output_cyclefold_E = circuit_cyclefold_E.synthesize(&mut cs_cyclefold_E);

    let (l_u_cyclefold_E, l_w_cyclefold_E) = cs_cyclefold_E
      .r1cs_instance_and_witness(&pp.circuit_shape_cyclefold.r1cs_shape, &pp.ck_cyclefold)
      .map_err(|_| NovaError::UnSat)?;

    let (nifs_cyclefold_E, (r_U_cyclefold_E, r_W_cyclefold_E), _) = NIFS::prove(
      &pp.ck_cyclefold,
      &pp.ro_consts_cyclefold,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.circuit_shape_cyclefold.r1cs_shape,
      &self.r_U_cyclefold,
      &self.r_W_cyclefold,
      &l_u_cyclefold_E,
      &l_w_cyclefold_E,
    )?;

    let comm_T_E = Commitment::<E2>::decompress(&nifs_cyclefold_E.comm_T)?;

    let mut cs_cyclefold_W = SatisfyingAssignment::<E2>::with_capacity(
      pp.circuit_shape_cyclefold.r1cs_shape.num_io + 1,
      pp.circuit_shape_cyclefold.r1cs_shape.num_vars,
    );

    let inputs_cyclefold_W: CyclefoldCircuitInputs<E1> = CyclefoldCircuitInputs::new(
      Some(self.r_U_primary.comm_W),
      Some(self.l_u_primary.comm_W),
      Some(W_new),
      r_bools,
    );

    let circuit_cyclefold_W: CyclefoldCircuit<E1> = CyclefoldCircuit::new(Some(inputs_cyclefold_W));

    let _output_cyclefold_W = circuit_cyclefold_W.synthesize(&mut cs_cyclefold_W);

    let (l_u_cyclefold_W, l_w_cyclefold_W) = cs_cyclefold_W
      .r1cs_instance_and_witness(&pp.circuit_shape_cyclefold.r1cs_shape, &pp.ck_cyclefold)
      .map_err(|_| NovaError::UnSat)?;

    let (nifs_cyclefold_E, (r_U_cyclefold_W, r_W_cyclefold_W), _) = NIFS::prove(
      &pp.ck_cyclefold,
      &pp.ro_consts_cyclefold,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.circuit_shape_cyclefold.r1cs_shape,
      &r_U_cyclefold_E,
      &r_W_cyclefold_E,
      &l_u_cyclefold_W,
      &l_w_cyclefold_W,
    )?;

    let comm_T_W = Commitment::<E2>::decompress(&nifs_cyclefold_E.comm_T)?;

    let mut cs_primary = SatisfyingAssignment::<E1>::with_capacity(
      pp.circuit_shape_primary.r1cs_shape.num_io + 1,
      pp.circuit_shape_primary.r1cs_shape.num_vars,
    );

    // TODO: Finish this method

    todo!()
  }

  /// TODO: docs
  pub fn verify(
    &self,
    _pp: &PublicParams<E1, E2, C1>,
    _num_steps: usize,
    _z0_primary: &[E1::Scalar],
  ) -> Result<Vec<E1::Scalar>, NovaError> {
    todo!()
  }
}

#[cfg(test)]
mod test {
  // use super::*;
}
