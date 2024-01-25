//! This module defines the Nova augmented circuit used for Cyclefold

use crate::{
  constants::{NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS},
  gadgets::{
    r1cs::AllocatedRelaxedR1CSInstance,
    utils::{
      alloc_num_equals, alloc_scalar_as_base, alloc_zero, conditionally_select_vec, le_bits_to_num,
    },
  },
  r1cs::{R1CSInstance, RelaxedR1CSInstance},
  traits::{
    circuit::StepCircuit, commitment::CommitmentTrait, Engine, ROCircuitTrait, ROConstantsCircuit,
  },
  Commitment,
};

use abomonation_derive::Abomonation;
use bellpepper::gadgets::{boolean::Boolean, num::AllocatedNum, Assignment};
use bellpepper_core::{boolean::AllocatedBit, ConstraintSystem, SynthesisError};
use ff::Field;
use serde::{Deserialize, Serialize};

use super::gadgets::{emulated, AllocatedFoldingData};

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

// TODO: This needs to take in the initial cyclefold relaxed R1CS instance as well
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
    &self,
    mut cs: CS,
  ) -> Result<
    (
      AllocatedRelaxedR1CSInstance<E1>,
      emulated::AllocatedRelaxedR1CSInstance<E1, E2>,
    ),
    SynthesisError,
  > {
    let U_c_default = AllocatedRelaxedR1CSInstance::default(
      cs.namespace(|| "Allocate U_c_default"),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let U_p_default = emulated::AllocatedRelaxedR1CSInstance::default(
      cs.namespace(|| "Allocated U_p_default"),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    Ok((U_c_default, U_p_default))
  }

  pub fn synthesize_non_base_case<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    &self,
    mut cs: CS,
    pp_digest: &AllocatedNum<E1::Base>,
    i: &AllocatedNum<E1::Base>,
    z_0: &[AllocatedNum<E1::Base>],
    z_i: &[AllocatedNum<E1::Base>],
    data_p: &emulated::AllocatedFoldingData<E1, E2>,
    data_c_1: &AllocatedFoldingData<E1>,
    data_c_2: &AllocatedFoldingData<E1>,
    E_new: &emulated::AllocatedPoint<E1, E2>,
    W_new: &emulated::AllocatedPoint<E1, E2>,
    arity: usize,
  ) -> Result<
    (
      AllocatedRelaxedR1CSInstance<E1>,
      emulated::AllocatedRelaxedR1CSInstance<E1, E2>,
      AllocatedBit,
    ),
    SynthesisError,
  > {
    // Follows the outline written down here https://hackmd.io/@mpenciak/HybHrnNFT
    let mut ro_p = E1::ROCircuit::new(
      self.ro_consts.clone(),
      NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity,
    );

    ro_p.absorb(pp_digest);
    ro_p.absorb(i);
    for e in z_0 {
      ro_p.absorb(e)
    }
    for e in z_i {
      ro_p.absorb(e)
    }
    data_p
      .U
      .absorb_in_ro(cs.namespace(|| "absorb U_p"), &mut ro_p)?;

    let hash_bits_p = ro_p.squeeze(cs.namespace(|| "primary hash bits"), NUM_HASH_BITS)?;
    let hash_p = le_bits_to_num(cs.namespace(|| "primary hash"), &hash_bits_p)?;

    let x_0 = data_p
      .u_x0
      .as_allocated_num(cs.namespace(|| "u.x[0] as AllocatedNum"))?;

    let check_primary = alloc_num_equals(
      cs.namespace(|| "u.X[0] = H(params, i, z0, zi, U_p)"),
      &x_0,
      &hash_p,
    )?;

    let mut ro_c = E1::ROCircuit::new(self.ro_consts.clone(), NUM_FE_WITHOUT_IO_FOR_CRHF);

    ro_c.absorb(pp_digest);
    data_c_1
      .U
      .absorb_in_ro(cs.namespace(|| "absorb U_c"), &mut ro_c)?;
    let hash_c_bits = ro_c.squeeze(cs.namespace(|| "cyclefold hash bits"), NUM_HASH_BITS)?;
    let hash_c = le_bits_to_num(cs.namespace(|| "cyclefold hash"), &hash_c_bits)?;

    let x_1 = data_p
      .u_x1
      .as_allocated_num(cs.namespace(|| "u.x[1] as AllocatedNum"))?;

    let check_cyclefold =
      alloc_num_equals(cs.namespace(|| "u.X[1] = H(params, U_c)"), &x_1, &hash_c)?;

    let check_io = AllocatedBit::and(
      cs.namespace(|| "both IOs match"),
      &check_primary,
      &check_cyclefold,
    )?;

    // Run NIVC.V on U_c, u_c_1, T_c_1
    let U_int = data_c_1.U.fold_with_r1cs(
      cs.namespace(|| "U_int = fold U_c with u_c_1"),
      pp_digest,
      &data_c_1.u,
      &data_c_1.T,
      self.ro_consts.clone(),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    // Calculate h_int = H(pp, U_c_int)
    let mut ro_c_int = E1::ROCircuit::new(self.ro_consts.clone(), NUM_FE_WITHOUT_IO_FOR_CRHF);
    ro_c_int.absorb(pp_digest);
    U_int.absorb_in_ro(cs.namespace(|| "absorb U_c_int"), &mut ro_c_int)?;
    let h_c_int_bits =
      ro_c_int.squeeze(cs.namespace(|| "intermediate hash bits"), NUM_HASH_BITS)?;
    let h_c_int = le_bits_to_num(cs.namespace(|| "intermediate hash"), &h_c_int_bits)?;

    // Calculate h_1 = H(pp, U_c_1)
    let mut ro_c_1 = E1::ROCircuit::new(self.ro_consts, NUM_FE_WITHOUT_IO_FOR_CRHF);
    ro_c_1.absorb(pp_digest);
    data_c_2
      .U
      .absorb_in_ro(cs.namespace(|| "absorb U_c_1"), &mut ro_c_1)?;
    let h_c_1_bits = ro_c_1.squeeze(cs.namespace(|| "cyclefold_1 hash bits"), NUM_HASH_BITS)?;
    let h_c_1 = le_bits_to_num(cs.namespace(|| "cyclefold_1 hash"), &h_c_1_bits)?;

    let check_cyclefold_int = alloc_num_equals(cs.namespace(|| "h_int = h_c_1"), &h_c_int, &h_c_1)?;

    let checks_pass = AllocatedBit::and(
      cs.namespace(|| "all checks passed"),
      &check_io,
      &check_cyclefold_int,
    )?;

    let U_c = data_c_2.U.fold_with_r1cs(
      cs.namespace(|| "U_c = fold U_c_1 with u_c_2"),
      pp_digest,
      &data_c_2.u,
      &data_c_2.T,
      self.ro_consts.clone(),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let U_p = data_p.U.fold_with_r1cs(
      cs.namespace(|| "fold u_p into U_p"),
      W_new.clone(),
      E_new.clone(),
      &data_p.u_x0,
      &data_p.u_x1,
      self.ro_consts.clone(),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    Ok((U_c, U_p, checks_pass))
  }

  pub fn synthesize<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Base>>, SynthesisError> {
    // TODO: It's written down here https://hackmd.io/@mpenciak/HybHrnNFT
    let arity = self.step_circuit.arity();

    let (pp_digest, i, z_0, z_i, data_p, data_c_1, data_c_2, E_new, W_new) =
      self.alloc_witness(cs.namespace(|| "alloc_witness"), self.params.n_limbs)?;

    let zero = alloc_zero(cs.namespace(|| "zero"));
    let is_base_case = alloc_num_equals(cs.namespace(|| "is base case"), &i, &zero)?;

    let (Unew_c_base, Unew_p_base) = self.synthesize_base_case(cs.namespace(|| "base case"))?;

    let (Unew_c_non_base, Unew_p_non_base, check_non_base_pass) = self.synthesize_non_base_case(
      cs.namespace(|| "synthesize non base case"),
      &pp_digest,
      &i,
      &z_0,
      &z_i,
      &data_p,
      &data_c_1,
      &data_c_2,
      &E_new,
      &W_new,
      arity,
    )?;

    let should_be_false = AllocatedBit::nor(
      cs.namespace(|| "check_non_base_pass nor base_case"),
      &check_non_base_pass,
      &is_base_case,
    )?;
    cs.enforce(
      || "check_non_base_pass nor base_case = false",
      |lc| lc + should_be_false.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );

    let is_base_case_bool = Boolean::from(is_base_case.clone());

    let Unew_p = Unew_p_base.conditionally_select(
      cs.namespace(|| "compute Unew_p"),
      &Unew_p_non_base,
      &is_base_case_bool,
    )?;

    let Unew_c = Unew_c_base.conditionally_select(
      cs.namespace(|| "compute Unew_c"),
      &Unew_c_non_base,
      &is_base_case_bool,
    )?;

    // Compute i + 1
    let i_new = AllocatedNum::alloc(cs.namespace(|| "i + 1"), || {
      Ok(*i.get_value().get()? + E1::Base::ONE)
    })?;
    cs.enforce(
      || "check i + 1",
      |lc| lc,
      |lc| lc,
      |lc| lc + i_new.get_variable() - CS::one() - i.get_variable(),
    );

    // Compute z_{i+1}
    let z_input = conditionally_select_vec(
      cs.namespace(|| "select input to F"),
      &z_0,
      &z_i,
      &Boolean::from(is_base_case),
    )?;

    let z_next = self
      .step_circuit
      .synthesize(&mut cs.namespace(|| "F"), &z_input)?;

    if z_next.len() != arity {
      return Err(SynthesisError::IncompatibleLengthVector(
        "z_next".to_string(),
      ));
    }

    let mut ro_p = E1::ROCircuit::new(
      self.ro_consts.clone(),
      NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity,
    );
    ro_p.absorb(&pp_digest);
    ro_p.absorb(&i_new);
    for e in &z_0 {
      ro_p.absorb(e);
    }
    for e in &z_next {
      ro_p.absorb(e);
    }
    Unew_p.absorb_in_ro(cs.namespace(|| "absorb Unew_p"), &mut ro_p)?;
    let hash_p_bits = ro_p.squeeze(cs.namespace(|| "hash_p_bits"), NUM_HASH_BITS)?;
    let hash_p = le_bits_to_num(cs.namespace(|| "hash_p"), &hash_p_bits)?;

    let mut ro_c = E1::ROCircuit::new(self.ro_consts, NUM_FE_WITHOUT_IO_FOR_CRHF);
    ro_c.absorb(&pp_digest);
    Unew_c.absorb_in_ro(cs.namespace(|| "absorb Unew_c"), &mut ro_c)?;
    let hash_c_bits = ro_c.squeeze(cs.namespace(|| "hash_c_bits"), NUM_HASH_BITS)?;
    let hash_c = le_bits_to_num(cs.namespace(|| "hash_c"), &hash_c_bits)?;

    hash_p.inputize(cs.namespace(|| "u_p.x[0] = hash_p"))?;
    hash_c.inputize(cs.namespace(|| "u_p.x[1] = hash_c"))?;

    Ok(z_next)
  }
}
