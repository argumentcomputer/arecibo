use crate::constants::{BN_N_LIMBS, NIO_CYCLE_FOLD, NUM_FE_IN_EMULATED_POINT, NUM_HASH_BITS};
use crate::cyclefold::gadgets::emulated::AllocatedEmulRelaxedR1CSInstance;
use crate::cyclefold::gadgets::AllocatedCycleFoldData;
use crate::gadgets::{
  alloc_num_equals, alloc_scalar_as_base, alloc_zero, conditionally_select_emul_alloc_relaxed_r1cs,
  conditionally_select_vec_emul_allocated_relaxed_r1cs_instance, le_bits_to_num,
  AllocatedRelaxedR1CSInstance,
};
use crate::supernova::cyclefold::gadgets::emulated as supernova_emulated;
use itertools::Itertools as _;

use crate::supernova::utils::get_selector_vec_from_index;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::ROCircuitTrait;
use crate::zip_with;
use crate::{
  cyclefold::{gadgets::emulated, util::FoldingData},
  supernova::circuit::EnforcingStepCircuit,
  traits::{Engine, ROConstantsCircuit},
  Commitment,
};
use abomonation_derive::Abomonation;
use bellpepper::gadgets::boolean_utils::conditionally_select_slice;
use bellpepper::gadgets::Assignment;
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::Field;
use serde::{Deserialize, Serialize};

use super::gadgets::emulated::SuperNovaAllocatedFoldingData;
use super::util::SuperNovaFoldingData;
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
pub struct SuperNovaAugmentedCircuitParams {
  limb_width: usize,
  n_limbs: usize,
}

impl SuperNovaAugmentedCircuitParams {
  pub const fn new(limb_width: usize, n_limbs: usize) -> Self {
    Self {
      limb_width,
      n_limbs,
    }
  }
}

#[derive(Debug)]
pub struct SuperNovaAugmentedCircuitInputs<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  pp_digest: E1::Scalar,
  i: E1::Base,

  /// Input to the circuit for the base case
  z0: Vec<E1::Base>,
  /// Input to the circuit for the non-base case
  zi: Option<Vec<E1::Base>>,

  data_p: Option<SuperNovaFoldingData<E2>>,

  data_c_1: Option<FoldingData<E1>>,
  data_c_2: Option<FoldingData<E1>>,

  E_new: Option<Commitment<E2>>,
  W_new: Option<Commitment<E2>>,

  /// Index of the current circuit
  program_counter: Option<E1::Base>,
  /// Index j of circuit being folded into U[j]
  last_augmented_circuit_index: E1::Base,
}

impl<E1, E2> SuperNovaAugmentedCircuitInputs<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  pub fn new(
    pp_digest: E1::Scalar,
    i: E1::Base,
    z0: Vec<E1::Base>,
    zi: Option<Vec<E1::Base>>,
    data_p: Option<SuperNovaFoldingData<E2>>,
    data_c_1: Option<FoldingData<E1>>,
    data_c_2: Option<FoldingData<E1>>,
    E_new: Option<Commitment<E2>>,
    W_new: Option<Commitment<E2>>,
    program_counter: Option<E1::Base>,
    last_augmented_circuit_index: E1::Base,
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
      program_counter,
      last_augmented_circuit_index,
    }
  }
}

pub struct SuperNovaAugmentedCircuit<'a, E1, E2, SC>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  SC: EnforcingStepCircuit<E2::Scalar>,
{
  params: &'a SuperNovaAugmentedCircuitParams,
  ro_consts: ROConstantsCircuit<E1>,
  inputs: Option<SuperNovaAugmentedCircuitInputs<E1, E2>>,
  step_circuit: &'a SC,          // The function that is applied for each step
  num_augmented_circuits: usize, // number of overall augmented circuits
}

impl<'a, E1, E2, SC> SuperNovaAugmentedCircuit<'a, E1, E2, SC>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  SC: EnforcingStepCircuit<E2::Scalar>,
{
  pub fn new(
    params: &'a SuperNovaAugmentedCircuitParams,
    inputs: Option<SuperNovaAugmentedCircuitInputs<E1, E2>>,
    step_circuit: &'a SC,
    ro_consts: ROConstantsCircuit<E1>,
    num_augmented_circuits: usize,
  ) -> Self {
    Self {
      params,
      ro_consts,
      inputs,
      step_circuit,
      num_augmented_circuits,
    }
  }

  fn alloc_witness<CS: ConstraintSystem<E1::Base>>(
    &self,
    mut cs: CS,
    arity: usize,
    num_augmented_circuits: usize,
  ) -> Result<
    (
      AllocatedNum<E1::Base>,                                // pp_digest
      AllocatedNum<E1::Base>,                                // i
      Vec<AllocatedNum<E1::Base>>,                           // z0
      Vec<AllocatedNum<E1::Base>>,                           // zi
      supernova_emulated::SuperNovaAllocatedFoldingData<E1>, // data_p
      AllocatedCycleFoldData<E1>,                            // data_c_1
      AllocatedCycleFoldData<E1>,                            // data_c_2
      emulated::AllocatedEmulPoint<E1::GE>,                  // E_new
      emulated::AllocatedEmulPoint<E1::GE>,                  // W_new
      AllocatedNum<E1::Base>,                                // program_counter
      Vec<Boolean>,                                          // last_augmented_circuit_selector
    ),
    SynthesisError,
  > {
    let limb_width = self.params.limb_width;
    let n_limbs = self.params.n_limbs;

    let pp_digest = alloc_scalar_as_base::<E1, _>(
      cs.namespace(|| "params"),
      self.inputs.as_ref().map(|inputs| inputs.pp_digest),
    )?;

    let i = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(self.inputs.get()?.i))?;

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

    let data_p = SuperNovaAllocatedFoldingData::<E1>::alloc(
      cs.namespace(|| "data_p"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_p.as_ref()),
      limb_width,
      n_limbs,
      num_augmented_circuits,
    )?;

    // x: <E1::Base> & y: <E1::Base> coords stored as E1::Bases
    let data_c_1 = AllocatedCycleFoldData::alloc(
      cs.namespace(|| "data_c_1"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_c_1.as_ref()),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    // x: <E1::Base> & y: <E1::Base> coords stored as E1::Bases
    let data_c_2 = AllocatedCycleFoldData::alloc(
      cs.namespace(|| "data_c_2"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_c_2.as_ref()),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    // Allocate E2::Bases as BigNats<E1::Bases>
    let E_new: emulated::AllocatedEmulPoint<<E1 as Engine>::GE> =
      emulated::AllocatedEmulPoint::alloc(
        cs.namespace(|| "E_new"),
        self
          .inputs
          .as_ref()
          .and_then(|inputs| inputs.E_new.as_ref())
          .map(|E_new| E_new.to_coordinates()),
        self.params.limb_width,
        self.params.n_limbs,
      )?;

    // Allocate E2::Bases as BigNats<E1::Bases>
    let W_new: emulated::AllocatedEmulPoint<<E1 as Engine>::GE> =
      emulated::AllocatedEmulPoint::alloc(
        cs.namespace(|| "W_new"),
        self
          .inputs
          .as_ref()
          .and_then(|inputs| inputs.W_new.as_ref())
          .map(|W_new| W_new.to_coordinates()),
        self.params.limb_width,
        self.params.n_limbs,
      )?;

    // Allocate program_counter
    let program_counter = AllocatedNum::alloc(cs.namespace(|| "program_counter"), || {
      Ok(
        self
          .inputs
          .get()?
          .program_counter
          .expect("program_counter missing"),
      )
    })?;

    let last_augmented_circuit_index =
      AllocatedNum::alloc(cs.namespace(|| "last_augmented_circuit_index"), || {
        Ok(self.inputs.get()?.last_augmented_circuit_index)
      })?;

    // Compute instance selector
    let last_augmented_circuit_selector = get_selector_vec_from_index(
      cs.namespace(|| "instance selector"),
      &last_augmented_circuit_index,
      num_augmented_circuits,
    )?;

    Ok((
      pp_digest,
      i,
      z_0,
      z_i,
      data_p,
      data_c_1,
      data_c_2,
      E_new,
      W_new,
      program_counter,
      last_augmented_circuit_selector,
    ))
  }

  pub fn synthesize_base_case<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<
    (
      AllocatedRelaxedR1CSInstance<E1, NIO_CYCLE_FOLD>,
      Vec<emulated::AllocatedEmulRelaxedR1CSInstance<E1>>,
    ),
    SynthesisError,
  > {
    // x: <E1::Base> & y: <E1::Base> coords stored as E1::Bases
    let U_c_default = AllocatedRelaxedR1CSInstance::default(
      cs.namespace(|| "Allocate U_c_default"),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    // Allocate E2::Bases as BigNats<E1::Bases>
    let U_p_default = (0..self.num_augmented_circuits)
      .map(|i| {
        emulated::AllocatedEmulRelaxedR1CSInstance::default(
          cs.namespace(|| format!("Allocated U_p_default {}", i)),
          self.params.limb_width,
          self.params.n_limbs,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    // In the first folding step return the default relaxed instances for both the CycleFold and
    // primary running accumulators
    Ok((U_c_default, U_p_default))
  }

  pub fn synthesize_non_base_case<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    &self,
    mut cs: CS,
    pp_digest: &AllocatedNum<E1::Base>,
    i: &AllocatedNum<E1::Base>,
    z_0: &[AllocatedNum<E1::Base>],
    z_i: &[AllocatedNum<E1::Base>],
    data_p: &SuperNovaAllocatedFoldingData<E1>,
    data_c_1: &AllocatedCycleFoldData<E1>,
    data_c_2: &AllocatedCycleFoldData<E1>,
    E_new: emulated::AllocatedEmulPoint<E1::GE>,
    W_new: emulated::AllocatedEmulPoint<E1::GE>,
    arity: usize,
    last_augmented_circuit_selector: &[Boolean],
    program_counter: &AllocatedNum<E1::Base>,
  ) -> Result<
    (
      AllocatedRelaxedR1CSInstance<E1, NIO_CYCLE_FOLD>,
      Vec<emulated::AllocatedEmulRelaxedR1CSInstance<E1>>,
      AllocatedBit,
    ),
    SynthesisError,
  > {
    // Calculate the first component of the public IO as the hash of the calculated primary running
    // instance
    // Compute the new hash H(params, i+1, program_counter, z0, z_{i+1}, U_next)
    let mut ro = E1::ROCircuit::new(
      self.ro_consts.clone(),
      2 + 2 * arity + self.num_augmented_circuits * (2 * NUM_FE_IN_EMULATED_POINT + 3) + 1, // pp + i + z_0 + z_next + (U_p) + pc
    );
    ro.absorb(pp_digest);
    ro.absorb(i);
    // optionally absorb program counter if exist
    ro.absorb(program_counter);
    for e in z_0 {
      ro.absorb(e);
    }
    for e in z_i {
      ro.absorb(e);
    }

    data_p.U.iter().enumerate().try_for_each(|(i, U)| {
      U.absorb_in_ro(cs.namespace(|| format!("absorb U_new {:?}", i)), &mut ro)
    })?;

    let hash_p_bits = ro.squeeze(cs.namespace(|| "output hash bits"), NUM_HASH_BITS)?;
    let hash_p = le_bits_to_num(cs.namespace(|| "convert hash to num"), &hash_p_bits)?;

    let check_primary = alloc_num_equals(
      cs.namespace(|| "u.X[0] = H(params, i, z0, zi, U_p)"),
      &data_p.u_x0,
      &hash_p,
    )?;

    // Calculate the hash of the non-dterministic advice for the secondary circuit
    let mut ro_c = E1::ROCircuit::new(
      self.ro_consts.clone(),
      1 + 1 + 3 + 3 + 1 + NIO_CYCLE_FOLD * BN_N_LIMBS, // pp + i + W + E + u + X
    );

    ro_c.absorb(pp_digest);
    ro_c.absorb(i);
    data_c_1
      .U
      .absorb_in_ro(cs.namespace(|| "absorb U_c"), &mut ro_c)?;
    let hash_c_bits = ro_c.squeeze(cs.namespace(|| "cyclefold hash bits"), NUM_HASH_BITS)?;
    let hash_c = le_bits_to_num(cs.namespace(|| "cyclefold hash"), &hash_c_bits)?;

    // check the hash matches the public IO from the last primary instance
    let check_cyclefold = alloc_num_equals(
      cs.namespace(|| "u.X[1] = H(params, U_c)"),
      &data_p.u_x1,
      &hash_c,
    )?;

    let check_io = AllocatedBit::and(
      cs.namespace(|| "both IOs match"),
      &check_primary,
      &check_cyclefold,
    )?;

    // Run NIVC.V on U_c, u_c_1, T_c_1
    let U_int = data_c_1.apply_fold(
      cs.namespace(|| "fold u_c_1 into U_c"),
      pp_digest,
      self.ro_consts.clone(),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    // Calculate h_int = H(pp, U_c_int)
    let mut ro_c_int = E1::ROCircuit::new(
      self.ro_consts.clone(),
      1 + 3 + 3 + 1 + NIO_CYCLE_FOLD * BN_N_LIMBS, // pp + W + E + u + X
    );
    ro_c_int.absorb(pp_digest);
    U_int.absorb_in_ro(cs.namespace(|| "absorb U_c_int"), &mut ro_c_int)?;
    let h_c_int_bits =
      ro_c_int.squeeze(cs.namespace(|| "intermediate hash bits"), NUM_HASH_BITS)?;
    let h_c_int = le_bits_to_num(cs.namespace(|| "intermediate hash"), &h_c_int_bits)?;

    // Calculate h_1 = H(pp, U_c_1)
    let mut ro_c_1 = E1::ROCircuit::new(
      self.ro_consts.clone(),
      1 + 3 + 3 + 1 + NIO_CYCLE_FOLD * BN_N_LIMBS, // pp + W + E + u + X
    );

    ro_c_1.absorb(pp_digest);
    data_c_2
      .U
      .absorb_in_ro(cs.namespace(|| "absorb U_c_1"), &mut ro_c_1)?;
    let h_c_1_bits = ro_c_1.squeeze(cs.namespace(|| "cyclefold_1 hash bits"), NUM_HASH_BITS)?;
    let h_c_1 = le_bits_to_num(cs.namespace(|| "cyclefold_1 hash"), &h_c_1_bits)?;

    // Check the intermediate-calculated running instance matches the non-deterministic advice provided to the prover
    let check_cyclefold_int = alloc_num_equals(cs.namespace(|| "h_int = h_c_1"), &h_c_int, &h_c_1)?;

    let checks_pass = AllocatedBit::and(
      cs.namespace(|| "all checks passed"),
      &check_io,
      &check_cyclefold_int,
    )?;

    // calculate the folded CycleFold accumulator
    let U_c = data_c_2.apply_fold(
      cs.namespace(|| "fold u_c_2 into U_c_1"),
      pp_digest,
      self.ro_consts.clone(),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    // Run NIFS Verifier
    let U_to_fold = data_p.U_to_fold(
      cs.namespace(|| "data_p.U_to_fold"),
      last_augmented_circuit_selector,
    )?;

    let U_p = U_to_fold.fold_with_r1cs(
      cs.namespace(|| "compute fold of U and u"),
      pp_digest,
      W_new,
      E_new,
      &data_p.u_W,
      &data_p.u_x0,
      &data_p.u_x1,
      &data_p.T,
      self.ro_consts.clone(),
    )?;

    // update AllocatedRelaxedR1CSInstance on index match augmented circuit index
    let U_next: Vec<AllocatedEmulRelaxedR1CSInstance<E1>> = zip_with!(
      (data_p.U.iter(), last_augmented_circuit_selector.iter()),
      |U, equal_bit| {
        conditionally_select_emul_alloc_relaxed_r1cs(
          cs.namespace(|| "select on index namespace"),
          &U_p,
          U,
          equal_bit,
        )
      }
    )
    .collect::<Result<Vec<AllocatedEmulRelaxedR1CSInstance<E1>>, _>>()?;

    Ok((U_c, U_next, checks_pass))
  }

  pub fn synthesize<CS: ConstraintSystem<E1::Base>>(
    &self,
    cs: &mut CS,
  ) -> Result<(Option<AllocatedNum<E1::Base>>, Vec<AllocatedNum<E1::Base>>), SynthesisError> {
    let arity = self.step_circuit.arity();

    // Allocate the witness
    let (
      pp_digest,
      i,
      z_0,
      z_i,
      data_p,
      data_c_1,
      data_c_2,
      E_new,
      W_new,
      program_counter,
      last_augmented_circuit_selector,
    ) = self.alloc_witness(
      cs.namespace(|| "alloc_witness"),
      arity,
      self.num_augmented_circuits,
    )?;

    // Check if i is 0
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let is_base_case = alloc_num_equals(cs.namespace(|| "is base case"), &i, &zero)?;

    // Get base case default values for running instances
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
      E_new,
      W_new,
      arity,
      &last_augmented_circuit_selector,
      &program_counter,
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

    // Compute the U_next
    let Unew_p = conditionally_select_vec_emul_allocated_relaxed_r1cs_instance(
      cs.namespace(|| "U_next"),
      &Unew_p_base[..],
      &Unew_p_non_base[..],
      &Boolean::from(is_base_case.clone()),
    )?;

    // select the new running CycleFold instance
    let Unew_c = Unew_c_base.conditionally_select(
      cs.namespace(|| "compute Unew_c"),
      &Unew_c_non_base,
      &Boolean::from(is_base_case.clone()),
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
    let z_input = conditionally_select_slice(
      cs.namespace(|| "select input to F"),
      &z_0,
      &z_i,
      &Boolean::from(is_base_case),
    )?;

    let (program_counter_new, z_next) = self.step_circuit.enforcing_synthesize(
      &mut cs.namespace(|| "F"),
      Some(&program_counter),
      &z_input,
    )?;

    if z_next.len() != arity {
      return Err(SynthesisError::IncompatibleLengthVector(
        "z_next".to_string(),
      ));
    }

    // Calculate the first component of the public IO as the hash of the calculated primary running
    // instance
    // Compute the new hash H(params, i+1, program_counter, z0, z_{i+1}, U_next)
    let mut ro = E1::ROCircuit::new(
      self.ro_consts.clone(),
      2 + 2 * arity + self.num_augmented_circuits * (2 * NUM_FE_IN_EMULATED_POINT + 3) + 1, // pp + i + z_0 + z_next + (U_p) + pc
    );
    ro.absorb(&pp_digest);
    ro.absorb(&i_new);

    // optionally absorb program counter if exist
    ro.absorb(
      program_counter_new
        .as_ref()
        .expect("new program counter missing"),
    );

    for e in &z_0 {
      ro.absorb(e);
    }
    for e in &z_next {
      ro.absorb(e);
    }

    Unew_p.iter().enumerate().try_for_each(|(i, U)| {
      U.absorb_in_ro(cs.namespace(|| format!("absorb U_new {:?}", i)), &mut ro)
    })?;

    let hash_p_bits = ro.squeeze(cs.namespace(|| "output hash bits"), NUM_HASH_BITS)?;
    let hash_p = le_bits_to_num(cs.namespace(|| "convert hash to num"), &hash_p_bits)?;

    // Calculate the second component of the public IO as the hash of the calculated CycleFold running
    // instance
    let mut ro_c = E1::ROCircuit::new(
      self.ro_consts.clone(),
      1 + 1 + 3 + 3 + 1 + NIO_CYCLE_FOLD * BN_N_LIMBS, // pp + i + W + E + u + X
    );
    ro_c.absorb(&pp_digest);
    ro_c.absorb(&i_new);
    Unew_c.absorb_in_ro(cs.namespace(|| "absorb Unew_c"), &mut ro_c)?;
    let hash_c_bits = ro_c.squeeze(cs.namespace(|| "hash_c_bits"), NUM_HASH_BITS)?;
    let hash_c = le_bits_to_num(cs.namespace(|| "hash_c"), &hash_c_bits)?;

    hash_p.inputize(cs.namespace(|| "u_p.x[0] = hash_p"))?;
    hash_c.inputize(cs.namespace(|| "u_p.x[1] = hash_c"))?;

    Ok((program_counter_new, z_next))
  }
}
