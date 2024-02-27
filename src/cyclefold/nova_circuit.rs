//! This module defines the Nova augmented circuit used for Cyclefold

use crate::{
  constants::{
    BN_N_LIMBS, NIO_CYCLE_FOLD, NUM_FE_IN_EMULATED_POINT,
    /*NUM_FE_WITHOUT_IO_FOR_CRHF,*/ NUM_HASH_BITS,
  },
  gadgets::{
    r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
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
use itertools::{chain, Itertools};
use serde::{Deserialize, Serialize};

use super::gadgets::{emulated, AllocatedFoldingData};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
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
  pub U: RelaxedR1CSInstance<E>,
  pub u: R1CSInstance<E>,
  pub T: Commitment<E>,
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
      AllocatedNum<E1::Base>,                   // pp_digest
      AllocatedNum<E1::Base>,                   // i
      Vec<AllocatedNum<E1::Base>>,              // z0
      Vec<AllocatedNum<E1::Base>>,              // zi
      emulated::AllocatedFoldingData<E1>,       //data_p
      AllocatedFoldingData<E1, NIO_CYCLE_FOLD>, // data_c_1
      AllocatedFoldingData<E1, NIO_CYCLE_FOLD>, // data_c_2
      emulated::AllocatedEmulPoint<E1::GE>,     // E_new
      emulated::AllocatedEmulPoint<E1::GE>,     // W_new
    ),
    SynthesisError,
  > {
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

    let data_p = emulated::AllocatedFoldingData::alloc(
      cs.namespace(|| "data_p"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_p.as_ref()),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let data_c_1 = AllocatedFoldingData::alloc(
      cs.namespace(|| "data_c_1"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_c_1.as_ref()),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let data_c_2 = AllocatedFoldingData::alloc(
      cs.namespace(|| "data_c_2"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.data_c_2.as_ref()),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let E_new = emulated::AllocatedEmulPoint::alloc(
      cs.namespace(|| "E_new"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.E_new.as_ref())
        .map(|E_new| E_new.to_coordinates()),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let W_new = emulated::AllocatedEmulPoint::alloc(
      cs.namespace(|| "W_new"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.W_new.as_ref())
        .map(|W_new| W_new.to_coordinates()),
      self.params.limb_width,
      self.params.n_limbs,
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
      AllocatedRelaxedR1CSInstance<E1, NIO_CYCLE_FOLD>,
      emulated::AllocatedEmulRelaxedR1CSInstance<E1>,
    ),
    SynthesisError,
  > {
    let U_c_default = AllocatedRelaxedR1CSInstance::default(
      cs.namespace(|| "Allocate U_c_default"),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    let U_p_default = emulated::AllocatedEmulRelaxedR1CSInstance::default(
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
    data_p: &emulated::AllocatedFoldingData<E1>,
    data_c_1: &AllocatedFoldingData<E1, NIO_CYCLE_FOLD>,
    data_c_2: &AllocatedFoldingData<E1, NIO_CYCLE_FOLD>,
    E_new: emulated::AllocatedEmulPoint<E1::GE>,
    W_new: emulated::AllocatedEmulPoint<E1::GE>,
    arity: usize,
  ) -> Result<
    (
      AllocatedRelaxedR1CSInstance<E1, NIO_CYCLE_FOLD>,
      emulated::AllocatedEmulRelaxedR1CSInstance<E1>,
      AllocatedBit,
    ),
    SynthesisError,
  > {
    // Follows the outline written down here https://hackmd.io/@lurk-lab/HybHrnNFT
    let mut ro_p = E1::ROCircuit::new(
      self.ro_consts.clone(),
      2 + 2 * arity + 2 * NUM_FE_IN_EMULATED_POINT + 3,
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

    let check_primary = alloc_num_equals(
      cs.namespace(|| "u.X[0] = H(params, i, z0, zi, U_p)"),
      &data_p.u_x0,
      &hash_p,
    )?;

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

    let check_cyclefold = alloc_num_equals(
      cs.namespace(|| "u.X[1] = H(params, U_c)"),
      &data_p.u_x1,
      &hash_c,
    )?;

    let u_E = &data_c_1.u;
    let E_1 = &data_p.U.comm_E;
    cyclefold_invocation_check(
      cs.namespace(|| "cyclefold invocation check E"),
      &E_1,
      &data_p.T,
      &E_new,
      u_E,
    )?;

    let u_W = &data_c_2.u;
    let W_1 = &data_p.U.comm_W;
    let W_2 = &data_p.u_W;
    cyclefold_invocation_check(
      cs.namespace(|| "cyclefold invocation check W"),
      &W_1,
      &W_2,
      &W_new,
      u_W,
    )?;

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
      pp_digest,
      W_new,
      E_new,
      &data_p.u_W,
      &data_p.u_x0,
      &data_p.u_x1,
      &data_p.T,
      self.ro_consts.clone(),
    )?;

    Ok((U_c, U_p, checks_pass))
  }

  pub fn synthesize<CS: ConstraintSystem<<E1 as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E1::Base>>, SynthesisError> {
    // TODO: It's written down here https://hackmd.io/SBvAur_2RQmaduDi7gYbhw
    let arity = self.step_circuit.arity();

    let (pp_digest, i, z_0, z_i, data_p, data_c_1, data_c_2, E_new, W_new) =
      self.alloc_witness(cs.namespace(|| "alloc_witness"), arity)?;

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
      E_new,
      W_new,
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

    let Unew_p = Unew_p_base.conditionally_select(
      cs.namespace(|| "compute Unew_p"),
      &Unew_p_non_base,
      &Boolean::from(is_base_case.clone()),
    )?;

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
      2 + 2 * arity + 2 * NUM_FE_IN_EMULATED_POINT + 3,
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

    let mut ro_c = E1::ROCircuit::new(
      self.ro_consts,
      1 + 1 + 3 + 3 + 1 + NIO_CYCLE_FOLD * BN_N_LIMBS,
    ); // pp + i + W + E + u + X
    ro_c.absorb(&pp_digest);
    ro_c.absorb(&i_new);
    Unew_c.absorb_in_ro(cs.namespace(|| "absorb Unew_c"), &mut ro_c)?;
    let hash_c_bits = ro_c.squeeze(cs.namespace(|| "hash_c_bits"), NUM_HASH_BITS)?;
    let hash_c = le_bits_to_num(cs.namespace(|| "hash_c"), &hash_c_bits)?;

    hash_p.inputize(cs.namespace(|| "u_p.x[0] = hash_p"))?;
    hash_c.inputize(cs.namespace(|| "u_p.x[1] = hash_c"))?;

    Ok(z_next)
  }
}

// TODO: Clean this up
pub fn emulated_point_check<E1: Engine, CS: ConstraintSystem<<E1 as Engine>::Base>>(
  mut cs: CS,
  point: &emulated::AllocatedEmulPoint<E1::GE>,
  io_limbs: &[AllocatedNum<<E1 as Engine>::Base>],
) -> Result<(), SynthesisError> {
  let x_limbs = point
    .x
    .group_limbs(BN_N_LIMBS / 2)
    .as_limbs()
    .iter()
    .enumerate()
    .map(|(idx, limb)| limb.as_allocated_num(cs.namespace(|| format!("alloc x_limb[{idx}]"))))
    .collect::<Result<Vec<_>, _>>()?;

  let y_limbs = point
    .y
    .group_limbs(BN_N_LIMBS / 2)
    .as_limbs()
    .iter()
    .enumerate()
    .map(|(idx, limb)| limb.as_allocated_num(cs.namespace(|| format!("alloc y_limb[{idx}]"))))
    .collect::<Result<Vec<_>, _>>()?;

  let is_infinity = AllocatedNum::alloc(cs.namespace(|| "allocate is_infinity"), || {
    if *point.is_infinity.get_value().get()? {
      Ok(<E1 as Engine>::Base::ONE)
    } else {
      Ok(<E1 as Engine>::Base::ZERO)
    }
  })?;

  cs.enforce(
    || "enforcing is_infinity",
    |lc| lc,
    |lc| lc,
    |lc| lc + is_infinity.get_variable() - point.is_infinity.get_variable(),
  );

  let all_variables = chain!(x_limbs, y_limbs, vec![is_infinity]);

  all_variables
    .into_iter()
    .zip_eq(io_limbs)
    .enumerate()
    .try_for_each(|(idx, (var, limb))| -> Result<(), SynthesisError> {
      cs.enforce(
        || format!("enforcing equality {idx}"),
        |lc| lc,
        |lc| lc,
        |lc| lc + var.get_variable() - limb.get_variable(),
      );

      Ok(())
    })?;

  Ok(())
}

// TODO: Clean this up
pub fn cyclefold_invocation_check<E1: Engine, CS: ConstraintSystem<<E1 as Engine>::Base>>(
  mut cs: CS,
  C_1: &emulated::AllocatedEmulPoint<E1::GE>,
  C_2: &emulated::AllocatedEmulPoint<E1::GE>,
  C_res: &emulated::AllocatedEmulPoint<E1::GE>,
  instance: &AllocatedR1CSInstance<E1, NIO_CYCLE_FOLD>,
) -> Result<(), SynthesisError> {
  let (point_1_io, point_23_io) = instance.X.split_at(5);
  let (point_2_io, point_3_io_plus_scalar) = point_23_io.split_at(5);
  let point_3_io = point_3_io_plus_scalar.split_at(5).0;
  emulated_point_check::<E1, _>(cs.namespace(|| "check point C_1"), C_1, point_1_io)?;
  emulated_point_check::<E1, _>(cs.namespace(|| "check point C_2"), C_2, point_2_io)?;
  emulated_point_check::<E1, _>(cs.namespace(|| "check point C_res"), C_res, point_3_io)?;

  Ok(())
}
#[cfg(test)]
mod test {
  use crate::{
    bellpepper::test_shape_cs::TestShapeCS,
    constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
    provider::{Bn256EngineKZG, PallasEngine, Secp256k1Engine},
    traits::{circuit::TrivialCircuit, CurveCycleEquipped, Dual},
  };

  use super::*;

  fn test_augmented_circuit_size_with<E>()
  where
    E: CurveCycleEquipped,
  {
    let params = AugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS);

    let ro_consts = ROConstantsCircuit::<E>::default();

    let step_circuit = TrivialCircuit::<E::Base>::default();

    let circuit = AugmentedCircuit::<E, Dual<E>, TrivialCircuit<E::Base>>::new(
      &params,
      ro_consts,
      None,
      &step_circuit,
    );
    let mut cs: TestShapeCS<Dual<E>> = TestShapeCS::default();

    let _ = circuit.synthesize(&mut cs);

    let num_constraints = cs.num_constraints();
    let num_variables = cs.num_aux();

    assert_eq!(num_constraints, 0);
    assert_eq!(num_variables, 0);
  }

  #[test]
  fn test_augmented_circuit_size() {
    test_augmented_circuit_size_with::<PallasEngine>();
    test_augmented_circuit_size_with::<Secp256k1Engine>();
    test_augmented_circuit_size_with::<Bn256EngineKZG>();
  }
}
