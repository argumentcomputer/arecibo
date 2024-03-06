//! This module defines Cyclefold stuff

use bellpepper::gadgets::Assignment;
use bellpepper_core::{boolean::AllocatedBit, num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::{
  constants::NUM_CHALLENGE_BITS,
  gadgets::{alloc_constant, le_bits_to_num, AllocatedPoint},
  traits::{commitment::CommitmentTrait, Engine},
  Commitment,
};

/// A structure containing the CycleFold circuit inputs and implementing the synthesize function
pub struct CyclefoldCircuit<E: Engine> {
  commit_1: Option<Commitment<E>>,
  commit_2: Option<Commitment<E>>,
  scalar: Option<[bool; NUM_CHALLENGE_BITS]>,
}

impl<E: Engine> Default for CyclefoldCircuit<E> {
  fn default() -> Self {
    Self {
      commit_1: None,
      commit_2: None,
      scalar: None,
    }
  }
}
impl<E: Engine> CyclefoldCircuit<E> {
  /// Create a new CycleFold circuit with the given inputs
  pub fn new(
    commit_1: Option<Commitment<E>>,
    commit_2: Option<Commitment<E>>,
    scalar: Option<[bool; NUM_CHALLENGE_BITS]>,
  ) -> Self {
    Self {
      commit_1,
      commit_2,
      scalar,
    }
  }

  fn alloc_witness<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<
    (
      AllocatedPoint<E::GE>,
      AllocatedPoint<E::GE>,
      Vec<AllocatedBit>,
    ),
    SynthesisError,
  > {
    let commit_1 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate C_1"),
      self.commit_1.map(|C_1| C_1.to_coordinates()),
    )?;
    commit_1.check_on_curve(cs.namespace(|| "commit_1 on curve"))?;

    let commit_2 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate C_2"),
      self.commit_2.map(|C_2| C_2.to_coordinates()),
    )?;
    commit_2.check_on_curve(cs.namespace(|| "commit_2 on curve"))?;

    let scalar: Vec<AllocatedBit> = self
      .scalar
      .unwrap_or([false; NUM_CHALLENGE_BITS])
      .into_iter()
      .enumerate()
      .map(|(idx, bit)| {
        AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {idx}")), Some(bit))
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok((commit_1, commit_2, scalar))
  }

  /// Synthesize the CycleFold circuit
  pub fn synthesize<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<(), SynthesisError> {
    let (C_1, C_2, r) = self.alloc_witness(cs.namespace(|| "allocate circuit witness"))?;

    // Calculate C_final
    let r_C_2 = C_2.scalar_mul(cs.namespace(|| "r * C_2"), &r)?;

    let C_final = C_1.add(cs.namespace(|| "C_1 + r * C_2"), &r_C_2)?;

    inputize_point::<E, _>(&C_1, cs.namespace(|| "inputize C_1"))?;
    inputize_point::<E, _>(&C_2, cs.namespace(|| "inputize C_2"))?;
    inputize_point::<E, _>(&C_final, cs.namespace(|| "inputize C_final"))?;

    let scalar = le_bits_to_num(cs.namespace(|| "get scalar"), &r)?;

    scalar.inputize(cs.namespace(|| "scalar"))?;

    Ok(())
  }
}

fn inputize_point<E, CS>(point: &AllocatedPoint<E::GE>, mut cs: CS) -> Result<(), SynthesisError>
where
  E: Engine,
  CS: ConstraintSystem<E::Base>,
{
  let (lower_x, upper_x) = split_field_element(&point.x, cs.namespace(|| "split x"))?;
  let (lower_y, upper_y) = split_field_element(&point.y, cs.namespace(|| "split y"))?;
  lower_x.inputize(cs.namespace(|| "inputize lower_x"))?;
  upper_x.inputize(cs.namespace(|| "inputize upper_x"))?;
  lower_y.inputize(cs.namespace(|| "inputize lower_y"))?;
  upper_y.inputize(cs.namespace(|| "inputize upper_y"))?;
  point
    .is_infinity
    .inputize(cs.namespace(|| "inputize is_infinity"))?;
  Ok(())
}

// TODO: Clean this up
fn split_field_element<Scalar, CS>(
  num: &AllocatedNum<Scalar>,
  mut cs: CS,
) -> Result<(AllocatedNum<Scalar>, AllocatedNum<Scalar>), SynthesisError>
where
  Scalar: PrimeField,
  CS: ConstraintSystem<Scalar>,
{
  let lower_allocated_num = AllocatedNum::alloc(cs.namespace(|| "alloc lower"), || {
    let repr = num.get_value().get()?.to_repr();
    let bytes = repr.as_ref();
    let (lower, _) = bytes.split_at(16);
    Ok(Scalar::from_u128(u128::from_le_bytes(
      (*lower).try_into().unwrap(),
    )))
  })?;
  let upper_allocated_num = AllocatedNum::alloc(cs.namespace(|| "alloc upper"), || {
    let repr = num.get_value().get()?.to_repr();
    let bytes = repr.as_ref();
    let (_, upper) = bytes.split_at(16);
    Ok(Scalar::from_u128(u128::from_le_bytes(
      (*upper).try_into().unwrap(),
    )))
  })?;

  let shift = alloc_constant(
    Scalar::from_u128(u128::MAX) + Scalar::ONE,
    cs.namespace(|| "alloc shift"),
  );

  let repr = num.get_value().get().map(|v| v.to_repr());

  let shifted_upper_num = repr.map(|v| {
    (0..128).fold(
      Scalar::from_u128(u128::from_le_bytes(
        (*v.as_ref().split_at(16).1).try_into().unwrap(),
      )),
      |acc, _| acc.double(),
    )
  });

  let shifted_upper_allocated_num =
    AllocatedNum::alloc(cs.namespace(|| "alloc shifted_upper"), || shifted_upper_num)?;

  cs.enforce(
    || "enforce shifted_upper is valid",
    |lc| lc + upper_allocated_num.get_variable(),
    |lc| lc + shift.get_variable(),
    |lc| lc + shifted_upper_allocated_num.get_variable(),
  );

  cs.enforce(
    || "enforce split",
    |lc| lc + CS::one(),
    |lc| lc + num.get_variable(),
    |lc| lc + lower_allocated_num.get_variable() + shifted_upper_allocated_num.get_variable(),
  );

  Ok((lower_allocated_num, upper_allocated_num))
}

#[cfg(test)]
mod tests {
  use expect_test::{expect, Expect};
  use ff::{Field, PrimeField, PrimeFieldBits};
  use rand_core::OsRng;

  use crate::{
    bellpepper::{
      r1cs::{NovaShape, NovaWitness},
      shape_cs::ShapeCS,
      solver::SatisfyingAssignment,
    },
    constants::NIO_CYCLE_FOLD,
    provider::{Bn256EngineKZG, PallasEngine, Secp256k1Engine},
    traits::{commitment::CommitmentEngineTrait, snark::default_ck_hint, CurveCycleEquipped, Dual},
  };

  use super::*;

  fn test_cyclefold_circuit_size_with<E1>(expected_constraints: &Expect, expected_vars: &Expect)
  where
    E1: CurveCycleEquipped,
  {
    // Instantiate the circuit with trivial inputs
    let circuit: CyclefoldCircuit<Dual<E1>> = CyclefoldCircuit::new(None, None, None);

    // Synthesize the R1CS shape
    let mut cs: ShapeCS<E1> = ShapeCS::new();
    let _ = circuit.synthesize(cs.namespace(|| "synthesizing shape"));

    // Extract the number of constraints and variables
    let num_constraints = cs.num_constraints();
    let num_variables = cs.num_aux();
    let num_io = cs.num_inputs();

    // Check the number of constraints and variables match the expected values
    expected_constraints.assert_eq(&num_constraints.to_string());
    expected_vars.assert_eq(&num_variables.to_string());
    assert_eq!(num_io, NIO_CYCLE_FOLD + 1); // includes 1
  }

  #[test]
  fn test_cyclefold_circuit_size() {
    test_cyclefold_circuit_size_with::<PallasEngine>(&expect!("1394"), &expect!("1382"));
    test_cyclefold_circuit_size_with::<Bn256EngineKZG>(&expect!("1394"), &expect!("1382"));
    test_cyclefold_circuit_size_with::<Secp256k1Engine>(&expect!("1394"), &expect!("1382"));
  }

  fn test_cyclefold_circuit_sat_with<E: CurveCycleEquipped>() {
    let rng = OsRng;

    let ck = <<Dual<E> as Engine>::CE as CommitmentEngineTrait<Dual<E>>>::setup(b"test", 5);

    // Generate random vectors to commit to
    let v1 = (0..5)
      .map(|_| <<Dual<E> as Engine>::Scalar as Field>::random(rng))
      .collect::<Vec<_>>();
    let v2 = (0..5)
      .map(|_| <<Dual<E> as Engine>::Scalar as Field>::random(rng))
      .collect::<Vec<_>>();

    // Calculate the random commitments
    let C_1 = <<Dual<E> as Engine>::CE as CommitmentEngineTrait<Dual<E>>>::commit(&ck, &v1);
    let C_2 = <<Dual<E> as Engine>::CE as CommitmentEngineTrait<Dual<E>>>::commit(&ck, &v2);

    // Generate a random scalar
    let val: u128 = rand::random();
    let r = <<Dual<E> as Engine>::Scalar as PrimeField>::from_u128(val);
    let r_bits = r
      .to_le_bits()
      .into_iter()
      .map(Some)
      .collect::<Option<Vec<_>>>()
      .map(|mut vec| {
        vec.resize_with(128, || false);
        vec.try_into().unwrap()
      });

    // Calculate the result out of circuit
    let native_result = C_1 + C_2 * r;
    let (res_X, res_Y, res_is_infinity) = native_result.to_coordinates();

    let circuit: CyclefoldCircuit<Dual<E>> = CyclefoldCircuit::new(Some(C_1), Some(C_2), r_bits);

    // Generate the R1CS shape and commitment key
    let mut cs: ShapeCS<E> = ShapeCS::new();
    let _ = circuit.synthesize(cs.namespace(|| "synthesizing shape"));
    let (shape, ck) = cs.r1cs_shape_and_key(&*default_ck_hint());

    // Synthesize the R1CS circuit on the random inputs
    let mut cs = SatisfyingAssignment::<E>::new();
    circuit
      .synthesize(cs.namespace(|| "synthesizing witness"))
      .unwrap();

    let (instance, witness) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();

    let X = &instance.X;

    // Recombine the scalar from the two 128 bit limbs in the public IO of the cyclefold circuit
    let recombine_scalar = |lower: E::Scalar, upper: E::Scalar| -> E::Scalar {
      let mut upper = upper;
      (0..128).for_each(|_| upper = upper.double());
      lower + upper
    };

    // Parse the public IO as the circuit values
    let circuit_res_X_lower = X[10];
    let circuit_res_X_upper = X[11];
    let circuit_res_X = recombine_scalar(circuit_res_X_lower, circuit_res_X_upper);

    let circuit_res_Y_lower = X[12];
    let circuit_res_Y_upper = X[13];
    let circuit_res_Y = recombine_scalar(circuit_res_Y_lower, circuit_res_Y_upper);

    let circuit_res_is_infinity = X[14];

    // Check the out of circuit result matches the circuit result
    assert_eq!(res_X, circuit_res_X);
    assert_eq!(res_Y, circuit_res_Y);
    assert_eq!(
      res_is_infinity,
      circuit_res_is_infinity == <Dual<E> as Engine>::Base::ONE
    );

    // Check the R1CS equation is satisfied
    shape.is_sat(&ck, &instance, &witness).unwrap();
  }

  #[test]
  fn test_cyclefold_circuit_sat() {
    test_cyclefold_circuit_sat_with::<PallasEngine>();
    test_cyclefold_circuit_sat_with::<Bn256EngineKZG>();
    test_cyclefold_circuit_sat_with::<Secp256k1Engine>();
  }
}
