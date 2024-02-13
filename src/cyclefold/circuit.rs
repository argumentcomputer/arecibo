//! This module defines Cyclefold stuff

use bellpepper_core::{boolean::AllocatedBit, ConstraintSystem, SynthesisError};

use crate::{
  constants::{NUM_CHALLENGE_BITS, NUM_HASH_BITS},
  gadgets::{ecc::AllocatedPoint, utils::le_bits_to_num},
  traits::{commitment::CommitmentTrait, Engine},
  Commitment,
};

/// TODO: docs
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
  /// TODO: docs
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

    let false_bit = AllocatedBit::alloc(cs.namespace(|| "allocated false bit"), Some(false))?;
    let scalar: Vec<AllocatedBit> =
      self
        .scalar
        .map_or(Ok(vec![false_bit; NUM_HASH_BITS]), |bits| {
          bits
            .iter()
            .enumerate()
            .map(|(idx, bit)| {
              AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {idx}")), Some(*bit))
            })
            .collect::<Result<Vec<_>, _>>()
        })?;

    Ok((commit_1, commit_2, scalar))
  }

  /// TODO: docs
  pub fn synthesize<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<(), SynthesisError> {
    let (C_1, C_2, r) = self.alloc_witness(cs.namespace(|| "allocate circuit witness"))?;

    // Calculate C_final
    let r_C_2 = C_2.scalar_mul(cs.namespace(|| "r * C_2"), &r)?;

    let C_final = C_1.add(cs.namespace(|| "C_1 + r * C_2"), &r_C_2)?;

    let mut inputize_point =
      |point: &AllocatedPoint<E::GE>, name: &str| -> Result<(), SynthesisError> {
        point.x.inputize(cs.namespace(|| format!("{name}.x")))?;
        point.y.inputize(cs.namespace(|| format!("{name}.y")))?;
        point
          .is_infinity
          .inputize(cs.namespace(|| format!("{name}.is_infinity")))?;
        Ok(())
      };
    inputize_point(&C_1, "commit_1")?;
    inputize_point(&C_2, "commit_2")?;
    inputize_point(&C_final, "result")?;

    let scalar = le_bits_to_num(cs.namespace(|| "get scalar"), &r)?;

    scalar.inputize(cs.namespace(|| "scalar"))?;

    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use expect_test::{expect, Expect};
  use ff::{Field, PrimeField, PrimeFieldBits};
  use rand_core::OsRng;

  use crate::{
    bellpepper::{solver::SatisfyingAssignment, test_shape_cs::TestShapeCS},
    provider::{Bn256Engine, PallasEngine, Secp256k1Engine},
    traits::{commitment::CommitmentEngineTrait, CurveCycleEquipped, Dual},
  };

  use super::*;

  fn test_cyclefold_circuit_size_with<E1>(expected_constraints: &Expect, expected_vars: &Expect)
  where
    E1: CurveCycleEquipped,
  {
    let rng = OsRng;

    let ck = <<Dual<E1> as Engine>::CE as CommitmentEngineTrait<Dual<E1>>>::setup(b"hi", 5);

    let v1 = (0..5)
      .map(|_| <<Dual<E1> as Engine>::Scalar as Field>::random(rng))
      .collect::<Vec<_>>();

    let v2 = (0..5)
      .map(|_| <<Dual<E1> as Engine>::Scalar as Field>::random(rng))
      .collect::<Vec<_>>();

    let C_1 = <<Dual<E1> as Engine>::CE as CommitmentEngineTrait<Dual<E1>>>::commit(&ck, &v1);

    let C_2 = <<Dual<E1> as Engine>::CE as CommitmentEngineTrait<Dual<E1>>>::commit(&ck, &v2);

    let val: u128 = rand::random();

    let r = <<Dual<E1> as Engine>::Scalar as PrimeField>::from_u128(val);

    let _result = C_1 + C_2 * r;

    let r_bits = r
      .to_le_bits()
      .iter()
      .map(|b| Some(*b))
      .collect::<Option<Vec<_>>>()
      .map(|v| v.try_into().unwrap());

    let circuit: CyclefoldCircuit<Dual<E1>> = CyclefoldCircuit::new(Some(C_1), Some(C_2), r_bits);

    // Test the circuit size does not change
    let mut cs: TestShapeCS<E1> = TestShapeCS::default();
    let _ = circuit.synthesize(cs.namespace(|| "synthesizing shape"));

    let num_constraints = cs.num_constraints();

    let num_variables = cs.num_aux();

    expected_constraints.assert_eq(&num_constraints.to_string());
    expected_vars.assert_eq(&num_variables.to_string());

    // Test the circuit calculation matches weighted sum of commitments
    let mut cs = SatisfyingAssignment::<E1>::new();

    let _ = circuit
      .synthesize(cs.namespace(|| "synthesizing witness"))
      .unwrap();

    let r_C_2 = C_2 * r;

    let _C_final = C_1 + r_C_2;
  }

  #[test]
  fn test_cyclefold_circuit_size() {
    test_cyclefold_circuit_size_with::<PallasEngine>(&expect!("2735"), &expect!("2728"));
    test_cyclefold_circuit_size_with::<Bn256Engine>(&expect!("2769"), &expect!("2760"));
    test_cyclefold_circuit_size_with::<Secp256k1Engine>(&expect!("2701"), &expect!("2696"));
  }

  // TODO: add test for circuit satisfiability
}
