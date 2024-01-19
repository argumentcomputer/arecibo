//! This module defines Cyclefold stuff

use bellpepper_core::{boolean::AllocatedBit, ConstraintSystem, SynthesisError};

use crate::{
  gadgets::ecc::AllocatedPoint,
  traits::{commitment::CommitmentTrait, Engine},
  Commitment,
};

/// TODO: docs
pub struct CyclefoldCircuitInputs<E: Engine> {
  commit_1: Option<Commitment<E>>,
  commit_2: Option<Commitment<E>>,
  result: Option<Commitment<E>>,
  scalar: Vec<Option<bool>>,
}

impl<E: Engine> CyclefoldCircuitInputs<E> {
  /// TODO
  pub fn new(
    commit_1: Option<Commitment<E>>,
    commit_2: Option<Commitment<E>>,
    result: Option<Commitment<E>>,
    scalar: Vec<Option<bool>>,
  ) -> Self {
    Self {
      commit_1,
      commit_2,
      result,
      scalar,
    }
  }
}

/// TODO: docs
pub struct CyclefoldCircuit<E: Engine> {
  inputs: Option<CyclefoldCircuitInputs<E>>,
}

impl<E: Engine> CyclefoldCircuit<E> {
  /// TODO: docs
  pub fn new(inputs: Option<CyclefoldCircuitInputs<E>>) -> Self {
    Self { inputs }
  }

  fn alloc_witness<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<
    (
      AllocatedPoint<E>,
      AllocatedPoint<E>,
      AllocatedPoint<E>,
      Vec<AllocatedBit>,
    ),
    SynthesisError,
  > {
    let commit_1 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate C_1"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.commit_1.map(|C_1| C_1.to_coordinates())),
    )?;

    let commit_2 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate C_2"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.commit_2.map(|C_2| C_2.to_coordinates())),
    )?;

    let result = AllocatedPoint::alloc(
      cs.namespace(|| "allocate C_1 + r * C_2"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.result.map(|result| result.to_coordinates())),
    )?;

    let scalar = self
      .inputs
      .as_ref()
      .ok_or(SynthesisError::AssignmentMissing)?
      .scalar
      .iter()
      .enumerate()
      .map(|(idx, b)| AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {}", idx)), *b))
      .collect::<Result<_, _>>()?;

    Ok((commit_1, commit_2, result, scalar))
  }

  /// TODO: docs
  pub fn synthesize<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocatedPoint<E>, SynthesisError> {
    let (C_1, C_2, result, r) = self.alloc_witness(cs.namespace(|| "allocate circuit witness"))?;

    // Calculate C_final
    let r_C_2 = C_2.scalar_mul(cs.namespace(|| "r * C_2"), &r)?;

    let C_final = C_1.add(cs.namespace(|| "C_1 + r * C_2"), &r_C_2)?;

    let (res_x, res_y, res_inf) = result.get_coordinates();

    // enforce C_final = result
    cs.enforce(
      || "C_final_x = res_x",
      |lc| lc + res_x.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + C_final.x.get_variable(),
    );

    cs.enforce(
      || "C_final_y = res_y",
      |lc| lc + res_y.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + C_final.y.get_variable(),
    );

    cs.enforce(
      || "C_final_inf = res_inf",
      |lc| lc + res_inf.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + C_final.is_infinity.get_variable(),
    );

    Ok(C_final)
  }
}

#[cfg(test)]
mod tests {
  use ff::{Field, PrimeFieldBits};
  use rand_core::OsRng;

  use crate::{
    bellpepper::{solver::SatisfyingAssignment, test_shape_cs::TestShapeCS},
    provider::{
      Bn256Engine, GrumpkinEngine, PallasEngine, Secp256k1Engine, Secq256k1Engine, VestaEngine,
    },
    traits::commitment::CommitmentEngineTrait,
  };

  use super::*;

  fn test_cyclefold_circuit_size_with<E1, E2>(expected_constraints: usize, expected_vars: usize)
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    let rng = OsRng;

    let ck = <<E2 as Engine>::CE as CommitmentEngineTrait<E2>>::setup(b"hi", 5);

    let v1 = (0..5)
      .map(|_| <E2::Scalar as Field>::random(rng))
      .collect::<Vec<_>>();

    let v2 = (0..5)
      .map(|_| <E2::Scalar as Field>::random(rng))
      .collect::<Vec<_>>();

    let C_1 = <<E2 as Engine>::CE as CommitmentEngineTrait<E2>>::commit(&ck, &v1);

    let C_2 = <<E2 as Engine>::CE as CommitmentEngineTrait<E2>>::commit(&ck, &v2);

    let r = <E2::Scalar as Field>::random(rng);

    let result = C_1 + C_2 * r;

    let r_bits = r.to_le_bits().iter().map(|b| Some(*b)).collect::<Vec<_>>();

    let inputs: CyclefoldCircuitInputs<E2> =
      CyclefoldCircuitInputs::new(Some(C_1), Some(C_2), Some(result), r_bits);

    let circuit: CyclefoldCircuit<_> = CyclefoldCircuit::new(Some(inputs));

    // Test the circuit size does not change
    let mut cs: TestShapeCS<E1> = TestShapeCS::default();
    let _ = circuit.synthesize(cs.namespace(|| "synthesizing shape"));

    let num_constraints = cs.num_constraints();

    let num_variables = cs.num_aux();

    assert_eq!(expected_constraints, num_constraints);
    assert_eq!(expected_vars, num_variables);

    // Test the circuit calculation matches weighted sum of commitments
    let mut cs = SatisfyingAssignment::<E1>::new();

    let P = circuit
      .synthesize(cs.namespace(|| "synthesizing witness"))
      .unwrap();

    let r_C_2 = C_2 * r;

    let C_final = C_1 + r_C_2;

    let P_x = P.x.get_value().unwrap();
    let P_y = P.y.get_value().unwrap();
    let P_infty = P.is_infinity.get_value().unwrap();

    let (x, y, infty) = C_final.to_coordinates();

    assert_eq!(x, P_x);
    assert_eq!(y, P_y);
    assert_eq!(infty, P_infty == <E1::Scalar as Field>::ONE);
  }

  #[test]
  fn test_cyclefold_circuit_size() {
    test_cyclefold_circuit_size_with::<PallasEngine, VestaEngine>(2735, 2728);
    test_cyclefold_circuit_size_with::<Bn256Engine, GrumpkinEngine>(2769, 2760);
    test_cyclefold_circuit_size_with::<Secp256k1Engine, Secq256k1Engine>(2701, 2696);
  }
}
