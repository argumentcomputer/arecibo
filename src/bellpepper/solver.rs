//! Support for generating R1CS witness using bellpepper.

use crate::{r1cs::R1CSShape, traits::Group};

use ff::Field;
use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::ConstraintSystem;

/// A `ConstraintSystem` which calculates witness values for a concrete instance of an R1CS circuit.
pub type SatisfyingAssignment<G> = WitnessCS<<G as Group>::Scalar>;

/// This extension trait is implemented by constraint systems that know how to pre-allocate their internal
/// storage based on an R1CSShape, which has (among others) a documented count for the number of io variables
/// the CS should encounter during synthesis.
pub trait WithShapeBasedPreAllocation<G: Group>: ConstraintSystem<<G as Group>::Scalar> {
  fn new_from_shape_parameters(r1cs_shape: &R1CSShape<G>) -> Self;
}

/// SatisfyingAssignment knows how to pre-allocate its internal storage given an R1CSShape.
impl<G: Group> WithShapeBasedPreAllocation<G> for SatisfyingAssignment<G> {
  fn new_from_shape_parameters(r1cs_shape: &R1CSShape<G>) -> Self {
    let mut cs = SatisfyingAssignment::<G>::with_capacity(r1cs_shape.num_io + 1, r1cs_shape.num_vars);
    // TODO: fix this bug in WitnessCS, compare SatisfyingAssignment::new()
    cs.extend_inputs(&[G::Scalar::ONE]);
    cs
  }
}
