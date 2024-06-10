use crate::{supernova::StepCircuit, traits::CurveCycleEquipped};

/// SuperNova helper trait, for implementors that provide sets of sub-circuits to be proved via NIVC. `C1` must be a
/// type (likely an `Enum`) for which a potentially-distinct instance can be supplied for each `index` below
/// `self.num_circuits()`.
pub trait NonUniformCircuit<E1>
where
  E1: CurveCycleEquipped,
{
  /// The type of the step-circuits on the primary
  type C1: StepCircuit<E1::Scalar>;

  /// Initial circuit index, defaults to zero.
  fn initial_circuit_index(&self) -> usize {
    0
  }

  /// How many circuits are provided?
  fn num_circuits(&self) -> usize;

  /// Return a new instance of the primary circuit at `index`.
  fn primary_circuit(&self, circuit_index: usize) -> Self::C1;
}
