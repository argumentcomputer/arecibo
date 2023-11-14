//! Support for generating R1CS witness using bellpepper.
use crate::traits::Engine;
use bellpepper_core::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use ff::PrimeField;

use bellpepper::util_cs::witness_cs::WitnessCS;

/// A [`ConstraintSystem`] which calculates witness values for a concrete instance of an R1CS circuit.
pub type SatisfyingAssignment<E> = WitnessCS<<E as Engine>::Scalar>;

#[derive(Debug, PartialEq, Eq)]
/// A [`ConstraintSystem`] which calculates witness values for a concrete instance of an R1CS circuit.
///
/// This is specialized to support Nova by offering a mutable handle into `R1CSWitness` and `R1CSInstance`.
/// - `aux_assignment` corresponds to `R1CSWitness.W`
/// - `input_assignment[0]` corresponds to `R1CSInstance.u`
/// - `input_assignment[1..]` corresponds to `R1CSInstance.X`
///
/// Whenever a new [`WitnessViewCS`] is constructed, we acquire handles into preallocated buffers that
/// `R1CSWitness` and `R1CSInstance` own. On the "zeroth" step of Nova, these buffers are empty and
/// [`WitnessViewCS`] does not know the expected witness sizes. This initial state is flagged as
/// `setup = true`. After the initial step, every next Nova step has a fixed shape, so the buffers in
/// `R1CSWitness` and `R1CSInstance` have the exact capacity they need. To be memory efficient,
/// [`WitnessViewCS`] is flagged as `setup = false` and we no longer allow the buffers to resize.
pub struct WitnessViewCS<'a, Scalar>
where
  Scalar: PrimeField,
{
  // Assignments of variables
  pub(crate) input_assignment: &'a mut Vec<Scalar>,
  pub(crate) aux_assignment: &'a mut Vec<Scalar>,
}

impl<'a, Scalar> ConstraintSystem<Scalar> for WitnessViewCS<'a, Scalar>
where
  Scalar: PrimeField,
{
  type Root = Self;

  fn new() -> Self {
    unimplemented!()
  }

  fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    self.aux_assignment.push(f()?);

    Ok(Variable(Index::Aux(self.aux_assignment.len() - 1)))
  }

  fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    self.input_assignment.push(f()?);

    Ok(Variable(Index::Input(self.input_assignment.len() - 1)))
  }

  fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, _a: LA, _b: LB, _c: LC)
  where
    A: FnOnce() -> AR,
    AR: Into<String>,
    LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
  {
    // Do nothing: we don't care about linear-combination evaluations in this context.
  }

  fn push_namespace<NR, N>(&mut self, _: N)
  where
    NR: Into<String>,
    N: FnOnce() -> NR,
  {
    // Do nothing; we don't care about namespaces in this context.
  }

  fn pop_namespace(&mut self) {
    // Do nothing; we don't care about namespaces in this context.
  }

  fn get_root(&mut self) -> &mut Self::Root {
    self
  }

  ////////////////////////////////////////////////////////////////////////////////
  // Extensible
  fn is_extensible() -> bool {
    true
  }

  /// This should not be used because the whole point of [`WitnessViewCS`] is to
  /// hold the witness in a external buffer, in which case we shouldn't have
  /// two [`WitnessViewCS`]s.
  fn extend(&mut self, _other: &Self) {
    panic!("WitnessViewCS::extend");
  }

  ////////////////////////////////////////////////////////////////////////////////
  // Witness generator
  fn is_witness_generator(&self) -> bool {
    true
  }

  fn extend_inputs(&mut self, new_inputs: &[Scalar]) {
    self.input_assignment.extend_from_slice(new_inputs);
  }

  fn extend_aux(&mut self, new_aux: &[Scalar]) {
    self.aux_assignment.extend_from_slice(new_aux);
  }

  fn allocate_empty(&mut self, aux_n: usize, inputs_n: usize) -> (&mut [Scalar], &mut [Scalar]) {
    let allocated_aux = {
      let i = self.aux_assignment.len();
      self.aux_assignment.resize(aux_n + i, Scalar::ZERO);
      &mut self.aux_assignment[i..]
    };

    let allocated_inputs = {
      let i = self.input_assignment.len();
      self.input_assignment.resize(inputs_n + i, Scalar::ZERO);
      &mut self.input_assignment[i..]
    };

    (allocated_aux, allocated_inputs)
  }

  fn inputs_slice(&self) -> &[Scalar] {
    self.input_assignment
  }

  fn aux_slice(&self) -> &[Scalar] {
    self.aux_assignment
  }
}

impl<'a, Scalar: PrimeField> WitnessViewCS<'a, Scalar> {
  pub fn new_view(
    input_assignment: &'a mut Vec<Scalar>,
    aux_assignment: &'a mut Vec<Scalar>,
  ) -> Self {
    input_assignment.clear();
    input_assignment.push(Scalar::ONE);
    aux_assignment.clear();

    Self {
      input_assignment,
      aux_assignment,
    }
  }
}
