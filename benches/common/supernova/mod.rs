// Code is considered dead unless used in all benchmark targets
#![allow(dead_code)]

pub mod bench;
pub mod targets;

use anyhow::anyhow;
use arecibo::{
  supernova::NonUniformCircuit,
  supernova::{StepCircuit, TrivialTestCircuit},
  traits::Engine,
};
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use core::marker::PhantomData;
use ff::PrimeField;

pub type E1 = arecibo::provider::PallasEngine;
pub type E2 = arecibo::provider::VestaEngine;
pub type EE1 = arecibo::provider::ipa_pc::EvaluationEngine<E1>;
pub type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
// SNARKs without computation commitments
pub type S1 = arecibo::spartan::batched::BatchedRelaxedR1CSSNARK<E1, EE1>;
pub type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;
// SNARKs with computation commitments
pub type SS1 = arecibo::spartan::batched_ppsnark::BatchedRelaxedR1CSSNARK<E1, EE1>;
pub type SS2 = arecibo::spartan::ppsnark::RelaxedR1CSSNARK<E2, EE2>;

// This should match the value in test_supernova_recursive_circuit_pasta
// Note `NUM_CONS_VERIFIER_CIRCUIT_PRIMARY` is different for Nova and Supernova
// TODO: This should also be a table matching the num_augmented_circuits in the below
pub const NUM_CONS_VERIFIER_CIRCUIT_PRIMARY: usize = 9844;
pub const NUM_SAMPLES: usize = 10;

#[derive(Copy, Clone)]
pub enum SnarkType {
  Recursive,
  Compressed,
}

// TODO: Move this up a level to `common/mod.rs`, then integrate with non-Supernova benches
pub fn num_cons() -> Vec<usize> {
  num_cons_env().unwrap_or_else(|_| {
    vec![
      NUM_CONS_VERIFIER_CIRCUIT_PRIMARY,
      16384,
      32768,
      65536,
      131072,
      262144,
      524288,
      1048576,
    ]
  })
}

fn num_cons_env() -> anyhow::Result<Vec<usize>> {
  std::env::var("ARECIBO_BENCH_NUM_CONS")
    .map_err(|e| anyhow!("ARECIBO_BENCH_NUM_CONS env var not set: {e}"))
    .and_then(|rc| {
      let vec: anyhow::Result<Vec<usize>> = rc
        .split(',')
        .map(|rc| {
          rc.parse::<usize>()
            .map_err(|e| anyhow!("Failed to parse constraint number: {e}"))
        })
        .collect();
      vec
    })
}

pub struct NonUniformBench<E1, E2, S>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S: StepCircuit<E2::Scalar> + Default,
{
  num_circuits: usize,
  num_cons: usize,
  _p: PhantomData<(E1, E2, S)>,
}

impl<E1, E2, S> NonUniformBench<E1, E2, S>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S: StepCircuit<E2::Scalar> + Default,
{
  fn new(num_circuits: usize, num_cons: usize) -> Self {
    Self {
      num_circuits,
      num_cons,
      _p: Default::default(),
    }
  }
}

impl<E1, E2, S>
  NonUniformCircuit<E1, NonTrivialTestCircuit<E1::Scalar>, E2, TrivialTestCircuit<E2::Scalar>>
  for NonUniformBench<E1, E2, S>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S: StepCircuit<E2::Scalar> + Default,
{
  fn num_circuits(&self) -> usize {
    self.num_circuits
  }

  fn primary_circuit(&self, circuit_index: usize) -> NonTrivialTestCircuit<E1::Scalar> {
    assert!(
      circuit_index < self.num_circuits,
      "Circuit index out of bounds: asked for {circuit_index}, but there are only {} circuits.",
      self.num_circuits
    );

    NonTrivialTestCircuit::new(self.num_cons)
  }

  fn secondary_circuit(&self) -> TrivialTestCircuit<E2::Scalar> {
    Default::default()
  }
}

#[derive(Clone, Debug, Default)]
pub struct NonTrivialTestCircuit<F: PrimeField> {
  num_cons: usize,
  _p: PhantomData<F>,
}

impl<F> NonTrivialTestCircuit<F>
where
  F: PrimeField,
{
  pub fn new(num_cons: usize) -> Self {
    Self {
      num_cons,
      _p: Default::default(),
    }
  }
}
impl<F> StepCircuit<F> for NonTrivialTestCircuit<F>
where
  F: PrimeField,
{
  fn arity(&self) -> usize {
    1
  }

  fn circuit_index(&self) -> usize {
    0
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    // Consider a an equation: `x^{2 * num_cons} = y`, where `x` and `y` are respectively the input and output.
    let mut x = z[0].clone();
    let mut y = x.clone();
    for i in 0..self.num_cons {
      y = x.square(cs.namespace(|| format!("x_sq_{i}")))?;
      x = y.clone();
    }
    Ok((pc.cloned(), vec![y]))
  }
}
