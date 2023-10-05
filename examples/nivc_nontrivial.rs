//! TODO: Make this into a test
use std::marker::PhantomData;

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::Field;
use ff::PrimeField;
use nova_snark::supernova::PublicParams;
use nova_snark::supernova::RecursiveSNARK;
use nova_snark::traits::circuit_supernova::TrivialSecondaryCircuit;
use nova_snark::{
  supernova::NonUniformCircuit,
  traits::{circuit_supernova::StepCircuit, Group},
};

const NUM_STEPS: usize = 10;

#[derive(Debug)]
struct ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  num_iter: usize,
  hint: G1::Scalar,
  _p: PhantomData<G2>,
}

impl<G1, G2> ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  fn new(num_iter: usize) -> (Vec<G1::Scalar>, Self) {
    let rng = rand::rngs::OsRng;
    let mut hint = <G1::Scalar as Field>::random(rng);
    let mut hints: Vec<G1::Scalar> = (0..num_iter + 1)
      .map(|iter| {
        let old_hint = hint;
        if iter % 2 == 0 {
          hint *= hint.square()
        } else {
          hint *= hint.square().square()
        }
        old_hint
      })
      .collect();

    hints.reverse();

    (
      hints.clone(),
      Self {
        num_iter,
        hint: hints[1],
        _p: PhantomData,
      },
    )
  }
}

#[derive(Debug, Clone)]
struct CubeRootCircuit<F: PrimeField> {
  hint: F,
}

impl<F: PrimeField> CubeRootCircuit<F> {
  fn new(hint: F) -> Self {
    Self { hint }
  }
}

impl<F: PrimeField> StepCircuit<F> for CubeRootCircuit<F> {
  fn arity(&self) -> usize {
    1
  }

  fn circuit_index(&self) -> usize {
    0
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let x = &z[0];

    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(self.hint))?;

    let y_sq = y.square(cs.namespace(|| "y_sq"))?;
    let y_cu = y_sq.mul(cs.namespace(|| "y_cu"), &y)?;

    cs.enforce(
      || "y^3 = x",
      |lc| lc + CS::one(),
      |lc| lc + y_cu.get_variable(),
      |lc| lc + x.get_variable(),
    );

    let next_pc = AllocatedNum::alloc(cs.namespace(|| "pc_1"), || Ok(<F as Field>::ONE))?;

    Ok((Some(next_pc), vec![y]))
  }
}
#[derive(Debug, Clone)]
struct FifthRootCircuit<F: PrimeField> {
  hint: F,
}

impl<F: PrimeField> FifthRootCircuit<F> {
  fn new(hint: F) -> Self {
    Self { hint }
  }
}

impl<F: PrimeField> StepCircuit<F> for FifthRootCircuit<F> {
  fn arity(&self) -> usize {
    1
  }

  fn circuit_index(&self) -> usize {
    1
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let x = &z[0];

    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(self.hint))?;

    let y_sq = y.square(cs.namespace(|| "y_sq"))?;
    let y_qu = y_sq.square(cs.namespace(|| "y_qu"))?;
    let y_fifth = y_qu.mul(cs.namespace(|| "y_fifth"), &y)?;

    cs.enforce(
      || "y^5 = x",
      |lc| lc + CS::one(),
      |lc| lc + y_fifth.get_variable(),
      |lc| lc + x.get_variable(),
    );

    let next_pc = AllocatedNum::alloc(cs.namespace(|| "pc_0"), || Ok(<F as Field>::ZERO))?;

    Ok((Some(next_pc), vec![y]))
  }
}

#[derive(Debug, Clone)]
enum TestCircuit<F: PrimeField> {
  Cube(CubeRootCircuit<F>),
  Fifth(FifthRootCircuit<F>),
}

impl<F: PrimeField> StepCircuit<F> for TestCircuit<F> {
  fn arity(&self) -> usize {
    match self {
      Self::Cube(x) => x.arity(),
      Self::Fifth(x) => x.arity(),
    }
  }

  fn circuit_index(&self) -> usize {
    match self {
      Self::Cube(x) => x.circuit_index(),
      Self::Fifth(x) => x.circuit_index(),
    }
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    match self {
      Self::Cube(x) => x.synthesize(cs, pc, z),
      Self::Fifth(x) => x.synthesize(cs, pc, z),
    }
  }
}

impl<G1, G2> NonUniformCircuit<G1, G2, TestCircuit<G1::Scalar>, TrivialSecondaryCircuit<G2::Scalar>>
  for ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  fn num_circuits(&self) -> usize {
    2
  }

  fn initial_program_counter(&self) -> <G1 as Group>::Scalar {
    if self.num_iter % 2 == 0 {
      <G1 as Group>::Scalar::ONE
    } else {
      <G1 as Group>::Scalar::ZERO
    }
  }

  fn primary_circuit(&self, circuit_index: usize) -> TestCircuit<G1::Scalar> {
    match circuit_index {
      0 => TestCircuit::Cube(CubeRootCircuit::new(self.hint)),
      1 => TestCircuit::Fifth(FifthRootCircuit::new(self.hint)),
      _ => panic!("This shouldn't happen"),
    }
  }

  fn secondary_circuit(&self) -> TrivialSecondaryCircuit<G2::Scalar> {
    Default::default()
  }
}

fn run_nivc_nontrivial_nondet_with<G1, G2>()
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  let (hints, example): (Vec<_>, ExampleSteps<G1, G2>) = ExampleSteps::new(NUM_STEPS);

  let pp = PublicParams::new(&example);

  let initial_pc: <G1 as Group>::Scalar = example.initial_program_counter();

  let augmented_circuit_index = field_as_usize(initial_pc);

  let z0_primary = vec![hints[0]];
  let z0_secondary = vec![<G2 as Group>::Scalar::ZERO];

  let mut recursive_snark = RecursiveSNARK::iter_base_step(
    &pp,
    augmented_circuit_index,
    &example.primary_circuit(augmented_circuit_index),
    &example.secondary_circuit(),
    Some(initial_pc),
    augmented_circuit_index,
    2,
    &z0_primary,
    &z0_secondary,
  )
  .unwrap();

  for hint in hints.into_iter().take(NUM_STEPS).skip(1) {
    let example: ExampleSteps<G1, G2> = ExampleSteps {
      num_iter: NUM_STEPS,
      hint,
      _p: PhantomData,
    };

    let program_counter: G1::Scalar = recursive_snark.get_program_counter();

    let augmented_circuit_index = field_as_usize(program_counter);

    let res = recursive_snark.prove_step(
      &pp,
      augmented_circuit_index,
      &example.primary_circuit(augmented_circuit_index),
      &example.secondary_circuit(),
      &z0_primary,
      &z0_secondary,
    );

    if let Err(e) = &res {
      println!("proving failed {:?}", e);
    }

    let res = recursive_snark.verify(&pp, augmented_circuit_index, &z0_primary, &z0_secondary);
    if let Err(e) = &res {
      println!("verifying failed {:?}", e);
    }
  }

  println!("No errors");
}

fn main() {
  run_nivc_nontrivial_nondet_with::<pasta_curves::pallas::Point, pasta_curves::vesta::Point>();
}

fn field_as_usize<F: PrimeField>(x: F) -> usize {
  u32::from_le_bytes(x.to_repr().as_ref()[0..4].try_into().unwrap()) as usize
}
