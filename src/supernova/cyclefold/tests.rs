use std::marker::PhantomData;
use std::time::Instant;

use crate::provider::PallasEngine;
use crate::supernova::cyclefold::snark::PublicParams;
use crate::traits::snark::default_ck_hint;
use crate::traits::Engine;
use crate::{
  bellpepper::test_shape_cs::TestShapeCS,
  supernova::{error::SuperNovaError, utils::get_selector_vec_from_index, StepCircuit},
  traits::{CurveCycleEquipped, Dual},
};
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::Field;
use ff::PrimeField;
use itertools::Itertools;
use tap::TapOptional;
use tracing::debug;

use super::augmented_circuit::SuperNovaAugmentedCircuit;
use super::snark::RecursiveSNARK;
use super::traits::NonUniformCircuit;

#[derive(Clone, Debug, Default)]
struct CubicCircuit<F> {
  _p: PhantomData<F>,
  circuit_index: usize,
  rom_size: usize,
}

impl<F> CubicCircuit<F> {
  fn new(circuit_index: usize, rom_size: usize) -> Self {
    Self {
      circuit_index,
      rom_size,
      _p: PhantomData,
    }
  }
}

fn next_rom_index_and_pc<F: PrimeField, CS: ConstraintSystem<F>>(
  cs: &mut CS,
  rom_index: &AllocatedNum<F>,
  allocated_rom: &[AllocatedNum<F>],
  pc: &AllocatedNum<F>,
) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
  // Compute a selector for the current rom_index in allocated_rom
  let current_rom_selector = get_selector_vec_from_index(
    cs.namespace(|| "rom selector"),
    rom_index,
    allocated_rom.len(),
  )?;

  // Enforce that allocated_rom[rom_index] = pc
  for (rom, bit) in allocated_rom.iter().zip_eq(current_rom_selector.iter()) {
    // if bit = 1, then rom = pc
    // bit * (rom - pc) = 0
    cs.enforce(
      || "enforce bit = 1 => rom = pc",
      |lc| lc + &bit.lc(CS::one(), F::ONE),
      |lc| lc + rom.get_variable() - pc.get_variable(),
      |lc| lc,
    );
  }

  // Get the index of the current rom, or the index of the invalid rom if no match
  let current_rom_index = current_rom_selector
    .iter()
    .position(|bit| bit.get_value().is_some_and(|v| v))
    .unwrap_or_default();
  let next_rom_index = current_rom_index + 1;

  let rom_index_next = AllocatedNum::alloc_infallible(cs.namespace(|| "next rom index"), || {
    F::from(next_rom_index as u64)
  });
  cs.enforce(
    || " rom_index + 1 - next_rom_index_num = 0",
    |lc| lc,
    |lc| lc,
    |lc| lc + rom_index.get_variable() + CS::one() - rom_index_next.get_variable(),
  );

  // Allocate the next pc without checking.
  // The next iteration will check whether the next pc is valid.
  let pc_next = AllocatedNum::alloc_infallible(cs.namespace(|| "next pc"), || {
    allocated_rom
      .get(next_rom_index)
      .and_then(|v| v.get_value())
      .unwrap_or(-F::ONE)
  });

  Ok((rom_index_next, pc_next))
}

impl<F> StepCircuit<F> for CubicCircuit<F>
where
  F: PrimeField,
{
  fn arity(&self) -> usize {
    2 + self.rom_size // value + rom_pc + rom[].len()
  }

  fn circuit_index(&self) -> usize {
    self.circuit_index
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let rom_index = &z[1];
    let allocated_rom = &z[2..];

    let (rom_index_next, pc_next) = next_rom_index_and_pc(
      &mut cs.namespace(|| "next and rom_index and pc"),
      rom_index,
      allocated_rom,
      pc.ok_or(SynthesisError::AssignmentMissing)?,
    )?;

    // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
    let x = &z[0];
    let x_sq = x.square(cs.namespace(|| "x_sq"))?;
    let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), x)?;
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
    })?;

    cs.enforce(
      || "y = x^3 + x + 5",
      |lc| {
        lc + x_cu.get_variable()
          + x.get_variable()
          + CS::one()
          + CS::one()
          + CS::one()
          + CS::one()
          + CS::one()
      },
      |lc| lc + CS::one(),
      |lc| lc + y.get_variable(),
    );

    let mut z_next = vec![y];
    z_next.push(rom_index_next);
    z_next.extend(z[2..].iter().cloned());
    Ok((Some(pc_next), z_next))
  }
}

#[derive(Clone, Debug, Default)]
struct SquareCircuit<F> {
  _p: PhantomData<F>,
  circuit_index: usize,
  rom_size: usize,
}

impl<F> SquareCircuit<F> {
  fn new(circuit_index: usize, rom_size: usize) -> Self {
    Self {
      circuit_index,
      rom_size,
      _p: PhantomData,
    }
  }
}

impl<F> StepCircuit<F> for SquareCircuit<F>
where
  F: PrimeField,
{
  fn arity(&self) -> usize {
    2 + self.rom_size // value + rom_pc + rom[].len()
  }

  fn circuit_index(&self) -> usize {
    self.circuit_index
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let rom_index = &z[1];
    let allocated_rom = &z[2..];

    let (rom_index_next, pc_next) = next_rom_index_and_pc(
      &mut cs.namespace(|| "next and rom_index and pc"),
      rom_index,
      allocated_rom,
      pc.ok_or(SynthesisError::AssignmentMissing)?,
    )?;

    // Consider an equation: `x^2 + x + 5 = y`, where `x` and `y` are respectively the input and output.
    let x = &z[0];
    let x_sq = x.square(cs.namespace(|| "x_sq"))?;
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(x_sq.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
    })?;

    cs.enforce(
      || "y = x^2 + x + 5",
      |lc| {
        lc + x_sq.get_variable()
          + x.get_variable()
          + CS::one()
          + CS::one()
          + CS::one()
          + CS::one()
          + CS::one()
      },
      |lc| lc + CS::one(),
      |lc| lc + y.get_variable(),
    );

    let mut z_next = vec![y];
    z_next.push(rom_index_next);
    z_next.extend(z[2..].iter().cloned());
    Ok((Some(pc_next), z_next))
  }
}

fn print_constraints_name_on_error_index<E1, C1: StepCircuit<E1::Scalar>>(
  err: &SuperNovaError,
  pp: &PublicParams<E1>,
  c_primary: &C1,
  num_augmented_circuits: usize,
) where
  E1: CurveCycleEquipped,
{
  match err {
    SuperNovaError::UnSatIndex(msg, index) if *msg == "r_primary" => {
      let circuit_primary: SuperNovaAugmentedCircuit<'_, Dual<E1>, E1, C1> =
        SuperNovaAugmentedCircuit::new(
          &pp.augmented_circuit_params,
          None,
          pp.ro_consts_circuit_primary.clone(),
          c_primary,
          num_augmented_circuits,
        );
      let mut cs: TestShapeCS<E1> = TestShapeCS::new();
      let _ = circuit_primary.synthesize(&mut cs);
      cs.constraints
        .get(*index)
        .tap_some(|constraint| debug!("{msg} failed at constraint {}", constraint.3));
    }
    _ => (),
  }
}

const OPCODE_0: usize = 0;
const OPCODE_1: usize = 1;

struct TestROM<E1> {
  rom: Vec<usize>,
  _p: PhantomData<E1>,
}

#[derive(Debug, Clone)]
enum TestROMCircuit<F: PrimeField> {
  Cubic(CubicCircuit<F>),
  Square(SquareCircuit<F>),
}

impl<F: PrimeField> StepCircuit<F> for TestROMCircuit<F> {
  fn arity(&self) -> usize {
    match self {
      Self::Cubic(x) => x.arity(),
      Self::Square(x) => x.arity(),
    }
  }

  fn circuit_index(&self) -> usize {
    match self {
      Self::Cubic(x) => x.circuit_index(),
      Self::Square(x) => x.circuit_index(),
    }
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    match self {
      Self::Cubic(x) => x.synthesize(cs, pc, z),
      Self::Square(x) => x.synthesize(cs, pc, z),
    }
  }
}

impl<E1> NonUniformCircuit<E1> for TestROM<E1>
where
  E1: CurveCycleEquipped,
{
  type C1 = TestROMCircuit<E1::Scalar>;

  fn num_circuits(&self) -> usize {
    2
  }

  fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
    match circuit_index {
      0 => TestROMCircuit::Cubic(CubicCircuit::new(circuit_index, self.rom.len())),
      1 => TestROMCircuit::Square(SquareCircuit::new(circuit_index, self.rom.len())),
      _ => panic!("unsupported primary circuit index"),
    }
  }

  fn initial_circuit_index(&self) -> usize {
    self.rom[0]
  }
}

impl<E1> TestROM<E1> {
  fn new(rom: Vec<usize>) -> Self {
    Self {
      rom,
      _p: Default::default(),
    }
  }
}

fn test_trivial_nivc_with<E1>() -> Result<(), SuperNovaError>
where
  E1: CurveCycleEquipped,
{
  // Here demo a simple RAM machine
  // - with 2 argumented circuit
  // - each argumented circuit contains primary and secondary circuit
  // - a memory commitment via a public IO `rom` (like a program) to constraint the sequence execution

  // This test also ready to add more argumented circuit and ROM can be arbitrary length

  // ROM is for constraints the sequence of execution order for opcode

  // TODO: replace with memory commitment along with suggestion from Supernova 4.4 optimisations

  // This is mostly done with the existing Nova code. With additions of U_i[] and program_counter checks
  // in the augmented circuit.

  let rom = vec![
    OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1,
    OPCODE_1,
  ];
  // let rom = vec![OPCODE_0, OPCODE_0, OPCODE_1, OPCODE_1];

  let test_rom = TestROM::<E1>::new(rom);

  println!("Producing PP");
  let time = Instant::now();
  let pp = PublicParams::setup(&test_rom, &*default_ck_hint(), &*default_ck_hint());
  println!("Producing PP took {:?}", time.elapsed());

  // extend z0_primary/secondary with rom content
  let mut z0_primary = vec![<E1 as Engine>::Scalar::ONE];
  z0_primary.push(<E1 as Engine>::Scalar::ZERO); // rom_index = 0
  z0_primary.extend(
    test_rom
      .rom
      .iter()
      .map(|opcode| <E1 as Engine>::Scalar::from(*opcode as u64)),
  );

  let mut recursive_snark_option: Option<RecursiveSNARK<E1>> = None;

  println!("starting NIVC");
  for (i, &op_code) in test_rom.rom.iter().enumerate() {
    println!("i {}, opcode {}", i, op_code);
    let circuit_primary = test_rom.primary_circuit(op_code);

    let mut recursive_snark = recursive_snark_option.unwrap_or_else(|| {
      RecursiveSNARK::new(&pp, &test_rom, &circuit_primary, &z0_primary).unwrap()
    });

    recursive_snark.prove_step(&pp, &circuit_primary)?;
    recursive_snark
      .verify(&pp, &z0_primary)
      .map_err(|err| {
        print_constraints_name_on_error_index(&err, &pp, &circuit_primary, test_rom.num_circuits())
      })
      .unwrap();

    recursive_snark_option = Some(recursive_snark)
  }

  assert!(recursive_snark_option.is_some());

  // Now you can handle the Result using if let
  let RecursiveSNARK {
    zi_primary,
    program_counter,
    ..
  } = &recursive_snark_option.unwrap();

  println!("zi_primary: {:?}", zi_primary);
  println!("final program_counter: {:?}", program_counter);

  // The final program counter should be -1
  assert_eq!(*program_counter, -<E1 as Engine>::Scalar::ONE);
  Ok(())
}

#[test]
#[tracing_test::traced_test]
fn test_trivial_nivc() -> Result<(), SuperNovaError> {
  // Experimenting with selecting the running claims for nifs
  test_trivial_nivc_with::<PallasEngine>()
}