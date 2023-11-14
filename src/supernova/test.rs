use crate::bellpepper::test_shape_cs::TestShapeCS;
use crate::gadgets::utils::alloc_const;
use crate::gadgets::utils::alloc_num_equals;
use crate::gadgets::utils::conditionally_select;
use crate::gadgets::utils::{alloc_one, alloc_zero};
use crate::provider::bn256_grumpkin::bn256;
use crate::provider::bn256_grumpkin::grumpkin;
use crate::provider::poseidon::PoseidonConstantsCircuit;
use crate::provider::secp_secq::secp256k1;
use crate::provider::secp_secq::secq256k1;
use crate::traits::circuit_supernova::{
  EnforcingStepCircuit, StepCircuit, TrivialSecondaryCircuit, TrivialTestCircuit,
};
use crate::traits::snark::default_ck_hint;
use bellpepper::gadgets::{boolean::Boolean, Assignment};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use core::marker::PhantomData;
use ff::Field;
use ff::PrimeField;
use std::fmt::Write;
use tap::TapOptional;

use super::*;

fn constrain_augmented_circuit_index<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  program_counter: &AllocatedNum<F>,
  rom: &[AllocatedNum<F>],
  circuit_index: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
  // select target when index match or empty
  let zero = alloc_zero(cs.namespace(|| "zero"));
  let rom_values = rom
    .iter()
    .enumerate()
    .map(|(i, rom_value)| {
      let index_alloc = alloc_const(
        cs.namespace(|| format!("rom_values {} index ", i)),
        F::from(i as u64),
      )?;
      let equal_bit = Boolean::from(alloc_num_equals(
        cs.namespace(|| format!("rom_values {} equal bit", i)),
        &index_alloc,
        program_counter,
      )?);
      conditionally_select(
        cs.namespace(|| format!("rom_values {} conditionally_select ", i)),
        rom_value,
        &zero,
        &equal_bit,
      )
    })
    .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

  let sum_lc = rom_values
    .iter()
    .fold(LinearCombination::<F>::zero(), |acc_lc, row_value| {
      acc_lc + row_value.get_variable()
    });

  cs.enforce(
    || "sum_lc == circuit_index",
    |lc| lc + circuit_index.get_variable() - &sum_lc,
    |lc| lc + CS::one(),
    |lc| lc,
  );

  Ok(())
}

#[derive(Clone, Debug, Default)]
struct CubicCircuit<F: PrimeField> {
  _p: PhantomData<F>,
  circuit_index: usize,
  rom_size: usize,
}

impl<F> CubicCircuit<F>
where
  F: PrimeField,
{
  fn new(circuit_index: usize, rom_size: usize) -> Self {
    CubicCircuit {
      circuit_index,
      rom_size,
      _p: PhantomData,
    }
  }
}
/// c = a + b where a, b is `AllocatedNum`
pub fn add_allocated_num<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "c"), || {
    Ok(*a.get_value().get()? + b.get_value().get()?)
  })?;
  cs.enforce(
    || "Check u_fold",
    |lc| lc + a.get_variable() + b.get_variable(),
    |lc| lc + CS::one(),
    |lc| lc + c.get_variable(),
  );
  Ok(c)
}

fn next_rom_index_and_pc<F: PrimeField, CS: ConstraintSystem<F>>(
  cs: &mut CS,
  rom_index: &AllocatedNum<F>,
  allocated_rom: &[AllocatedNum<F>],
) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
  let one = alloc_one(cs.namespace(|| "alloc one"));

  let rom_index_next = add_allocated_num(
    // rom_index = rom_index + 1
    cs.namespace(|| "rom_index = rom_index + 1".to_string()),
    rom_index,
    &one,
  )?;
  let pc_next = AllocatedNum::alloc(&mut cs.namespace(|| "pc_next"), || {
    rom_index_next
      .get_value()
      .and_then(|f| {
        let n: u64 = u64::from_le_bytes(f.to_repr().as_ref()[0..8].try_into().unwrap());
        allocated_rom
          .get(n as usize)
          .and_then(|x| x.get_value())
          .or(Some(F::ZERO))
      })
      .ok_or(SynthesisError::AssignmentMissing)
  })?;
  constrain_augmented_circuit_index(
    cs.namespace(|| "CubicCircuit agumented circuit constraint"),
    &rom_index_next,
    allocated_rom,
    &pc_next,
  )?;
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
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let rom_index = &z[1];
    let allocated_rom = &z[2..];

    let (rom_index_next, pc_next) = next_rom_index_and_pc(
      &mut cs.namespace(|| "next and rom_index and pc"),
      rom_index,
      allocated_rom,
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
struct SquareCircuit<F: PrimeField> {
  _p: PhantomData<F>,
  circuit_index: usize,
  rom_size: usize,
}

impl<F> SquareCircuit<F>
where
  F: PrimeField,
{
  fn new(circuit_index: usize, rom_size: usize) -> Self {
    SquareCircuit {
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
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let rom_index = &z[1];
    let allocated_rom = &z[2..];

    let (rom_index_next, pc_next) = next_rom_index_and_pc(
      &mut cs.namespace(|| "next and rom_index and pc"),
      rom_index,
      allocated_rom,
    )?;

    constrain_augmented_circuit_index(
      cs.namespace(|| "SquareCircuit agumented circuit constraint"),
      &rom_index_next,
      allocated_rom,
      &pc_next,
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

fn print_constraints_name_on_error_index<G1, G2, C1, C2>(
  err: &SuperNovaError,
  pp: &PublicParams<G1, G2, C1, C2>,
  c_primary: &C1,
  c_secondary: &C2,
  num_augmented_circuits: usize,
) where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: EnforcingStepCircuit<G1::Scalar>,
  C2: EnforcingStepCircuit<G2::Scalar>,
{
  match err {
    SuperNovaError::UnSatIndex(msg, index) if *msg == "r_primary" => {
      let circuit_primary: SuperNovaAugmentedCircuit<'_, G2, C1> = SuperNovaAugmentedCircuit::new(
        &pp.augmented_circuit_params_primary,
        None,
        c_primary,
        pp.ro_consts_circuit_primary.clone(),
        num_augmented_circuits,
      );
      let mut cs: TestShapeCS<G1> = TestShapeCS::new();
      let _ = circuit_primary.synthesize(&mut cs);
      cs.constraints
        .get(*index)
        .tap_some(|constraint| debug!("{msg} failed at constraint {}", constraint.3));
    }
    SuperNovaError::UnSatIndex(msg, index) if *msg == "r_secondary" || *msg == "l_secondary" => {
      let circuit_secondary: SuperNovaAugmentedCircuit<'_, G1, C2> = SuperNovaAugmentedCircuit::new(
        &pp.augmented_circuit_params_secondary,
        None,
        c_secondary,
        pp.ro_consts_circuit_secondary.clone(),
        num_augmented_circuits,
      );
      let mut cs: TestShapeCS<G2> = TestShapeCS::new();
      let _ = circuit_secondary.synthesize(&mut cs);
      cs.constraints
        .get(*index)
        .tap_some(|constraint| debug!("{msg} failed at constraint {}", constraint.3));
    }
    _ => (),
  }
}

const OPCODE_0: usize = 0;
const OPCODE_1: usize = 1;

struct TestROM<G1, G2, S>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  S: EnforcingStepCircuit<G2::Scalar> + Default,
{
  rom: Vec<usize>,
  _p: PhantomData<(G1, G2, S)>,
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

impl<G1, G2>
  NonUniformCircuit<G1, G2, TestROMCircuit<G1::Scalar>, TrivialSecondaryCircuit<G2::Scalar>>
  for TestROM<G1, G2, TrivialSecondaryCircuit<G2::Scalar>>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  fn num_circuits(&self) -> usize {
    2
  }

  fn primary_circuit(&self, circuit_index: usize) -> TestROMCircuit<G1::Scalar> {
    match circuit_index {
      0 => TestROMCircuit::Cubic(CubicCircuit::new(circuit_index, self.rom.len())),
      1 => TestROMCircuit::Square(SquareCircuit::new(circuit_index, self.rom.len())),
      _ => panic!("unsupported primary circuit index"),
    }
  }

  fn secondary_circuit(&self) -> TrivialSecondaryCircuit<G2::Scalar> {
    Default::default()
  }

  fn initial_circuit_index(&self) -> usize {
    self.rom[0]
  }
}

impl<G1, G2, S> TestROM<G1, G2, S>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  S: EnforcingStepCircuit<G2::Scalar> + Default,
{
  fn new(rom: Vec<usize>) -> Self {
    Self {
      rom,
      _p: Default::default(),
    }
  }

  fn num_steps(&self) -> usize {
    self.rom.len()
  }
}

fn test_trivial_nivc_with<G1, G2>()
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  // Here demo a simple RAM machine
  // - with 2 argumented circuit
  // - each argumented circuit contains primary and secondary circuit
  // - a memory commmitment via a public IO `rom` (like a program) to constraint the sequence execution

  // This test also ready to add more argumented circuit and ROM can be arbitrary length

  // ROM is for constraints the sequence of execution order for opcode
  // program counter initially point to 0

  // TODO: replace with memory commitment along with suggestion from Supernova 4.4 optimisations

  // This is mostly done with the existing Nova code. With additions of U_i[] and program_counter checks
  // in the augmented circuit.

  // To save the test time, after each step of iteration, RecursiveSNARK just verfiy the latest U_i[augmented_circuit_index] needs to be a satisfying instance.
  // TODO At the end of this test, RecursiveSNARK need to verify all U_i[] are satisfying instances

  let rom = vec![
    OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1,
    OPCODE_1,
  ]; // Rom can be arbitrary length.

  let test_rom = TestROM::<G1, G2, TrivialSecondaryCircuit<G2::Scalar>>::new(rom);
  let num_steps = test_rom.num_steps();

  let pp = PublicParams::new(&test_rom, &*default_ck_hint(), &*default_ck_hint());

  let initial_program_counter = test_rom.initial_program_counter();

  // extend z0_primary/secondary with rom content
  let mut z0_primary = vec![<G1 as Group>::Scalar::ONE];
  z0_primary.push(initial_program_counter);
  z0_primary.extend(
    test_rom
      .rom
      .iter()
      .map(|opcode| <G1 as Group>::Scalar::from(*opcode as u64)),
  );
  let z0_secondary = vec![<G2 as Group>::Scalar::ONE];

  let mut recursive_snark_option: Option<RecursiveSNARK<G1, G2>> = None;

  for _ in 0..num_steps {
    let program_counter = recursive_snark_option.as_ref().map_or_else(
      || initial_program_counter,
      |recursive_snark| recursive_snark.program_counter,
    );

    // The program counter directly specifies the next circuit index.
    let augmented_circuit_index = u32::from_le_bytes(
      // convert program counter from field to usize (only took le 4 bytes)
      program_counter.to_repr().as_ref()[0..4].try_into().unwrap(),
    ) as usize;

    let mut recursive_snark =
      recursive_snark_option.unwrap_or_else(|| match augmented_circuit_index {
        OPCODE_0 | OPCODE_1 => RecursiveSNARK::new(
          &pp,
          &test_rom,
          &test_rom.primary_circuit(augmented_circuit_index),
          &test_rom.secondary_circuit(),
          &z0_primary,
          &z0_secondary,
        )
        .unwrap(),
        _ => {
          unimplemented!()
        }
      });
    match augmented_circuit_index {
      OPCODE_0 | OPCODE_1 => {
        let circuit_primary = test_rom.primary_circuit(augmented_circuit_index);
        let circuit_secondary = test_rom.secondary_circuit();
        recursive_snark
          .prove_step(&pp, &circuit_primary, &circuit_secondary)
          .unwrap();
        recursive_snark
          .verify(&pp, augmented_circuit_index, &z0_primary, &z0_secondary)
          .map_err(|err| {
            print_constraints_name_on_error_index(
              &err,
              &pp,
              &circuit_primary,
              &circuit_secondary,
              test_rom.num_circuits(),
            )
          })
          .unwrap();
      }
      _ => (),
    }
    recursive_snark_option = Some(recursive_snark)
  }

  assert!(recursive_snark_option.is_some());

  // Now you can handle the Result using if let
  let RecursiveSNARK {
    zi_primary,
    zi_secondary,
    program_counter,
    ..
  } = &recursive_snark_option.unwrap();

  println!("zi_primary: {:?}", zi_primary);
  println!("zi_secondary: {:?}", zi_secondary);
  println!("final program_counter: {:?}", program_counter);
}

#[test]
#[tracing_test::traced_test]
fn test_trivial_nivc() {
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;

  // Expirementing with selecting the running claims for nifs
  test_trivial_nivc_with::<G1, G2>();
}

// In the following we use 1 to refer to the primary, and 2 to refer to the secondary circuit
fn test_recursive_circuit_with<G1, G2>(
  primary_params: &SuperNovaAugmentedCircuitParams,
  secondary_params: &SuperNovaAugmentedCircuitParams,
  ro_consts1: ROConstantsCircuit<G2>,
  ro_consts2: ROConstantsCircuit<G1>,
  num_constraints_primary: usize,
  num_constraints_secondary: usize,
) where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  // Initialize the shape and ck for the primary
  let step_circuit1 = TrivialTestCircuit::default();
  let arity1 = step_circuit1.arity();
  let circuit1: SuperNovaAugmentedCircuit<'_, G2, TrivialTestCircuit<<G2 as Group>::Base>> =
    SuperNovaAugmentedCircuit::new(primary_params, None, &step_circuit1, ro_consts1.clone(), 2);
  let mut cs: ShapeCS<G1> = ShapeCS::new();
  if let Err(e) = circuit1.synthesize(&mut cs) {
    panic!("{}", e)
  }
  let (shape1, ck1) = cs.r1cs_shape_and_key(&*default_ck_hint());
  assert_eq!(cs.num_constraints(), num_constraints_primary);

  // Initialize the shape and ck for the secondary
  let step_circuit2 = TrivialSecondaryCircuit::default();
  let arity2 = step_circuit2.arity();
  let circuit2: SuperNovaAugmentedCircuit<'_, G1, TrivialSecondaryCircuit<<G1 as Group>::Base>> =
    SuperNovaAugmentedCircuit::new(
      secondary_params,
      None,
      &step_circuit2,
      ro_consts2.clone(),
      2,
    );
  let mut cs: ShapeCS<G2> = ShapeCS::new();
  if let Err(e) = circuit2.synthesize(&mut cs) {
    panic!("{}", e)
  }
  let (shape2, ck2) = cs.r1cs_shape_and_key(&*default_ck_hint());
  assert_eq!(cs.num_constraints(), num_constraints_secondary);

  // Execute the base case for the primary
  let zero1 = <<G2 as Group>::Base as Field>::ZERO;
  let z0 = vec![zero1; arity1];
  let mut cs1 = SatisfyingAssignment::<G1>::new();
  let inputs1: SuperNovaAugmentedCircuitInputs<'_, G2> = SuperNovaAugmentedCircuitInputs::new(
    scalar_as_base::<G1>(zero1), // pass zero for testing
    zero1,
    &z0,
    None,
    None,
    None,
    None,
    Some(zero1),
    zero1,
  );
  let step_circuit = TrivialTestCircuit::default();
  let circuit1: SuperNovaAugmentedCircuit<'_, G2, TrivialTestCircuit<<G2 as Group>::Base>> =
    SuperNovaAugmentedCircuit::new(primary_params, Some(inputs1), &step_circuit, ro_consts1, 2);
  if let Err(e) = circuit1.synthesize(&mut cs1) {
    panic!("{}", e)
  }
  let (inst1, witness1) = cs1.r1cs_instance_and_witness(&shape1, &ck1).unwrap();
  // Make sure that this is satisfiable
  assert!(shape1.is_sat(&ck1, &inst1, &witness1).is_ok());

  // Execute the base case for the secondary
  let zero2 = <<G1 as Group>::Base as Field>::ZERO;
  let z0 = vec![zero2; arity2];
  let mut cs2 = SatisfyingAssignment::<G2>::new();
  let inputs2: SuperNovaAugmentedCircuitInputs<'_, G1> = SuperNovaAugmentedCircuitInputs::new(
    scalar_as_base::<G2>(zero2), // pass zero for testing
    zero2,
    &z0,
    None,
    None,
    Some(&inst1),
    None,
    None,
    zero2,
  );
  let step_circuit = TrivialSecondaryCircuit::default();
  let circuit2: SuperNovaAugmentedCircuit<'_, G1, TrivialSecondaryCircuit<<G1 as Group>::Base>> =
    SuperNovaAugmentedCircuit::new(
      secondary_params,
      Some(inputs2),
      &step_circuit,
      ro_consts2,
      2,
    );
  if let Err(e) = circuit2.synthesize(&mut cs2) {
    panic!("{}", e)
  }
  let (inst2, witness2) = cs2.r1cs_instance_and_witness(&shape2, &ck2).unwrap();
  // Make sure that it is satisfiable
  assert!(shape2.is_sat(&ck2, &inst2, &witness2).is_ok());
}

#[test]
fn test_recursive_circuit() {
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;
  let params1 = SuperNovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
  let params2 = SuperNovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);
  let ro_consts1: ROConstantsCircuit<G2> = PoseidonConstantsCircuit::default();
  let ro_consts2: ROConstantsCircuit<G1> = PoseidonConstantsCircuit::default();

  test_recursive_circuit_with::<G1, G2>(&params1, &params2, ro_consts1, ro_consts2, 9845, 12036);
}

fn test_pp_digest_with<G1, G2, T1, T2, NC>(non_uniform_circuit: &NC, expected: &str)
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  T1: StepCircuit<G1::Scalar>,
  T2: StepCircuit<G2::Scalar>,
  NC: NonUniformCircuit<G1, G2, T1, T2>,
{
  // TODO: add back in https://github.com/lurk-lab/arecibo/issues/53
  // // this tests public parameters with a size specifically intended for a spark-compressed SNARK
  // let pp_hint1 = Some(SPrime::<G1>::commitment_key_floor());
  // let pp_hint2 = Some(SPrime::<G2>::commitment_key_floor());
  let pp = PublicParams::<G1, G2, T1, T2>::new(
    non_uniform_circuit,
    &*default_ck_hint(),
    &*default_ck_hint(),
  );

  let digest_str = pp
    .digest()
    .to_repr()
    .as_ref()
    .iter()
    .fold(String::new(), |mut output, b| {
      let _ = write!(output, "{b:02x}");
      output
    });
  assert_eq!(digest_str, expected);
}

#[test]
fn test_supernova_pp_digest() {
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;

  let rom = vec![
    OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1,
    OPCODE_1,
  ]; // Rom can be arbitrary length.
  let test_rom = TestROM::<G1, G2, TrivialSecondaryCircuit<<G2 as Group>::Scalar>>::new(rom);

  test_pp_digest_with::<G1, G2, _, _, _>(
    &test_rom,
    "1ea5f38a96bbad918d2132d15ac3f463ee97c532988bb4fc16a761bfe7847300",
  );

  let rom = vec![
    OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1,
    OPCODE_1,
  ]; // Rom can be arbitrary length.
  let test_rom_grumpkin = TestROM::<
    bn256::Point,
    grumpkin::Point,
    TrivialSecondaryCircuit<<grumpkin::Point as Group>::Scalar>,
  >::new(rom);

  test_pp_digest_with::<bn256::Point, grumpkin::Point, _, _, _>(
    &test_rom_grumpkin,
    "09dc431db3be49a3e4f065a67c9d7260accdaed737fb0bc2abd70c1068b8df00",
  );

  let rom = vec![
    OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1, OPCODE_1, OPCODE_0, OPCODE_0, OPCODE_1,
    OPCODE_1,
  ]; // Rom can be arbitrary length.
  let test_rom_secp = TestROM::<
    secp256k1::Point,
    secq256k1::Point,
    TrivialSecondaryCircuit<<secq256k1::Point as Group>::Scalar>,
  >::new(rom);

  test_pp_digest_with::<secp256k1::Point, secq256k1::Point, _, _, _>(
    &test_rom_secp,
    "c695e71fb75c3235471fb53d5b6b02610ac698af294877c20b9d855398679102",
  );
}

// y is a non-deterministic hint representing the cube root of the input at a step.
#[derive(Clone, Debug)]
struct CubeRootCheckingCircuit<F: PrimeField> {
  y: Option<F>,
}

impl<F> StepCircuit<F> for CubeRootCheckingCircuit<F>
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
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let x = &z[0];

    // we allocate a variable and set it to the provided non-deterministic hint.
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      self.y.ok_or(SynthesisError::AssignmentMissing)
    })?;

    // We now check if y = x^{1/3} by checking if y^3 = x
    let y_sq = y.square(cs.namespace(|| "y_sq"))?;
    let y_cube = y_sq.mul(cs.namespace(|| "y_cube"), &y)?;

    cs.enforce(
      || "y^3 = x",
      |lc| lc + y_cube.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + x.get_variable(),
    );

    let next_pc = alloc_const(&mut cs.namespace(|| "next_pc"), F::ONE)?;

    Ok((Some(next_pc), vec![y]))
  }
}

// y is a non-deterministic hint representing the fifth root of the input at a step.
#[derive(Clone, Debug)]
struct FifthRootCheckingCircuit<F: PrimeField> {
  y: Option<F>,
}

impl<F> StepCircuit<F> for FifthRootCheckingCircuit<F>
where
  F: PrimeField,
{
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

    // we allocate a variable and set it to the provided non-deterministic hint.
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      self.y.ok_or(SynthesisError::AssignmentMissing)
    })?;

    // We now check if y = x^{1/5} by checking if y^5 = x
    let y_sq = y.square(cs.namespace(|| "y_sq"))?;
    let y_quad = y_sq.square(cs.namespace(|| "y_quad"))?;
    let y_pow_5 = y_quad.mul(cs.namespace(|| "y_fifth"), &y)?;

    cs.enforce(
      || "y^5 = x",
      |lc| lc + y_pow_5.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + x.get_variable(),
    );

    let next_pc = alloc_const(&mut cs.namespace(|| "next_pc"), F::ZERO)?;

    Ok((Some(next_pc), vec![y]))
  }
}

#[derive(Clone, Debug)]
enum RootCheckingCircuit<F: PrimeField> {
  Cube(CubeRootCheckingCircuit<F>),
  Fifth(FifthRootCheckingCircuit<F>),
}

impl<F: PrimeField> RootCheckingCircuit<F> {
  fn new(num_steps: usize) -> (Vec<F>, Vec<Self>) {
    let mut powers = Vec::new();
    let rng = &mut rand::rngs::OsRng;
    let mut seed = F::random(rng);

    for i in 0..num_steps + 1 {
      let seed_sq = seed.clone().square();
      // Cube-root and fifth-root circuits alternate. We compute the hints backward, so the calculations appear to be
      // associated with the 'wrong' circuit. The final circuit is discarded, and only the final seed is used (as z_0).
      powers.push(if i % 2 == num_steps % 2 {
        seed *= seed_sq;
        Self::Fifth(FifthRootCheckingCircuit { y: Some(seed) })
      } else {
        seed *= seed_sq.clone().square();
        Self::Cube(CubeRootCheckingCircuit { y: Some(seed) })
      })
    }

    // reverse the powers to get roots
    let roots = powers.into_iter().rev().collect::<Vec<Self>>();
    (vec![roots[0].get_y().unwrap()], roots[1..].to_vec())
  }

  fn get_y(&self) -> Option<F> {
    match self {
      Self::Fifth(x) => x.y,
      Self::Cube(x) => x.y,
    }
  }
}

impl<F> StepCircuit<F> for RootCheckingCircuit<F>
where
  F: PrimeField,
{
  fn arity(&self) -> usize {
    1
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
      Self::Cube(c) => c.synthesize(cs, pc, z),
      Self::Fifth(c) => c.synthesize(cs, pc, z),
    }
  }
}

impl<G1, G2>
  NonUniformCircuit<G1, G2, RootCheckingCircuit<G1::Scalar>, TrivialSecondaryCircuit<G1::Base>>
  for RootCheckingCircuit<G1::Scalar>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  fn num_circuits(&self) -> usize {
    2
  }

  fn primary_circuit(&self, circuit_index: usize) -> Self {
    match circuit_index {
      0 => Self::Cube(CubeRootCheckingCircuit { y: None }),
      1 => Self::Fifth(FifthRootCheckingCircuit { y: None }),
      _ => unreachable!(),
    }
  }

  fn secondary_circuit(&self) -> TrivialSecondaryCircuit<G1::Base> {
    TrivialSecondaryCircuit::<G1::Base>::default()
  }
}

fn test_nivc_nondet_with<G1, G2>()
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  // this is due to the reliance on Abomonation
  <<G1 as Group>::Scalar as PrimeField>::Repr: Abomonation,
  <<G2 as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
  let circuit_secondary = TrivialSecondaryCircuit::default();

  let num_steps = 3;

  // produce non-deterministic hint
  let (z0_primary, roots) = RootCheckingCircuit::new(num_steps);
  assert_eq!(num_steps, roots.len());
  let z0_secondary = vec![<G2 as Group>::Scalar::ZERO];

  // produce public parameters
  let pp = PublicParams::<
    G1,
    G2,
    RootCheckingCircuit<<G1 as Group>::Scalar>,
    TrivialSecondaryCircuit<<G2 as Group>::Scalar>,
  >::new(&roots[0], &*default_ck_hint(), &*default_ck_hint());
  // produce a recursive SNARK

  let circuit_primary = &roots[0];

  let mut recursive_snark = RecursiveSNARK::<G1, G2>::new(
    &pp,
    circuit_primary,
    circuit_primary,
    &circuit_secondary,
    &z0_primary,
    &z0_secondary,
  )
  .map_err(|err| {
    print_constraints_name_on_error_index(
      &err,
      &pp,
      circuit_primary,
      &circuit_secondary,
      <RootCheckingCircuit<G1::Scalar> as NonUniformCircuit<
        G1,
        G2,
        RootCheckingCircuit<G1::Scalar>,
        TrivialSecondaryCircuit<G1::Base>,
      >>::num_circuits(circuit_primary),
    )
  })
  .unwrap();

  for circuit_primary in roots.iter().take(num_steps) {
    let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
    assert!(res
      .map_err(|err| {
        print_constraints_name_on_error_index(
          &err,
          &pp,
          circuit_primary,
          &circuit_secondary,
          <RootCheckingCircuit<G1::Scalar> as NonUniformCircuit<
            G1,
            G2,
            RootCheckingCircuit<G1::Scalar>,
            TrivialSecondaryCircuit<G1::Base>,
          >>::num_circuits(circuit_primary),
        )
      })
      .is_ok());

    // verify the recursive SNARK
    let res = recursive_snark
      .verify(&pp, 0, &z0_primary, &z0_secondary)
      .map_err(|err| {
        print_constraints_name_on_error_index(
          &err,
          &pp,
          circuit_primary,
          &circuit_secondary,
          <RootCheckingCircuit<G1::Scalar> as NonUniformCircuit<
            G1,
            G2,
            RootCheckingCircuit<G1::Scalar>,
            TrivialSecondaryCircuit<G1::Base>,
          >>::num_circuits(circuit_primary),
        )
      });
    assert!(res.is_ok());
  }
}

#[test]
fn test_nivc_nondet() {
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;

  test_nivc_nondet_with::<G1, G2>();
  test_nivc_nondet_with::<bn256::Point, grumpkin::Point>();
  test_nivc_nondet_with::<secp256k1::Point, secq256k1::Point>();
}
