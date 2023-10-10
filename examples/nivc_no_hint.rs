use std::marker::PhantomData;

use bellpepper::gadgets::{blake2s::blake2s, multipack::pack_bits, sha256::sha256};
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::Field;
use ff::{PrimeField, PrimeFieldBits};
use rand::rngs::OsRng;

use nova_snark::{
  supernova::{NonUniformCircuit, PublicParams, RecursiveSNARK},
  traits::{
    circuit_supernova::{StepCircuit, TrivialSecondaryCircuit},
    Group,
  },
};

const NUM_STEPS: usize = 10;

#[derive(Clone, Debug, Default)]
struct SHACircuit<F: PrimeField> {
  _p: PhantomData<F>,
}

impl<F: PrimeField + PrimeFieldBits> StepCircuit<F> for SHACircuit<F> {
  fn arity(&self) -> usize {
    1
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let preimage = &z[0];

    let mut preimage_bits = preimage.to_bits_le(cs.namespace(|| "sha_preimage_bits"))?;

    preimage_bits.truncate(160);

    let digest_bits = sha256(cs.namespace(|| "sha256"), &preimage_bits)?;

    let digest = pack_bits(cs.namespace(|| "digest_from_bits"), &digest_bits)?;

    let new_pc = digest_bits[0].get_value().map(|bit| {
      let new_pc = if bit {
        AllocatedNum::alloc(cs.namespace(|| "sha_branch"), || Ok(F::ONE))
      } else {
        AllocatedNum::alloc(cs.namespace(|| "blake_branch"), || Ok(F::ZERO))
      }
      .unwrap();
      cs.enforce(
        || "enforce new_pc",
        |lc| lc + CS::one(),
        |lc| lc + new_pc.get_variable(),
        |_lc| digest_bits[0].lc(CS::one(), F::ONE),
      );
      new_pc
    });

    if _pc.is_some() {
      assert!(new_pc.is_some())
    }

    Ok((new_pc, vec![digest]))
  }
}

#[derive(Clone, Debug, Default)]
struct BlakeCircuit<F: PrimeField> {
  _p: PhantomData<F>,
}

impl<F: PrimeField + PrimeFieldBits> StepCircuit<F> for BlakeCircuit<F> {
  fn arity(&self) -> usize {
    1
  }
  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let preimage = &z[0];

    let mut preimage_bits = preimage.to_bits_le(cs.namespace(|| "blake_preimage_bits"))?;

    preimage_bits.truncate(160);

    let digest_bits = blake2s(cs.namespace(|| "blake2s"), &preimage_bits, b"personal")?;

    let digest = pack_bits(cs.namespace(|| "digest_from_bits"), &digest_bits)?;

    let new_pc = digest_bits[0].get_value().map(|bit| {
      let new_pc = if bit {
        AllocatedNum::alloc(cs.namespace(|| "sha_branch"), || Ok(F::ONE))
      } else {
        AllocatedNum::alloc(cs.namespace(|| "blake_branch"), || Ok(F::ZERO))
      }
      .unwrap();
      cs.enforce(
        || "enforce new_pc",
        |lc| lc + CS::one(),
        |lc| lc + new_pc.get_variable(),
        |_lc| digest_bits[0].lc(CS::one(), F::ONE),
      );
      new_pc
    });

    if _pc.is_some() {
      assert!(new_pc.is_some())
    }

    Ok((new_pc, vec![digest]))
  }
}

#[derive(Debug)]
struct ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  _p: PhantomData<(G1, G2)>,
}

impl<G1, G2> ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  fn new() -> Self {
    Self { _p: PhantomData }
  }
}

#[derive(Debug, Clone)]
enum ExampleCircuit<F: PrimeField + PrimeFieldBits> {
  Sha(SHACircuit<F>),
  Blake(BlakeCircuit<F>),
}

impl<F: PrimeField + PrimeFieldBits> StepCircuit<F> for ExampleCircuit<F> {
  fn arity(&self) -> usize {
    match self {
      Self::Blake(_) => 1,
      Self::Sha(_) => 1,
    }
  }

  fn circuit_index(&self) -> usize {
    match self {
      Self::Blake(_) => 0,
      Self::Sha(_) => 1,
    }
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    match self {
      Self::Blake(blake_circuit) => blake_circuit.synthesize(cs, pc, z),
      Self::Sha(sha_circuit) => sha_circuit.synthesize(cs, pc, z),
    }
  }
}

impl<G1, G2>
  NonUniformCircuit<G1, G2, ExampleCircuit<G1::Scalar>, TrivialSecondaryCircuit<G2::Scalar>>
  for ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  fn num_circuits(&self) -> usize {
    2
  }

  fn initial_program_counter(&self) -> <G1 as Group>::Scalar {
    <G1 as Group>::Scalar::ZERO
  }

  fn primary_circuit(&self, circuit_index: usize) -> ExampleCircuit<G1::Scalar> {
    match circuit_index {
      0 => ExampleCircuit::Blake(Default::default()),
      1 => ExampleCircuit::Sha(Default::default()),
      _ => panic!("This shouldn't happen"),
    }
  }

  fn secondary_circuit(&self) -> TrivialSecondaryCircuit<G2::Scalar> {
    Default::default()
  }
}

fn main() {
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;

  let example = ExampleSteps::<G1, G2>::new();

  let pp = PublicParams::new(&example);

  let initial_pc = example.initial_program_counter();

  let augmented_circuit_index = field_as_usize(initial_pc);

  let rng = OsRng;
  let initial_preimage = <G1 as Group>::Scalar::random(rng);

  let z0_primary = vec![initial_preimage];
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

  for _ in 0..NUM_STEPS {
    let program_counter = recursive_snark.get_program_counter();

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
}

// TODO: This should be factored out as described in issue #64
fn field_as_usize<F: PrimeField>(x: F) -> usize {
  u32::from_le_bytes(x.to_repr().as_ref()[0..4].try_into().unwrap()) as usize
}
