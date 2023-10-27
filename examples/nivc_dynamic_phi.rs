use std::marker::PhantomData;

use bellpepper::gadgets::{blake2s::blake2s, multipack::pack_bits, sha256::sha256};
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use blake2s_simd::Params;
use ff::{Field, PrimeField, PrimeFieldBits};
use rand::Rng;
use rand_core::OsRng;
use sha2::{Digest, Sha256};

use nova_snark::{
  supernova::{NonUniformCircuit, PublicParams, RecursiveSNARK},
  traits::{
    circuit_supernova::{StepCircuit, TrivialSecondaryCircuit},
    Group,
  },
};

const NUM_STEPS: usize = 10;
const NUM_BYTES: usize = 10;

#[derive(Clone, Debug)]
struct SHACircuit<F: PrimeField> {
  next_pc: bool,
  _p: PhantomData<F>,
}

impl<F: PrimeField> SHACircuit<F> {
  fn new(next_pc: bool) -> Self {
    Self {
      next_pc,
      _p: PhantomData,
    }
  }
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

    let preimage_bits = preimage.to_bits_le_strict(cs.namespace(|| "sha_preimage_bits"))?;

    let (preimage_bits, _) = preimage_bits.split_at(8 * NUM_BYTES);

    let preimage_bits = preimage_bits
      .chunks(8)
      .map(|chunk| {
        let mut chunk = chunk.to_vec();
        chunk.reverse();
        chunk
      })
      .flatten()
      .collect::<Vec<_>>();

    let digest_bits = sha256(cs.namespace(|| "sha256"), preimage_bits.as_slice())?;

    let (digest_bits, _) = digest_bits.split_at(8 * NUM_BYTES);

    let next_pc_bit = &digest_bits[7];

    let digest_bits = digest_bits
      .chunks(8)
      .map(|chunk| {
        let mut chunk = chunk.to_vec();
        chunk.reverse();
        chunk
      })
      .flatten()
      .collect::<Vec<Boolean>>();

    let digest = pack_bits(cs.namespace(|| "digest_from_bits"), digest_bits.as_slice())?;

    let new_pc = AllocatedNum::alloc(cs.namespace(|| "next_pc"), || {
      if self.next_pc {
        Ok(F::ONE)
      } else {
        Ok(F::ZERO)
      }
    })?;

    cs.enforce(
      || "enforce new_pc is first bit",
      |lc| lc + CS::one(),
      |lc| lc + new_pc.get_variable(),
      |_| next_pc_bit.lc(CS::one(), F::ONE),
    );

    Ok((Some(new_pc), vec![digest]))
  }
}

#[derive(Clone, Debug)]
struct BlakeCircuit<F: PrimeField> {
  next_pc: bool,
  _p: PhantomData<F>,
}

impl<F: PrimeField> BlakeCircuit<F> {
  fn new(next_pc: bool) -> Self {
    Self {
      next_pc,
      _p: PhantomData,
    }
  }
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

    let preimage_bits = preimage.to_bits_le_strict(cs.namespace(|| "blake_preimage_bits"))?;

    let (preimage_bits, _) = preimage_bits.split_at(8 * NUM_BYTES);

    let digest_bits = blake2s(
      cs.namespace(|| "blake2s"),
      preimage_bits.as_ref(),
      b"personal",
    )?;

    let (digest_bits, _) = digest_bits.split_at(8 * NUM_BYTES);

    let next_pc_bit = digest_bits.first();

    let digest = pack_bits(cs.namespace(|| "digest_from_bits"), digest_bits)?;

    let new_pc = AllocatedNum::alloc(cs.namespace(|| "next_pc"), || {
      if self.next_pc {
        Ok(F::ONE)
      } else {
        Ok(F::ZERO)
      }
    })?;

    cs.enforce(
      || "enforce new_pc is first bit",
      |lc| lc + CS::one(),
      |lc| lc + new_pc.get_variable(),
      |_| next_pc_bit.unwrap().lc(CS::one(), F::ONE),
    );

    Ok((Some(new_pc), vec![digest]))
  }
}

#[derive(Debug)]
struct ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  next_pc: bool,
  _p: PhantomData<(G1, G2)>,
}

impl<G1, G2> ExampleSteps<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  <G1 as Group>::Scalar: PrimeFieldBits,
{
  fn new(preimage: <G1 as Group>::Scalar) -> (Vec<bool>, Self) {
    let mut hasher = Sha256::new();
    let mut preimage_repr = preimage.to_repr();
    let preimage_bytes: &mut [u8; 32] = preimage_repr.as_mut().try_into().expect("wrong size");

    let first_input: &[u8; NUM_BYTES] = preimage_bytes[..NUM_BYTES].try_into().expect("wrong size");

    hasher.update(first_input);
    let digest = hasher.finalize();

    let mut hashes: Vec<[u8; NUM_BYTES]> =
      vec![digest[..NUM_BYTES].try_into().expect("wrong size")];

    for _ in 0..NUM_STEPS {
      let last_hash = hashes.last_mut().unwrap();

      if last_hash.first().unwrap() & 1 == 0 {
        let mut hasher = Sha256::new();

        hasher.update(last_hash[..NUM_BYTES].as_ref());

        let digest = hasher.finalize();

        hashes.push(digest[..NUM_BYTES].try_into().expect("wrong size"));
      } else {
        let digest = Params::new()
          .hash_length(32)
          .personal(b"personal")
          .hash(&last_hash[..NUM_BYTES]);

        hashes.push(
          digest.as_ref()[..NUM_BYTES]
            .try_into()
            .expect("wrong array length"),
        );
      }
    }

    let hints: Vec<bool> = hashes
      .into_iter()
      .map(|hash| hash.first().unwrap() & 1 == 1)
      .collect();

    (
      hints.clone(),
      Self {
        next_pc: hints[0],
        _p: PhantomData,
      },
    )
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
      Self::Sha(_) => 1,
      Self::Blake(_) => 1,
    }
  }

  fn circuit_index(&self) -> usize {
    match self {
      Self::Sha(_) => 0,
      Self::Blake(_) => 1,
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
      0 => ExampleCircuit::Sha(SHACircuit::new(self.next_pc)),
      1 => ExampleCircuit::Blake(BlakeCircuit::new(self.next_pc)),
      _ => panic!("invalid circuit index"),
    }
  }

  fn secondary_circuit(&self) -> TrivialSecondaryCircuit<G2::Scalar> {
    Default::default()
  }
}

fn main() {
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;

  let mut rng = OsRng;

  let mut preimage_bytes = [0u8; 32];

  for idx in 0..NUM_BYTES {
    preimage_bytes[idx] = rng.gen::<u8>();
  }

  let initial_preimage = <G1 as Group>::Scalar::from_repr(preimage_bytes);

  let initial_preimage = initial_preimage.unwrap();

  let (hints, example) = ExampleSteps::<G1, G2>::new(initial_preimage);

  let pp = PublicParams::new(&example);

  let initial_pc = example.initial_program_counter();
  let augmented_circuit_index = field_as_usize(initial_pc);

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

  for next_pc in hints.into_iter() {
    let example = ExampleSteps::<G1, G2> {
      next_pc,
      _p: PhantomData,
    };

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

  println!("proving and verifying done");
}

// TODO: This should be factored out as described in issue #64
fn field_as_usize<F: PrimeField>(x: F) -> usize {
  u32::from_le_bytes(x.to_repr().as_ref()[0..4].try_into().unwrap()) as usize
}
