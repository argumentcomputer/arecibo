//! Demonstrates performance gain that comes from using Zeromorph.
//! Example circuits ('Sha256Circuit' and 'TestTrivialCircuit') are taken from Sha256 benches.
use abomonation::Abomonation;
use bellpepper::gadgets::{sha256::sha256, Assignment};
use bellpepper_core::{
  boolean::{AllocatedBit, Boolean},
  num::{AllocatedNum, Num},
  ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use flate2::{write::ZlibEncoder, Compression};
use nova_snark::traits::evaluation::EvaluationEngineTrait;
use nova_snark::traits::snark::RelaxedR1CSSNARKTrait;
use nova_snark::{
  traits::{
    circuit::{StepCircuit, TrivialCircuit},
    Group,
  },
  CompressedSNARK, RecursiveSNARK,
};
use sha2::{Digest, Sha256};
use std::marker::PhantomData;
use std::time::Instant;

#[derive(Clone, Debug)]
struct Sha256Circuit<Scalar: PrimeField> {
  preimage: Vec<u8>,
  _p: PhantomData<Scalar>,
}

impl<Scalar: PrimeField + PrimeFieldBits> Sha256Circuit<Scalar> {
  pub fn new(preimage: Vec<u8>) -> Self {
    Self {
      preimage,
      _p: PhantomData,
    }
  }
}

impl<Scalar: PrimeField + PrimeFieldBits> StepCircuit<Scalar> for Sha256Circuit<Scalar> {
  fn arity(&self) -> usize {
    1
  }

  fn synthesize<CS: ConstraintSystem<Scalar>>(
    &self,
    cs: &mut CS,
    _z: &[AllocatedNum<Scalar>],
  ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError> {
    let mut z_out: Vec<AllocatedNum<Scalar>> = Vec::new();

    let bit_values: Vec<_> = self
      .preimage
      .clone()
      .into_iter()
      .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
      .map(Some)
      .collect();
    assert_eq!(bit_values.len(), self.preimage.len() * 8);

    let preimage_bits = bit_values
      .into_iter()
      .enumerate()
      .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {i}")), b))
      .map(|b| b.map(Boolean::from))
      .collect::<Result<Vec<_>, _>>()?;

    let hash_bits = sha256(cs.namespace(|| "sha256"), &preimage_bits)?;

    for (i, hash_bits) in hash_bits.chunks(256_usize).enumerate() {
      let mut num = Num::<Scalar>::zero();
      let mut coeff = Scalar::ONE;
      for bit in hash_bits {
        num = num.add_bool_with_coeff(CS::one(), bit, coeff);

        coeff = coeff.double();
      }

      let hash = AllocatedNum::alloc(cs.namespace(|| format!("input {i}")), || {
        Ok(*num.get_value().get()?)
      })?;

      // num * 1 = hash
      cs.enforce(
        || format!("packing constraint {i}"),
        |_| num.lc(Scalar::ONE),
        |lc| lc + CS::one(),
        |lc| lc + hash.get_variable(),
      );
      z_out.push(hash);
    }

    // sanity check with the hasher
    let mut hasher = Sha256::new();
    hasher.update(&self.preimage);
    let hash_result = hasher.finalize();

    let mut s = hash_result
      .iter()
      .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

    for b in hash_bits {
      match b {
        Boolean::Is(b) => {
          assert!(s.next().unwrap() == b.get_value().unwrap());
        }
        Boolean::Not(b) => {
          assert!(s.next().unwrap() != b.get_value().unwrap());
        }
        Boolean::Constant(_b) => {
          panic!("Can't reach here")
        }
      }
    }

    Ok(z_out)
  }
}

fn example_pp_spartan_zeromorph<G1, G2, E1, E2>()
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  E1: EvaluationEngineTrait<G1>,
  E2: EvaluationEngineTrait<G2>,
  // this is due to the reliance on Abomonation
  <<G1 as Group>::Scalar as PrimeField>::Repr: Abomonation,
  <<G2 as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
  println!("PP-SPARTAN + ZEROMORPH");

  let circuit_primary = Sha256Circuit::<<G1 as Group>::Scalar>::new(vec![0u8; 1 << 2]);
  let circuit_secondary = TrivialCircuit::default();

  // Produce public parameters
  let start = Instant::now();
  let pp = nova_snark::PublicParams::<
    G1,
    G2,
    Sha256Circuit<<G1 as Group>::Scalar>,
    TrivialCircuit<<G2 as Group>::Scalar>,
  >::new(
    &circuit_primary,
    &circuit_secondary,
    Some(SPrime::<_, E1>::commitment_key_floor()),
    Some(SPrime::<_, E2>::commitment_key_floor()),
  );

  println!("PublicParams::setup, took {:?} ", start.elapsed());

  let z0_primary = vec![<G1 as Group>::Scalar::from(2u64)];
  let z0_secondary = vec![<G2 as Group>::Scalar::from(2u64)];

  // produce a recursive SNARK
  let mut recursive_snark: RecursiveSNARK<
    G1,
    G2,
    Sha256Circuit<<G1 as Group>::Scalar>,
    TrivialCircuit<<G2 as Group>::Scalar>,
  > = RecursiveSNARK::new(
    &pp,
    &circuit_primary,
    &circuit_secondary,
    z0_primary.clone(),
    z0_secondary.clone(),
  );

  let num_steps = 5;
  for i in 0..num_steps {
    let start = Instant::now();
    let res = recursive_snark.prove_step(
      &pp,
      &circuit_primary,
      &circuit_secondary,
      z0_primary.clone(),
      z0_secondary.clone(),
    );
    assert!(res.is_ok());
    println!(
      "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
      i,
      res.is_ok(),
      start.elapsed()
    );
  }

  // verify the recursive SNARK
  let start = Instant::now();
  let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
  println!(
    "RecursiveSNARK::verify: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());

  // produce a compressed SNARK
  let (pk, vk) = CompressedSNARK::<_, _, _, _, SPrime<G1, E1>, SPrime<G2, E2>>::setup(&pp).unwrap();

  let start = Instant::now();
  let res = CompressedSNARK::<_, _, _, _, SPrime<G1, E1>, SPrime<G2, E2>>::prove(
    &pp,
    &pk,
    &recursive_snark,
  );
  println!(
    "CompressedSNARK::prove: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());
  let compressed_snark = res.unwrap();
  let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
  bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
  let compressed_snark_encoded = encoder.finish().unwrap();
  println!(
    "CompressedSNARK::len {:?} bytes",
    compressed_snark_encoded.len()
  );

  // verify the compressed SNARK
  let start = Instant::now();
  let res = compressed_snark.verify(&vk, num_steps, z0_primary, z0_secondary);
  println!(
    "CompressedSNARK::verify: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());
  println!("=========================================================");
}

fn example_regular_spartan_zeromorph<G1, G2, S1, S2>()
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  // this is due to the reliance on Abomonation
  <<G1 as Group>::Scalar as PrimeField>::Repr: Abomonation,
  <<G2 as Group>::Scalar as PrimeField>::Repr: Abomonation,
  S1: RelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  println!("'REGULAR' SPARTAN + ZEROMORPH");

  let circuit_primary = Sha256Circuit::<<G1 as Group>::Scalar>::new(vec![0u8; 1 << 2]);
  let circuit_secondary = TrivialCircuit::default();

  // Produce public parameters
  let start = Instant::now();
  let pp = nova_snark::PublicParams::<
    G1,
    G2,
    Sha256Circuit<<G1 as Group>::Scalar>,
    TrivialCircuit<<G2 as Group>::Scalar>,
  >::new(&circuit_primary, &circuit_secondary, None, None);

  println!("PublicParams::setup, took {:?} ", start.elapsed());

  let z0_primary = vec![<G1 as Group>::Scalar::from(2u64)];
  let z0_secondary = vec![<G2 as Group>::Scalar::from(2u64)];

  // produce a recursive SNARK
  let mut recursive_snark: RecursiveSNARK<
    G1,
    G2,
    Sha256Circuit<<G1 as Group>::Scalar>,
    TrivialCircuit<<G2 as Group>::Scalar>,
  > = RecursiveSNARK::new(
    &pp,
    &circuit_primary,
    &circuit_secondary,
    z0_primary.clone(),
    z0_secondary.clone(),
  );

  let num_steps = 5;
  for i in 0..num_steps {
    let start = Instant::now();
    let res = recursive_snark.prove_step(
      &pp,
      &circuit_primary,
      &circuit_secondary,
      z0_primary.clone(),
      z0_secondary.clone(),
    );
    assert!(res.is_ok());
    println!(
      "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
      i,
      res.is_ok(),
      start.elapsed()
    );
  }

  // verify the recursive SNARK
  let start = Instant::now();
  let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
  println!(
    "RecursiveSNARK::verify: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());

  // produce a compressed SNARK
  let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

  let start = Instant::now();
  let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
  println!(
    "CompressedSNARK::prove: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());
  let compressed_snark = res.unwrap();
  let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
  bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
  let compressed_snark_encoded = encoder.finish().unwrap();
  println!(
    "CompressedSNARK::len {:?} bytes",
    compressed_snark_encoded.len()
  );

  // verify the compressed SNARK
  let start = Instant::now();
  let res = compressed_snark.verify(&vk, num_steps, z0_primary, z0_secondary);
  println!(
    "CompressedSNARK::verify: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());
  println!("=========================================================");
}

type ZM<E> = nova_snark::provider::non_hiding_zeromorph::ZMPCS<E>;
type EE<G> = nova_snark::provider::ipa_pc::EvaluationEngine<G>;
type S<G, EE> = nova_snark::spartan::snark::RelaxedR1CSSNARK<G, EE>;
type SPrime<G, EE> = nova_snark::spartan::ppsnark::RelaxedR1CSSNARK<G, EE>;

/// cargo run --release --example sha256-zeromorph
fn main() {
  example_pp_spartan_zeromorph::<
    halo2curves::bn256::G1,
    halo2curves::grumpkin::G1,
    ZM<halo2curves::bn256::Bn256>,
    EE<_>,
  >();

  example_regular_spartan_zeromorph::<
    halo2curves::bn256::G1,
    halo2curves::grumpkin::G1,
    S<halo2curves::bn256::G1, ZM<halo2curves::bn256::Bn256>>,
    S<halo2curves::grumpkin::G1, EE<_>>,
  >();
}
