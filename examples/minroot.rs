//! Demonstrates how to use Nova to produce a recursive proof of the correct execution of
//! iterations of the `MinRoot` function, thereby realizing a Nova-based verifiable delay function (VDF).
//! We execute a configurable number of iterations of the `MinRoot` function per step of Nova's recursion.
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use flate2::{write::ZlibEncoder, Compression};
use nova_snark::{
  provider::{PallasEngine, VestaEngine},
  traits::{
    circuit::{StepCircuit, TrivialCircuit},
    snark::default_ck_hint,
    Engine,
  },
  CompressedSNARK, PublicParams, RecursiveSNARK,
};
use num_bigint::BigUint;
use std::time::Instant;
use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

type E1 = PallasEngine;
type E2 = VestaEngine;

#[cfg(feature = "abomonate")]
mod utils {
  use super::*;
  use std::{io::Write, mem::size_of};

  pub const FILEPATH: &str = "/tmp/data";
  /// Unspeakable horrors from a type safety PoV
  unsafe fn any_as_u8_slice<T: Sized>(p: &T) -> &[u8] {
    ::core::slice::from_raw_parts((p as *const T) as *const u8, ::core::mem::size_of::<T>())
  }

  /// this is dangerous
  #[allow(non_snake_case)]
  unsafe fn entomb_F<F: PrimeField, W: Write>(f: &F, bytes: &mut W) -> std::io::Result<()> {
    println!("entomb: {}", size_of::<F>());
    // this is  dangerous
    bytes.write_all(any_as_u8_slice(&f))?;
    Ok(())
  }

  /// this is dangerous
  #[allow(non_snake_case)]
  unsafe fn exhume_F<'a, F: PrimeField>(f: &mut F, bytes: &'a mut [u8]) -> &'a mut [u8] {
    let (mine, rest) = bytes.split_at_mut(size_of::<F>());
    let mine = (mine as *const [u8]) as *const F;
    std::ptr::write(f, std::ptr::read(mine));
    rest
  }
  impl<F: PrimeField> abomonation::Abomonation for MinRootIteration<F> {
    unsafe fn entomb<W: Write>(&self, bytes: &mut W) -> std::io::Result<()> {
      entomb_F(&self.x_i, bytes)?;
      entomb_F(&self.y_i, bytes)?;
      entomb_F(&self.x_i_plus_1, bytes)?;
      entomb_F(&self.y_i_plus_1, bytes)?;
      Ok(())
    }

    unsafe fn exhume<'b>(&mut self, bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
      let bytes = exhume_F(&mut self.x_i, bytes);
      let bytes = exhume_F(&mut self.y_i, bytes);
      let bytes = exhume_F(&mut self.x_i_plus_1, bytes);
      let bytes = exhume_F(&mut self.y_i_plus_1, bytes);
      Some(bytes)
    }

    fn extent(&self) -> usize {
      0
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
struct MinRootIteration<F: PrimeField> {
  x_i: F,
  y_i: F,
  x_i_plus_1: F,
  y_i_plus_1: F,
}

impl<F: PrimeField> MinRootIteration<F> {
  // produces a sample non-deterministic advice, executing one invocation of MinRoot per step
  fn new(num_iters: usize, x_0: &F, y_0: &F) -> (Vec<F>, Vec<Self>) {
    // although this code is written generically, it is tailored to Pallas' scalar field
    // (p - 3 / 5)
    let exp = BigUint::parse_bytes(
      b"23158417847463239084714197001737581570690445185553317903743794198714690358477",
      10,
    )
    .unwrap();

    let mut res = Vec::new();
    let mut x_i = *x_0;
    let mut y_i = *y_0;
    for _i in 0..num_iters {
      let x_i_plus_1 = (x_i + y_i).pow_vartime(exp.to_u64_digits()); // computes the fifth root of x_i + y_i

      // sanity check
      if cfg!(debug_assertions) {
        let sq = x_i_plus_1 * x_i_plus_1;
        let quad = sq * sq;
        let fifth = quad * x_i_plus_1;
        assert_eq!(fifth, x_i + y_i);
      }

      let y_i_plus_1 = x_i;

      res.push(Self {
        x_i,
        y_i,
        x_i_plus_1,
        y_i_plus_1,
      });

      x_i = x_i_plus_1;
      y_i = y_i_plus_1;
    }

    let z0 = vec![*x_0, *y_0];

    (z0, res)
  }
}

#[derive(Clone, Debug, PartialEq)]
struct MinRootCircuit<F: PrimeField> {
  seq: Vec<MinRootIteration<F>>,
}

impl<F: PrimeField> StepCircuit<F> for MinRootCircuit<F> {
  fn arity(&self) -> usize {
    2
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let mut z_out: Result<Vec<AllocatedNum<F>>, SynthesisError> =
      Err(SynthesisError::AssignmentMissing);

    // use the provided inputs
    let x_0 = z[0].clone();
    let y_0 = z[1].clone();

    // variables to hold running x_i and y_i
    let mut x_i = x_0;
    let mut y_i = y_0;
    for i in 0..self.seq.len() {
      // non deterministic advice
      let x_i_plus_1 =
        AllocatedNum::alloc(cs.namespace(|| format!("x_i_plus_1_iter_{i}")), || {
          Ok(self.seq[i].x_i_plus_1)
        })?;

      // check the following conditions hold:
      // (i) x_i_plus_1 = (x_i + y_i)^{1/5}, which can be more easily checked with x_i_plus_1^5 = x_i + y_i
      // (ii) y_i_plus_1 = x_i
      // (1) constraints for condition (i) are below
      // (2) constraints for condition (ii) is avoided because we just used x_i wherever y_i_plus_1 is used
      let x_i_plus_1_sq = x_i_plus_1.square(cs.namespace(|| format!("x_i_plus_1_sq_iter_{i}")))?;
      let x_i_plus_1_quad =
        x_i_plus_1_sq.square(cs.namespace(|| format!("x_i_plus_1_quad_{i}")))?;
      cs.enforce(
        || format!("x_i_plus_1_quad * x_i_plus_1 = x_i + y_i_iter_{i}"),
        |lc| lc + x_i_plus_1_quad.get_variable(),
        |lc| lc + x_i_plus_1.get_variable(),
        |lc| lc + x_i.get_variable() + y_i.get_variable(),
      );

      if i == self.seq.len() - 1 {
        z_out = Ok(vec![x_i_plus_1.clone(), x_i.clone()]);
      }

      // update x_i and y_i for the next iteration
      y_i = x_i;
      x_i = x_i_plus_1;
    }

    z_out
  }
}

/// cargo run --release --example minroot
fn main() {
  let subscriber = Registry::default()
    .with(fmt::layer().pretty())
    .with(EnvFilter::from_default_env())
    .with(TeXRayLayer::new());
  tracing::subscriber::set_global_default(subscriber).unwrap();

  println!("Nova-based VDF with MinRoot delay function");
  println!("=========================================================");

  let num_steps = 10;
  for num_iters_per_step in [1024, 2048, 4096, 8192, 16384, 32768, 65536] {
    // number of iterations of MinRoot per Nova's recursive step
    let circuit_primary = MinRootCircuit {
      seq: vec![
        MinRootIteration {
          x_i: <E1 as Engine>::Scalar::zero(),
          y_i: <E1 as Engine>::Scalar::zero(),
          x_i_plus_1: <E1 as Engine>::Scalar::zero(),
          y_i_plus_1: <E1 as Engine>::Scalar::zero(),
        };
        num_iters_per_step
      ],
    };

    let circuit_secondary = TrivialCircuit::default();

    println!("Proving {num_iters_per_step} iterations of MinRoot per step");

    // produce public parameters
    let start = Instant::now();
    println!("Producing public parameters...");
    let pp = PublicParams::<
      E1,
      E2,
      MinRootCircuit<<E1 as Engine>::Scalar>,
      TrivialCircuit<<E2 as Engine>::Scalar>,
    >::setup(
      &circuit_primary,
      &circuit_secondary,
      &*default_ck_hint(),
      &*default_ck_hint(),
    );
    println!("PublicParams::setup, took {:?} ", start.elapsed());
    #[cfg(feature = "abomonate")]
    {
      use abomonation::encode;
      let mut file = std::fs::File::create(utils::FILEPATH).unwrap();
      unsafe {
        encode(&pp, &mut file).unwrap();
      }
      println!("Encoded!");
    }

    println!(
      "Number of constraints per step (primary circuit): {}",
      pp.num_constraints().0
    );
    println!(
      "Number of constraints per step (secondary circuit): {}",
      pp.num_constraints().1
    );

    println!(
      "Number of variables per step (primary circuit): {}",
      pp.num_variables().0
    );
    println!(
      "Number of variables per step (secondary circuit): {}",
      pp.num_variables().1
    );

    #[cfg(feature = "abomonate")]
    {
      use abomonation::decode;
      use std::io::Read;

      let file = std::fs::File::open(utils::FILEPATH).unwrap();
      let mut reader = std::io::BufReader::new(file);
      let mut bytes = Vec::new();
      reader.read_to_end(&mut bytes).unwrap();
      if let Some((result, remaining)) = unsafe {
        decode::<
          PublicParams<
            E1,
            E2,
            MinRootCircuit<<E1 as Engine>::Scalar>,
            TrivialCircuit<<E2 as Engine>::Scalar>,
          >,
        >(&mut bytes)
      } {
        assert!(*result == pp, "decoded parameters not equal to original!");
        assert!(remaining.is_empty());
      } else {
        println!("Decoding failure!");
      }
    }

    // produce non-deterministic advice
    let (z0_primary, minroot_iterations) = MinRootIteration::new(
      num_iters_per_step * num_steps,
      &<E1 as Engine>::Scalar::zero(),
      &<E1 as Engine>::Scalar::one(),
    );
    let minroot_circuits = (0..num_steps)
      .map(|i| MinRootCircuit {
        seq: (0..num_iters_per_step)
          .map(|j| MinRootIteration {
            x_i: minroot_iterations[i * num_iters_per_step + j].x_i,
            y_i: minroot_iterations[i * num_iters_per_step + j].y_i,
            x_i_plus_1: minroot_iterations[i * num_iters_per_step + j].x_i_plus_1,
            y_i_plus_1: minroot_iterations[i * num_iters_per_step + j].y_i_plus_1,
          })
          .collect::<Vec<_>>(),
      })
      .collect::<Vec<_>>();

    let z0_secondary = vec![<E2 as Engine>::Scalar::zero()];

    type C1 = MinRootCircuit<<E1 as Engine>::Scalar>;
    type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;
    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> =
      RecursiveSNARK::<E1, E2, C1, C2>::new(
        &pp,
        &minroot_circuits[0],
        &circuit_secondary,
        &z0_primary,
        &z0_secondary,
      )
      .unwrap();

    for (i, circuit_primary) in minroot_circuits.iter().enumerate() {
      let start = Instant::now();
      let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
      assert!(res.is_ok());
      println!(
        "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
        i,
        res.is_ok(),
        start.elapsed()
      );
    }

    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
    println!(
      "RecursiveSNARK::verify: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());

    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
    let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

    let start = Instant::now();
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
    type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

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
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&vk, num_steps, &z0_primary, &z0_secondary);
    println!(
      "CompressedSNARK::verify: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
  }
}
