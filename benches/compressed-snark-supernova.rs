#![allow(non_snake_case)]

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use core::marker::PhantomData;
use criterion::*;
use ff::PrimeField;
use nova_snark::{
  supernova::NonUniformCircuit,
  supernova::{snark::CompressedSNARK, PublicParams, RecursiveSNARK},
  traits::{
    circuit_supernova::{StepCircuit, TrivialTestCircuit},
    snark::RelaxedR1CSSNARKTrait,
    snark::{default_ck_hint, BatchedRelaxedR1CSSNARKTrait},
    Engine,
  },
};
use std::time::Duration;

type E1 = nova_snark::provider::PallasEngine;
type E2 = nova_snark::provider::VestaEngine;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
// SNARKs without computational commitments
type S1 = nova_snark::spartan::batched::BatchedRelaxedR1CSSNARK<E1, EE1>;
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;
// SNARKs with computational commitments
type SS1 = nova_snark::spartan::batched_ppsnark::BatchedRelaxedR1CSSNARK<E1, EE1>;
type SS2 = nova_snark::spartan::ppsnark::RelaxedR1CSSNARK<E2, EE2>;

// To run these benchmarks, first download `criterion` with `cargo install cargo-criterion`.
// Then `cargo criterion --bench compressed-snark-supernova`. The results are located in `target/criterion/data/<name-of-benchmark>`.
// For flamegraphs, run `cargo criterion --bench compressed-snark-supernova --features flamegraph -- --profile-time <secs>`.
// The results are located in `target/criterion/profile/<name-of-benchmark>`.
cfg_if::cfg_if! {
  if #[cfg(feature = "flamegraph")] {
    criterion_group! {
      name = compressed_snark_suipernova;
      config = Criterion::default().warm_up_time(Duration::from_millis(3000)).with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
      targets = bench_one_augmented_circuit_compressed_snark, bench_two_augmented_circuit_compressed_snark, bench_two_augmented_circuit_compressed_snark_with_computational_commitments
    }
  } else {
    criterion_group! {
      name = compressed_snark_supernova;
      config = Criterion::default().warm_up_time(Duration::from_millis(3000));
      targets = bench_one_augmented_circuit_compressed_snark, bench_two_augmented_circuit_compressed_snark, bench_two_augmented_circuit_compressed_snark_with_computational_commitments
    }
  }
}

criterion_main!(compressed_snark_supernova);

struct NonUniformBench<E1, E2, S>
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
  NonUniformCircuit<E1, E2, NonTrivialTestCircuit<E1::Scalar>, TrivialTestCircuit<E2::Scalar>>
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
    assert!(circuit_index < self.num_circuits);

    NonTrivialTestCircuit::new(self.num_cons)
  }

  fn secondary_circuit(&self) -> TrivialTestCircuit<E2::Scalar> {
    Default::default()
  }
}

fn bench_one_augmented_circuit_compressed_snark(c: &mut Criterion) {
  let num_cons_verifier_circuit_primary = 9819;
  // we vary the number of constraints in the step circuit
  for &num_cons_in_augmented_circuit in
    [9819, 16384, 32768, 65536, 131072, 262144, 524288, 1048576].iter()
  {
    // number of constraints in the step circuit
    let num_cons = num_cons_in_augmented_circuit - num_cons_verifier_circuit_primary;

    let mut group = c.benchmark_group(format!(
      "CompressedSNARKSuperNova-1circuit-StepCircuitSize-{num_cons}"
    ));
    group.sample_size(10);

    let bench: NonUniformBench<E1, E2, TrivialTestCircuit<<E2 as Engine>::Scalar>> =
      NonUniformBench::new(1, num_cons);
    let pp = PublicParams::setup(&bench, &*default_ck_hint(), &*default_ck_hint());

    let num_steps = 3;
    let z0_primary = vec![<E1 as Engine>::Scalar::from(2u64)];
    let z0_secondary = vec![<E2 as Engine>::Scalar::from(2u64)];
    let mut recursive_snark_option: Option<RecursiveSNARK<E1, E2>> = None;

    for _ in 0..num_steps {
      let mut recursive_snark = recursive_snark_option.unwrap_or_else(|| {
        RecursiveSNARK::new(
          &pp,
          &bench,
          &bench.primary_circuit(0),
          &bench.secondary_circuit(),
          &z0_primary,
          &z0_secondary,
        )
        .unwrap()
      });

      let res =
        recursive_snark.prove_step(&pp, &bench.primary_circuit(0), &bench.secondary_circuit());
      if let Err(e) = &res {
        println!("res failed {:?}", e);
      }
      assert!(res.is_ok());
      let res = recursive_snark.verify(&pp, 0, &z0_primary, &z0_secondary);
      if let Err(e) = &res {
        println!("res failed {:?}", e);
      }
      assert!(res.is_ok());
      recursive_snark_option = Some(recursive_snark)
    }

    assert!(recursive_snark_option.is_some());
    let recursive_snark = recursive_snark_option.unwrap();

    let (prover_key, verifier_key) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

    // Benchmark the prove time
    group.bench_function("Prove", |b| {
      b.iter(|| {
        assert!(CompressedSNARK::<_, _, _, _, S1, S2>::prove(
          black_box(&pp),
          black_box(&prover_key),
          black_box(&recursive_snark)
        )
        .is_ok());
      })
    });

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &prover_key, &recursive_snark);

    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // Benchmark the verification time
    group.bench_function("Verify", |b| {
      b.iter(|| {
        assert!(black_box(compressed_snark.clone())
          .verify(
            black_box(&pp),
            black_box(&verifier_key),
            black_box(z0_primary.clone()),
            black_box(z0_secondary.clone()),
          )
          .is_ok());
      })
    });

    group.finish();
  }
}

fn bench_two_augmented_circuit_compressed_snark(c: &mut Criterion) {
  let num_cons_verifier_circuit_primary = 9819;
  // we vary the number of constraints in the step circuit
  for &num_cons_in_augmented_circuit in
    [9819, 16384, 32768, 65536, 131072, 262144, 524288, 1048576].iter()
  {
    // number of constraints in the step circuit
    let num_cons = num_cons_in_augmented_circuit - num_cons_verifier_circuit_primary;

    let mut group = c.benchmark_group(format!(
      "CompressedSNARKSuperNova-2circuit-StepCircuitSize-{num_cons}"
    ));
    group.sample_size(10);

    let bench: NonUniformBench<E1, E2, TrivialTestCircuit<<E2 as Engine>::Scalar>> =
      NonUniformBench::new(2, num_cons);
    let pp = PublicParams::setup(&bench, &*default_ck_hint(), &*default_ck_hint());

    let num_steps = 3;
    let z0_primary = vec![<E1 as Engine>::Scalar::from(2u64)];
    let z0_secondary = vec![<E2 as Engine>::Scalar::from(2u64)];
    let mut recursive_snark_option: Option<RecursiveSNARK<E1, E2>> = None;
    let mut selected_augmented_circuit = 0;

    for _ in 0..num_steps {
      let mut recursive_snark = recursive_snark_option.unwrap_or_else(|| {
        RecursiveSNARK::new(
          &pp,
          &bench,
          &bench.primary_circuit(0),
          &bench.secondary_circuit(),
          &z0_primary,
          &z0_secondary,
        )
        .unwrap()
      });

      if selected_augmented_circuit == 0 {
        let res =
          recursive_snark.prove_step(&pp, &bench.primary_circuit(0), &bench.secondary_circuit());
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
        let res = recursive_snark.verify(&pp, 0, &z0_primary, &z0_secondary);
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
      } else if selected_augmented_circuit == 1 {
        let res =
          recursive_snark.prove_step(&pp, &bench.primary_circuit(1), &bench.secondary_circuit());
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
        let res = recursive_snark.verify(&pp, 1, &z0_primary, &z0_secondary);
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
      } else {
        unimplemented!()
      }
      selected_augmented_circuit = (selected_augmented_circuit + 1) % 2;
      recursive_snark_option = Some(recursive_snark)
    }

    assert!(recursive_snark_option.is_some());
    let recursive_snark = recursive_snark_option.unwrap();

    let (prover_key, verifier_key) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

    // Benchmark the prove time
    group.bench_function("Prove", |b| {
      b.iter(|| {
        assert!(CompressedSNARK::<_, _, _, _, S1, S2>::prove(
          black_box(&pp),
          black_box(&prover_key),
          black_box(&recursive_snark)
        )
        .is_ok());
      })
    });

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &prover_key, &recursive_snark);

    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // Benchmark the verification time
    group.bench_function("Verify", |b| {
      b.iter(|| {
        assert!(black_box(compressed_snark.clone())
          .verify(
            black_box(&pp),
            black_box(&verifier_key),
            black_box(z0_primary.clone()),
            black_box(z0_secondary.clone()),
          )
          .is_ok());
      })
    });

    group.finish();
  }
}

fn bench_two_augmented_circuit_compressed_snark_with_computational_commitments(c: &mut Criterion) {
  let num_cons_verifier_circuit_primary = 9819;
  // we vary the number of constraints in the step circuit
  for &num_cons_in_augmented_circuit in
    [9819, 16384, 32768, 65536, 131072, 262144, 524288, 1048576].iter()
  {
    // number of constraints in the step circuit
    let num_cons = num_cons_in_augmented_circuit - num_cons_verifier_circuit_primary;

    let mut group = c.benchmark_group(format!(
      "pp-CompressedSNARKSuperNova-2circuit-StepCircuitSize-{num_cons}"
    ));
    group.sample_size(10);

    let bench: NonUniformBench<E1, E2, TrivialTestCircuit<<E2 as Engine>::Scalar>> =
      NonUniformBench::new(2, num_cons);
    let pp = PublicParams::setup(&bench, &*SS1::ck_floor(), &*SS2::ck_floor());

    let num_steps = 3;
    let z0_primary = vec![<E1 as Engine>::Scalar::from(2u64)];
    let z0_secondary = vec![<E2 as Engine>::Scalar::from(2u64)];
    let mut recursive_snark_option: Option<RecursiveSNARK<E1, E2>> = None;
    let mut selected_augmented_circuit = 0;

    for _ in 0..num_steps {
      let mut recursive_snark = recursive_snark_option.unwrap_or_else(|| {
        RecursiveSNARK::new(
          &pp,
          &bench,
          &bench.primary_circuit(0),
          &bench.secondary_circuit(),
          &z0_primary,
          &z0_secondary,
        )
        .unwrap()
      });

      if selected_augmented_circuit == 0 {
        let res =
          recursive_snark.prove_step(&pp, &bench.primary_circuit(0), &bench.secondary_circuit());
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
        let res = recursive_snark.verify(&pp, 0, &z0_primary, &z0_secondary);
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
      } else if selected_augmented_circuit == 1 {
        let res =
          recursive_snark.prove_step(&pp, &bench.primary_circuit(1), &bench.secondary_circuit());
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
        let res = recursive_snark.verify(&pp, 1, &z0_primary, &z0_secondary);
        if let Err(e) = &res {
          println!("res failed {:?}", e);
        }
        assert!(res.is_ok());
      } else {
        unimplemented!()
      }
      selected_augmented_circuit = (selected_augmented_circuit + 1) % 2;
      recursive_snark_option = Some(recursive_snark)
    }

    assert!(recursive_snark_option.is_some());
    let recursive_snark = recursive_snark_option.unwrap();

    let (prover_key, verifier_key) = CompressedSNARK::<_, _, _, _, SS1, SS2>::setup(&pp).unwrap();

    // Benchmark the prove time
    group.bench_function("Prove", |b| {
      b.iter(|| {
        assert!(CompressedSNARK::<_, _, _, _, SS1, SS2>::prove(
          black_box(&pp),
          black_box(&prover_key),
          black_box(&recursive_snark)
        )
        .is_ok());
      })
    });

    let res = CompressedSNARK::<_, _, _, _, SS1, SS2>::prove(&pp, &prover_key, &recursive_snark);

    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // Benchmark the verification time
    group.bench_function("Verify", |b| {
      b.iter(|| {
        assert!(black_box(compressed_snark.clone())
          .verify(
            black_box(&pp),
            black_box(&verifier_key),
            black_box(z0_primary.clone()),
            black_box(z0_secondary.clone()),
          )
          .is_ok());
      })
    });

    group.finish();
  }
}
#[derive(Clone, Debug, Default)]
struct NonTrivialTestCircuit<F: PrimeField> {
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
