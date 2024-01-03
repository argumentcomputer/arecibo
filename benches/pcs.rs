use arecibo::provider::{
  ipa_pc::EvaluationEngine as IPAEvaluationEngine, mlkzg::EvaluationEngine as MLEvaluationEngine,
  non_hiding_zeromorph::ZMPCS, Bn256EngineKZG, Bn256EngineZM, GrumpkinEngine,
};
use arecibo::spartan::polys::multilinear::MultilinearPolynomial;
use arecibo::traits::{
  commitment::CommitmentEngineTrait, evaluation::EvaluationEngineTrait, Engine,
  TranscriptEngineTrait,
};
use criterion::measurement::WallTime;
use criterion::{
  black_box, criterion_group, criterion_main, Bencher, BenchmarkGroup, BenchmarkId, Criterion,
  SamplingMode, Throughput,
};
use halo2curves::bn256::Bn256;
use rand::rngs::StdRng;
use rand_core::{CryptoRng, RngCore, SeedableRng};
use std::time::Duration;

// To run these benchmarks, first download `criterion` with `cargo install cargo-criterion`.
// Then `cargo criterion --bench pcs`.
// For flamegraphs, run `cargo criterion --bench pcs --features flamegraph -- --profile-time <secs>`.
// The results are located in `target/criterion/profile/<name-of-benchmark>`.
cfg_if::cfg_if! {
  if #[cfg(feature = "flamegraph")] {
    criterion_group! {
          name = pcs;
          config = Criterion::default().warm_up_time(Duration::from_millis(3000)).with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
          targets = bench_pcs
    }
  } else {
    criterion_group! {
          name = pcs;
          config = Criterion::default().warm_up_time(Duration::from_millis(3000));
          targets = bench_pcs
    }
  }
}

criterion_main!(pcs);

const TEST_ELL: [usize; 2] = [10, 11];

struct BenchAssests<E: Engine, EE: EvaluationEngineTrait<E>> {
  poly: MultilinearPolynomial<<E as Engine>::Scalar>,
  point: Vec<<E as Engine>::Scalar>,
  eval: <E as Engine>::Scalar,
  ck: <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey,
  commitment: <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
  prover_key: <EE as EvaluationEngineTrait<E>>::ProverKey,
  verifier_key: <EE as EvaluationEngineTrait<E>>::VerifierKey,
  proof: Option<<EE as EvaluationEngineTrait<E>>::EvaluationArgument>,
}

// Macro to generate benchmark code for multiple engine and evaluation engine types
macro_rules! benchmark_engines {
    ($ell:expr, $rng:expr, $group:expr, $internal_fn:expr, $( ($engine:ty, $eval_engine:ty, $engine_name:expr) ),*) => {
        $(
            let mut assets = deterministic_assets::<$engine, $eval_engine, StdRng>($ell, &mut $rng);
            $group.bench_with_input(BenchmarkId::new($engine_name, $ell), &$ell, |b, _| {
                $internal_fn(b, &mut assets);
            });
        )*
    };
}

fn bench_pcs(c: &mut Criterion) {
  for &ell in TEST_ELL.iter() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(ell as u64);

    // Proving group
    {
      let mut proving_group = c.benchmark_group(format!("PCS-Proving"));
      proving_group
        .sampling_mode(SamplingMode::Flat)
        .sample_size(10);

      benchmark_engines!(
          ell,
          rng,
          proving_group,
          bench_pcs_proving_internal,
          (GrumpkinEngine, IPAEvaluationEngine<GrumpkinEngine>, "IPA"),
          (Bn256EngineKZG, MLEvaluationEngine<Bn256, Bn256EngineKZG>, "MLKZG"),
          (Bn256EngineZM, ZMPCS<Bn256, Bn256EngineZM>, "ZM")
      );

      proving_group.finish();
    }

    // Verifying group
    {
      let mut verifying_group = c.benchmark_group(format!("PCS-Verifying"));
      verifying_group
        .sampling_mode(SamplingMode::Flat)
        .sample_size(10);

      benchmark_engines!(
          ell,
          rng,
          verifying_group,
          bench_pcs_verifying_internal,
          (GrumpkinEngine, IPAEvaluationEngine<GrumpkinEngine>, "IPA"),
          (Bn256EngineKZG, MLEvaluationEngine<Bn256, Bn256EngineKZG>, "MLKZG"),
          (Bn256EngineZM, ZMPCS<Bn256, Bn256EngineZM>, "ZM")
      );

      verifying_group.finish();
    }
  }
}

fn deterministic_assets<E: Engine, EE: EvaluationEngineTrait<E>, R: CryptoRng + RngCore>(
  ell: usize,
  mut rng: &mut R,
) -> BenchAssests<E, EE> {
  let (poly, point, eval) = MultilinearPolynomial::random_with_eval(ell, &mut rng);

  // Mock commitment key.
  let ck = E::CE::setup(b"test", 1 << ell);
  // Commits to the provided vector using the provided generators.
  let commitment = E::CE::commit(&ck, poly.evaluations());

  let (prover_key, verifier_key) = EE::setup(&ck);

  // Generate proof so that we can bench verification.
  let proof = EE::prove(
    &ck,
    &prover_key,
    &mut E::TE::new(b"TestEval"),
    &commitment,
    poly.evaluations(),
    &point,
    &eval,
  )
  .unwrap();

  BenchAssests {
    poly,
    point,
    eval,
    ck,
    commitment,
    prover_key,
    verifier_key,
    proof: Some(proof),
  }
}

fn bench_pcs_proving_internal<E: Engine, EE: EvaluationEngineTrait<E>>(
  b: &mut Bencher,
  mut bench_assets: &mut BenchAssests<E, EE>,
) {
  // Bench generate proof.
  b.iter(|| {
    EE::prove(
      &bench_assets.ck,
      &bench_assets.prover_key,
      &mut E::TE::new(b"TestEval"),
      &bench_assets.commitment,
      bench_assets.poly.evaluations(),
      &bench_assets.point,
      &bench_assets.eval,
    )
    .unwrap();
  });
}

fn bench_pcs_verifying_internal<E: Engine, EE: EvaluationEngineTrait<E>>(
  b: &mut Bencher,
  bench_assets: &BenchAssests<E, EE>,
) {
  // Bench verify proof.
  b.iter(|| {
    EE::verify(
      &bench_assets.verifier_key,
      &mut E::TE::new(b"TestEval"),
      &bench_assets.commitment,
      &bench_assets.point,
      &bench_assets.eval,
      bench_assets.proof.as_ref().unwrap(),
    )
    .unwrap();
  });
}
