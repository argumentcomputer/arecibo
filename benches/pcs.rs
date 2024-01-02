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
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion, SamplingMode};
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

const TEST_ELL: [usize; 11] = [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
fn bench_pcs(c: &mut Criterion) {
  for ell in TEST_ELL.iter() {
    let mut group = c.benchmark_group(format!("PCS-PolynomialSize-{ell}"));
    group.sampling_mode(SamplingMode::Flat).sample_size(10);

    let mut rng = rand::rngs::StdRng::seed_from_u64(*ell as u64);

    bench_pcs_internal::<GrumpkinEngine, IPAEvaluationEngine<GrumpkinEngine>, StdRng>(
      &mut group,
      "IPA-Grumpkin",
      *ell,
      &mut rng,
    );

    bench_pcs_internal::<Bn256EngineKZG, MLEvaluationEngine<Bn256, Bn256EngineKZG>, StdRng>(
      &mut group, "MLKZG-Bn", *ell, &mut rng,
    );

    bench_pcs_internal::<Bn256EngineZM, ZMPCS<Bn256, Bn256EngineZM>, StdRng>(
      &mut group, "ZM-Bn", *ell, &mut rng,
    );

    group.finish();
  }
}

fn bench_pcs_internal<E: Engine, EE: EvaluationEngineTrait<E>, R: CryptoRng + RngCore>(
  group: &mut BenchmarkGroup<'_, WallTime>,
  id: &str,
  ell: usize,
  mut rng: &mut R,
) {
  let (poly, point, eval) = MultilinearPolynomial::random_with_eval(ell, &mut rng);

  // Mock commitment key.
  let ck = E::CE::setup(b"test", 1 << ell);
  // Commits to the provided vector using the provided generators.
  let commitment = E::CE::commit(&ck, poly.evaluations());

  let (prover_key, verifier_key) = EE::setup(&ck);

  // Bench generate proof.
  group.bench_function(format!("Prove-{}", id), |b| {
    b.iter(|| {
      EE::prove(
        &ck,
        &prover_key,
        &mut E::TE::new(b"TestEval"),
        &commitment,
        poly.evaluations(),
        &point,
        &eval,
      )
      .unwrap();
    })
  });

  // Generate proof so that we can bench verification.
  let mut prover_transcript = E::TE::new(b"TestEval");
  let proof = EE::prove(
    &ck,
    &prover_key,
    &mut prover_transcript,
    &commitment,
    poly.evaluations(),
    &point,
    &eval,
  )
  .unwrap();
  let pcp = prover_transcript.squeeze(b"c").unwrap();

  // Bench verify proof.
  group.bench_function(format!("Verify-{}", id), |b| {
    b.iter(|| {
      EE::verify(
        &verifier_key,
        &mut E::TE::new(b"TestEval"),
        &commitment,
        &point,
        &eval,
        &proof,
      )
      .unwrap();
    })
  });

  // Assert that verification goes well and that challenge passes.
  let mut verifier_transcript = E::TE::new(b"TestEval");
  EE::verify(
    &verifier_key,
    &mut verifier_transcript,
    &commitment,
    &point,
    &eval,
    &proof,
  )
  .unwrap();
  let pcv = verifier_transcript.squeeze(b"c").unwrap();

  // Check if the prover transcript and verifier transcript are kept in the same state.
  assert_eq!(pcp, pcv);
}
