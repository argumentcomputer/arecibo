use arecibo::provider::ipa_pc::EvaluationEngine as IPAEvaluationEngine;
use arecibo::provider::mlkzg::EvaluationEngine as MLEvaluationEngine;
use arecibo::provider::non_hiding_zeromorph::ZMPCS;
use arecibo::provider::util::test_utils::{commitment_setup, gen_poly_point_eval};
use arecibo::provider::{Bn256EngineKZG, Bn256EngineZM, GrumpkinEngine};
use arecibo::traits::evaluation::EvaluationEngineTrait;
use arecibo::traits::{Engine, TranscriptEngineTrait};
use criterion::measurement::WallTime;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion, SamplingMode};
use halo2curves::bn256::Bn256;
use std::time::Duration;
// To run these benchmarks, first download `criterion` with `cargo install cargo-criterion`.
// Then `cargo criterion --bench pcs --features bench`. The results are located in `target/criterion/data/<name-of-benchmark>`.
criterion_group! {
      name = pcs;
      config = Criterion::default().warm_up_time(Duration::from_millis(3000));
      targets = bench_proving
}

criterion_main!(pcs);

const SEEDS: [usize; 3] = [4, 5, 6];
fn bench_proving(c: &mut Criterion) {
  for seed in SEEDS.iter() {
    let mut group = c.benchmark_group(format!("PCS-Seed-{seed}"));
    group.sampling_mode(SamplingMode::Flat);

    bench_proving_internal::<GrumpkinEngine, IPAEvaluationEngine<GrumpkinEngine>>(
      &mut group,
      "IPA-Grumpkin",
      *seed,
    );

    bench_proving_internal::<Bn256EngineKZG, MLEvaluationEngine<Bn256, Bn256EngineKZG>>(
      &mut group, "MLKZG-Bn", *seed,
    );

    bench_proving_internal::<Bn256EngineZM, ZMPCS<Bn256, Bn256EngineZM>>(
      &mut group, "ZM-Bn", *seed,
    );

    group.finish();
  }
}

fn bench_proving_internal<E: Engine, EE: EvaluationEngineTrait<E>>(
  group: &mut BenchmarkGroup<'_, WallTime>,
  id: &str,
  seed: usize,
) {
  let (poly, point, eval) = gen_poly_point_eval::<E>(seed);

  let (ck, commitment, prover_key, verifier_key) = commitment_setup::<E, EE>(seed, &poly);

  // Generate proof.
  group.bench_function(format!("Prove-{}", id), |b| {
    b.iter(|| {
      assert!(EE::prove(
        &ck,
        &prover_key,
        &mut E::TE::new(b"TestEval"),
        &commitment,
        poly.evaluations(),
        &point,
        &eval,
      )
      .is_ok());
    })
  });
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

  // Verify proof.
  group.bench_function(format!("Verify-{}", id), |b| {
    b.iter(|| {
      assert!(EE::prove(
        &ck,
        &prover_key,
        &mut E::TE::new(b"TestEval"),
        &commitment,
        poly.evaluations(),
        &point,
        &eval,
      )
      .is_ok());
    })
  });
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
