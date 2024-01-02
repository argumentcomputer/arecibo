//! Utilities for provider module.
pub(in crate::provider) mod fb_msm;
pub mod msm {
  use halo2curves::msm::best_multiexp;
  use halo2curves::CurveAffine;

  // this argument swap is useful until Rust gets named arguments
  // and saves significant complexity in macro code
  pub fn cpu_best_msm<C: CurveAffine>(bases: &[C], scalars: &[C::Scalar]) -> C::Curve {
    best_multiexp(scalars, bases)
  }
}

#[cfg(any(test, feature = "bench"))]
pub mod test_utils {
  //! Contains utilities for testing and benchmarking.

  use crate::spartan::polys::multilinear::MultilinearPolynomial;
  use crate::traits::commitment::CommitmentEngineTrait;
  use crate::traits::evaluation::EvaluationEngineTrait;
  use crate::traits::Engine;
  #[cfg(test)]
  use crate::traits::TranscriptEngineTrait;
  use ff::Field;
  use rand_core::SeedableRng;
  /// Generates a random polynomial and point from a seed. Then, produces the evaluation of the point
  /// over the polynomial.
  pub fn gen_poly_point_eval<E: Engine>(
    seed: usize,
  ) -> (
    MultilinearPolynomial<<E as Engine>::Scalar>,
    Vec<<E as Engine>::Scalar>,
    <E as Engine>::Scalar,
  ) {
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed as u64);

    // Generate random polynomial and point.
    let poly = MultilinearPolynomial::random(seed, &mut rng);
    let point = (0..seed)
      .map(|_| E::Scalar::random(&mut rng))
      .collect::<Vec<_>>();

    // Calculation evaluation of point over polynomial.
    let eval = MultilinearPolynomial::evaluate_with(poly.evaluations(), &point);

    (poly, point, eval)
  }

  /// Commits to the provided vector using the provided generators, and generate Prover and verifier
  /// key for given commitment key.
  pub fn commitment_setup<E: Engine, EE: EvaluationEngineTrait<E>>(
    seed: usize,
    poly: &MultilinearPolynomial<<E as Engine>::Scalar>,
  ) -> (
    <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey,
    <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
    <EE as EvaluationEngineTrait<E>>::ProverKey,
    <EE as EvaluationEngineTrait<E>>::VerifierKey,
  ) {
    // Mock commitment key.
    let ck = E::CE::setup(b"test", 1 << seed);
    // Commits to the provided vector using the provided generators.
    let commitment = E::CE::commit(&ck, poly.evaluations());

    // Generate Prover and verifier key for given commitment key.
    let (prover_key, verifier_key) = EE::setup(&ck);

    (ck, commitment, prover_key, verifier_key)
  }

  /// Generates a random polynomial and point from a seed to test a proving/verifying flow of one
  /// of our EvaluationEngine over a given Engine.
  #[cfg(test)]
  pub(crate) fn test_from_seed<E: Engine, EE: EvaluationEngineTrait<E>>(seed: usize) {
    let (poly, point, eval) = gen_poly_point_eval::<E>(seed);

    let (ck, commitment, prover_key, verifier_key) = commitment_setup::<E, EE>(seed, &poly);

    // Generate proof.
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

  /// Test the flow where we have a bad proof generated and we try to verify it. We expect it to fail,
  /// as it should.
  #[cfg(test)]
  pub(crate) fn test_fail_bad_proof<E: Engine, EE: EvaluationEngineTrait<E>>(seed: usize) {
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed as u64);

    let (prover_poly, prover_point, prover_eval) = gen_poly_point_eval::<E>(seed);

    // Generate another point to verify proof. Also produce eval.
    let verifier_point = prover_point
      .iter()
      .map(|_| E::Scalar::random(&mut rng))
      .collect::<Vec<_>>();
    let verifier_eval =
      MultilinearPolynomial::evaluate_with(prover_poly.evaluations(), &prover_point);

    let (ck, commitment, prover_key, verifier_key) = commitment_setup::<E, EE>(seed, &prover_poly);

    // Generate proof.
    let mut prover_transcript = E::TE::new(b"TestEval");
    let proof = EE::prove(
      &ck,
      &prover_key,
      &mut prover_transcript,
      &commitment,
      prover_poly.evaluations(),
      &prover_point,
      &prover_eval,
    )
    .unwrap();

    // Verify proof, should fail.
    let mut verifier_transcript = E::TE::new(b"TestEval");
    assert!(EE::verify(
      &verifier_key,
      &mut verifier_transcript,
      &commitment,
      &verifier_point,
      &verifier_eval,
      &proof,
    )
    .is_err());
  }
}
