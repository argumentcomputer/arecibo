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

#[cfg(test)]
pub mod test_utils {
  //! Contains utilities for testing and benchmarking.
  use crate::spartan::polys::multilinear::MultilinearPolynomial;
  use crate::traits::{
    commitment::CommitmentEngineTrait, evaluation::EvaluationEngineTrait, Engine,
  };

  /// Generates a random polynomial and point from a seed to test a proving/verifying flow of one
  /// of our EvaluationEngine over a given Engine.
  pub(crate) fn prove_verify_from_ell<E: Engine, EE: EvaluationEngineTrait<E>>(ell: usize) {
    use rand_core::SeedableRng;

    let mut rng = rand::rngs::StdRng::seed_from_u64(ell as u64);

    let (poly, point, eval) = MultilinearPolynomial::random_with_eval(ell, &mut rng);

    // Mock commitment key.
    let ck = E::CE::setup(b"test", 1 << ell);
    // Commits to the provided vector using the provided generators.
    let commitment = E::CE::commit(&ck, poly.evaluations());

    prove_verify_with::<E, EE>(&ck, &commitment, &poly, &point, &eval, true)
  }

  pub(crate) fn prove_verify_with<E: Engine, EE: EvaluationEngineTrait<E>>(
    ck: &<<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey,
    commitment: &<<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
    poly: &MultilinearPolynomial<<E as Engine>::Scalar>,
    point: &[<E as Engine>::Scalar],
    eval: &<E as Engine>::Scalar,
    evaluate_bad_proof: bool,
  ) {
    use crate::traits::TranscriptEngineTrait;
    use ff::Field;
    use std::ops::Add;

    // Generate Prover and verifier key for given commitment key.
    let (prover_key, verifier_key) = EE::setup(ck);

    // Generate proof.
    let mut prover_transcript = E::TE::new(b"TestEval");
    let proof = EE::prove(
      ck,
      &prover_key,
      &mut prover_transcript,
      commitment,
      poly.evaluations(),
      point,
      eval,
    )
    .unwrap();
    let pcp = prover_transcript.squeeze(b"c").unwrap();

    // Verify proof.
    let mut verifier_transcript = E::TE::new(b"TestEval");
    EE::verify(
      &verifier_key,
      &mut verifier_transcript,
      commitment,
      point,
      eval,
      &proof,
    )
    .unwrap();
    let pcv = verifier_transcript.squeeze(b"c").unwrap();

    // Check if the prover transcript and verifier transcript are kept in the same state.
    assert_eq!(pcp, pcv);

    if evaluate_bad_proof {
      // Generate another point to verify proof. Also produce eval.
      let altered_verifier_point = point
        .iter()
        .map(|s| s.add(<E as Engine>::Scalar::ONE))
        .collect::<Vec<_>>();
      let altered_verifier_eval =
        MultilinearPolynomial::evaluate_with(poly.evaluations(), &altered_verifier_point);

      // Verify proof, should fail.
      let mut verifier_transcript = E::TE::new(b"TestEval");
      assert!(EE::verify(
        &verifier_key,
        &mut verifier_transcript,
        commitment,
        &altered_verifier_point,
        &altered_verifier_eval,
        &proof,
      )
      .is_err());
    }
  }
}
