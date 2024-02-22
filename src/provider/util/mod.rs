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

pub mod iterators {
  use ff::Field;
  use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
  use rayon_scan::ScanParallelIterator;
  use std::iter::DoubleEndedIterator;
  use std::{
    borrow::Borrow,
    ops::{AddAssign, MulAssign},
  };

  pub trait DoubleEndedIteratorExt: DoubleEndedIterator {
    /// This function employs Horner's scheme and core traits to create a combination of an iterator input with the powers
    /// of a provided coefficient.
    fn rlc<T, F>(&mut self, coefficient: &F) -> T
    where
      T: Clone + for<'a> MulAssign<&'a F> + for<'r> AddAssign<&'r T>,
      Self::Item: Borrow<T>,
    {
      let mut iter = self.rev();
      let Some(fst) = iter.next() else {
        panic!("input iterator should not be empty")
      };

      iter.fold(fst.borrow().clone(), |mut acc, item| {
        acc *= coefficient;
        acc += item.borrow();
        acc
      })
    }
  }

  impl<I: DoubleEndedIterator> DoubleEndedIteratorExt for I {}

  pub trait IndexedParallelIteratorExt: IndexedParallelIterator {
    /// This function core traits to create a combination of an iterator input with the powers
    /// of a provided coefficient.
    fn rlc<T, F>(self, coefficient: &F) -> T
    where
      F: Field,
      Self::Item: Borrow<T>,
      T: Clone + for<'a> MulAssign<&'a F> + for<'r> AddAssign<&'r T> + Send + Sync,
    {
      debug_assert!(self.len() > 0);
      // generate an iterator of powers of the right length
      let v = {
        let mut v = vec![*coefficient; self.len()];
        v[0] = F::ONE;
        v
      };
      // the collect is due to Scan being unindexed
      let powers: Vec<_> = v.into_par_iter().scan(|a, b| *a * *b, F::ONE).collect();

      self
        .zip_eq(powers.into_par_iter())
        .map(|(pt, val)| {
          let mut pt = pt.borrow().clone();
          pt *= &val;
          pt
        })
        .reduce_with(|mut a, b| {
          a += &b;
          a
        })
        .unwrap()
    }
  }

  impl<I: IndexedParallelIterator> IndexedParallelIteratorExt for I {}
}

#[cfg(test)]
pub mod test_utils {
  //! Contains utilities for testing and benchmarking.
  use crate::spartan::polys::multilinear::MultilinearPolynomial;
  use crate::traits::{
    commitment::CommitmentEngineTrait, evaluation::EvaluationEngineTrait, Engine,
  };
  use ff::Field;
  use rand::rngs::StdRng;
  use rand_core::{CryptoRng, RngCore};
  use std::sync::Arc;

  /// Returns a random polynomial, a point and calculate its evaluation.
  pub(crate) fn random_poly_with_eval<E: Engine, R: RngCore + CryptoRng>(
    num_vars: usize,
    mut rng: &mut R,
  ) -> (
    MultilinearPolynomial<<E as Engine>::Scalar>,
    Vec<<E as Engine>::Scalar>,
    <E as Engine>::Scalar,
  ) {
    // Generate random polynomial and point.
    let poly = MultilinearPolynomial::random(num_vars, &mut rng);
    let point = (0..num_vars)
      .map(|_| <E as Engine>::Scalar::random(&mut rng))
      .collect::<Vec<_>>();

    // Calculation evaluation of point over polynomial.
    let eval = poly.evaluate(&point);

    (poly, point, eval)
  }

  /// Methods used to test the prove and verify flow of [`MultilinearPolynomial`] Commitment Schemes
  /// (PCS).
  ///
  /// Generates a random polynomial and point from a seed to test a proving/verifying flow of one
  /// of our [`EvaluationEngine`].
  pub(crate) fn prove_verify_from_num_vars<E: Engine, EE: EvaluationEngineTrait<E>>(
    num_vars: usize,
  ) {
    use rand_core::SeedableRng;

    let mut rng = rand::rngs::StdRng::seed_from_u64(num_vars as u64);

    let (poly, point, eval) = random_poly_with_eval::<E, StdRng>(num_vars, &mut rng);

    // Mock commitment key.
    let ck = E::CE::setup(b"test", 1 << num_vars);
    let ck = Arc::new(ck);
    // Commits to the provided vector using the provided generators.
    let commitment = E::CE::commit(&ck, poly.evaluations());

    prove_verify_with::<E, EE>(ck, &commitment, &poly, &point, &eval, true)
  }

  fn prove_verify_with<E: Engine, EE: EvaluationEngineTrait<E>>(
    ck: Arc<<<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey>,
    commitment: &<<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
    poly: &MultilinearPolynomial<<E as Engine>::Scalar>,
    point: &[<E as Engine>::Scalar],
    eval: &<E as Engine>::Scalar,
    evaluate_bad_proof: bool,
  ) {
    use crate::traits::TranscriptEngineTrait;
    use std::ops::Add;

    // Generate Prover and verifier key for given commitment key.
    let ock = ck.clone();
    let (prover_key, verifier_key) = EE::setup(ck);

    // Generate proof.
    let mut prover_transcript = E::TE::new(b"TestEval");
    let proof = EE::prove(
      &*ock,
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

#[cfg(test)]
pub mod solidity_compatibility_utils {
  use crate::provider::traits::DlogGroup;
  use crate::spartan::polys::multilinear::MultilinearPolynomial;
  use crate::traits::{
    commitment::CommitmentEngineTrait, evaluation::EvaluationEngineTrait, Engine,
  };
  use group::prime::PrimeCurve;
  use group::prime::PrimeCurveAffine;
  use rand::rngs::StdRng;
  use serde_json::{Map, Value};
  use std::sync::Arc;

  pub(crate) fn generate_pcs_solidity_unit_test_data<E: Engine, EE: EvaluationEngineTrait<E>>(
    num_vars: usize,
  ) -> (
    <E::CE as CommitmentEngineTrait<E>>::Commitment,
    Vec<E::Scalar>,
    E::Scalar,
    EE::EvaluationArgument,
    EE::VerifierKey,
  ) {
    use rand_core::SeedableRng;

    let mut rng = rand::rngs::StdRng::seed_from_u64(num_vars as u64);

    let (poly, point, eval) =
      crate::provider::util::test_utils::random_poly_with_eval::<E, StdRng>(num_vars, &mut rng);

    // Mock commitment key.
    let ck = E::CE::setup(b"test", 1 << num_vars);
    let ck_arc = Arc::new(ck.clone());
    // Commits to the provided vector using the provided generators.
    let commitment = E::CE::commit(&ck_arc, poly.evaluations());

    let (proof, vk) = prove_verify_solidity::<E, EE>(ck_arc, &commitment, &poly, &point, &eval);

    (commitment, point, eval, proof, vk)
  }

  fn prove_verify_solidity<E: Engine, EE: EvaluationEngineTrait<E>>(
    ck: Arc<<<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey>,
    commitment: &<<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment,
    poly: &MultilinearPolynomial<<E as Engine>::Scalar>,
    point: &[<E as Engine>::Scalar],
    eval: &<E as Engine>::Scalar,
  ) -> (EE::EvaluationArgument, EE::VerifierKey) {
    use crate::traits::TranscriptEngineTrait;

    // Generate Prover and verifier key for given commitment key.
    let ock = ck.clone();
    let (prover_key, verifier_key) = EE::setup(ck);

    // Generate proof.
    let mut prover_transcript = E::TE::new(b"TestEval");
    let proof: EE::EvaluationArgument = EE::prove(
      &*ock,
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

    (proof, verifier_key)
  }

  pub(crate) fn field_elements_to_json<E: Engine>(field_elements: &[E::Scalar]) -> Vec<Value> {
    let mut value_vector = vec![];
    field_elements.iter().enumerate().for_each(|(i, fe)| {
      let mut value = Map::new();
      value.insert("i".to_string(), Value::String(i.to_string()));
      value.insert("val".to_string(), Value::String(format!("{:?}", fe)));
      value_vector.push(Value::Object(value));
    });
    value_vector
  }

  pub(crate) fn ec_points_to_json<E>(ec_points: &[<E::GE as PrimeCurve>::Affine]) -> Vec<Value>
  where
    E: Engine,
    E::GE: DlogGroup<ScalarExt = E::Scalar>,
  {
    let mut value_vector = vec![];
    ec_points.iter().enumerate().for_each(|(i, ec_point)| {
      let mut value = Map::new();
      let coordinates_info = ec_point.to_curve().to_coordinates();
      let not_infinity = !coordinates_info.2;
      assert!(not_infinity);
      value.insert("i".to_string(), Value::String(i.to_string()));
      value.insert(
        "x".to_string(),
        Value::String(format!("{:?}", coordinates_info.0)),
      );
      value.insert(
        "y".to_string(),
        Value::String(format!("{:?}", coordinates_info.1)),
      );
      value_vector.push(Value::Object(value));
    });
    value_vector
  }
}
