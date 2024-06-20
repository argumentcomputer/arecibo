use ff::Field;
use rayon::prelude::*;

use crate::provider::util::field::batch_invert;
use crate::spartan::math::Math;
use crate::spartan::polys::{
  eq::EqPolynomial, masked_eq::MaskedEqPolynomial, multilinear::MultilinearPolynomial,
  power::PowPolynomial,
};
use crate::spartan::zksumcheck::ZKSumcheckProof;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::{Commitment, CommitmentKey, Engine, NovaError};
use crate::spartan::powers;
use crate::spartan::zksumcheck::Bn256EngineZKPedersen;
use itertools::Itertools;
use std::marker::PhantomData;

// Define a iterator over Natural number without allocated a whole size vector
// it started from 0 instead of 1
pub(in crate::spartan) struct NaturalNumVec<E: Engine> {
  curr: u64,
  size: u64,
  _phatom: PhantomData<E>,
}
impl<E: Engine> NaturalNumVec<E> {
  pub fn new(size: u64) -> Self {
    NaturalNumVec {
      curr: 0,
      size,
      _phatom: PhantomData,
    }
  }
}

impl<E: Engine> Iterator for NaturalNumVec<E> {
  // We can refer to this type using Self::Item
  type Item = E::Scalar;

  fn next(&mut self) -> Option<Self::Item> {
    let next = if self.curr < self.size {
      Some(E::Scalar::from(self.curr))
    } else {
      None
    };
    self.curr += 1;
    next
  }
}

impl<E: Engine> ExactSizeIterator for NaturalNumVec<E> {
  // We can easily calculate the remaining number of iterations.
  fn len(&self) -> usize {
    (self.size - self.curr).try_into().unwrap()
  }
}

/// Defines a trait for implementing sum-check in a generic manner
pub trait ZKSumcheckEngine: Send + Sync {
  /// returns the initial claims
  fn initial_claims(&self) -> Vec<<Bn256EngineZKPedersen as Engine>::Scalar>;

  /// degree of the sum-check polynomial
  fn degree(&self) -> usize;

  /// the size of the polynomials
  fn size(&self) -> usize;

  /// returns evaluation points at 0, 2, d-1 (where d is the degree of the sum-check polynomial)
  fn evaluation_points(&self) -> Vec<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>;

  /// bounds a variable in the constituent polynomials
  fn bound(&mut self, r: &<Bn256EngineZKPedersen as Engine>::Scalar);

  /// returns the final claims
  fn final_claims(&self) -> Vec<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>;
}

/// The [`WitnessBoundSumcheck`] ensures that the witness polynomial W defined over n = log(N) variables,
/// is zero outside of the first `num_vars = 2^m` entries.
///
/// # Details
///
/// The `W` polynomial is padded with zeros to size N = 2^n.
/// The `masked_eq` polynomials is defined as with regards to a random challenge `tau` as
/// the eq(tau) polynomial, where the first 2^m evaluations to 0.
///
/// The instance is given by
///  `0 = ∑_{0≤i<2^n} masked_eq[i] * W[i]`.
/// It is equivalent to the expression
///  `0 = ∑_{2^m≤i<2^n} eq[i] * W[i]`
/// Since `eq` is random, the instance is only satisfied if `W[2^{m}..] = 0`.
pub(in crate::spartan) struct WitnessBoundSumcheck<E: Engine> {
  poly_W: MultilinearPolynomial<E::Scalar>,
  poly_masked_eq: MultilinearPolynomial<E::Scalar>,
}

impl<E: Engine> WitnessBoundSumcheck<E> {
  pub fn new(tau: E::Scalar, poly_W_padded: Vec<E::Scalar>, num_vars: usize) -> Self {
    let num_vars_log = num_vars.log_2();
    // When num_vars = num_rounds, we shouldn't have to prove anything
    // but we still want this instance to compute the evaluation of W
    let num_rounds = poly_W_padded.len().log_2();
    assert!(num_vars_log < num_rounds);

    let tau_coords = PowPolynomial::new(&tau, num_rounds).coordinates();
    let poly_masked_eq_evals =
      MaskedEqPolynomial::new(&EqPolynomial::new(tau_coords), num_vars_log).evals();

    Self {
      poly_W: MultilinearPolynomial::new(poly_W_padded),
      poly_masked_eq: MultilinearPolynomial::new(poly_masked_eq_evals),
    }
  }
}
impl ZKSumcheckEngine for WitnessBoundSumcheck<Bn256EngineZKPedersen> {
  fn initial_claims(&self) -> Vec<<Bn256EngineZKPedersen as Engine>::Scalar> {
    vec![<Bn256EngineZKPedersen as Engine>::Scalar::ZERO]
  }

  fn degree(&self) -> usize {
    3
  }

  fn size(&self) -> usize {
    assert_eq!(self.poly_W.len(), self.poly_masked_eq.len());
    self.poly_W.len()
  }

  fn evaluation_points(&self) -> Vec<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>> {
    let comb_func = |poly_A_comp: &<Bn256EngineZKPedersen as Engine>::Scalar,
                     poly_B_comp: &<Bn256EngineZKPedersen as Engine>::Scalar,
                     _: &<Bn256EngineZKPedersen as Engine>::Scalar|
     -> <Bn256EngineZKPedersen as Engine>::Scalar { *poly_A_comp * *poly_B_comp };

    let (eval_point_0, eval_point_2, eval_point_3) = ZKSumcheckProof::compute_eval_points_cubic(
      &self.poly_masked_eq,
      &self.poly_W,
      &self.poly_W, // unused
      &comb_func,
    );

    vec![vec![eval_point_0, eval_point_2, eval_point_3]]
  }

  fn bound(&mut self, r: &<Bn256EngineZKPedersen as Engine>::Scalar) {
    [&mut self.poly_W, &mut self.poly_masked_eq]
      .par_iter_mut()
      .for_each(|poly| poly.bind_poly_var_top(r));
  }

  fn final_claims(&self) -> Vec<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>> {
    vec![vec![self.poly_W[0], self.poly_masked_eq[0]]]
  }
}
