//! This module implements `RelaxedR1CSSNARKTrait` using Spartan that is generic
//! over the polynomial commitment and evaluation argument (i.e., a PCS)
//! We provide two implementations, one in snark.rs (which does not use any preprocessing)
//! and another in ppsnark.rs (which uses preprocessing to keep the verifier's state small if the PCS provides a succinct verifier)
//! We also provide direct.rs that allows proving a step circuit directly with either of the two SNARKs.
//!
//! In polynomial.rs we also provide foundational types and functions for manipulating multilinear polynomials.
pub mod batched;
pub mod direct;
pub(crate) mod math;
pub mod polys;
pub mod ppsnark;
pub mod snark;
mod sumcheck;

use crate::{
  r1cs::{R1CSShape, SparseMatrix},
  traits::Group,
  Commitment,
};
use ff::Field;
use polys::multilinear::SparsePolynomial;
use rayon::{iter::IntoParallelRefIterator, prelude::*};

fn powers<G: Group>(s: &G::Scalar, n: usize) -> Vec<G::Scalar> {
  assert!(n >= 1);
  let mut powers = Vec::new();
  powers.push(G::Scalar::ONE);
  for i in 1..n {
    powers.push(powers[i - 1] * s);
  }
  powers
}

/// A type that holds a witness to a polynomial evaluation instance
pub struct PolyEvalWitness<G: Group> {
  p: Vec<G::Scalar>, // polynomial
}

impl<G: Group> PolyEvalWitness<G> {
  fn pad(W: &[PolyEvalWitness<G>]) -> Vec<PolyEvalWitness<G>> {
    // determine the maximum size
    if let Some(n) = W.iter().map(|w| w.p.len()).max() {
      W.iter()
        .map(|w| {
          let mut p = vec![G::Scalar::ZERO; n];
          p[..w.p.len()].copy_from_slice(&w.p);
          PolyEvalWitness { p }
        })
        .collect()
    } else {
      Vec::new()
    }
  }

  fn weighted_sum(W: &[PolyEvalWitness<G>], s: &[G::Scalar]) -> PolyEvalWitness<G> {
    assert_eq!(W.len(), s.len());
    let mut p = vec![G::Scalar::ZERO; W[0].p.len()];
    for i in 0..W.len() {
      for j in 0..W[i].p.len() {
        p[j] += W[i].p[j] * s[i]
      }
    }
    PolyEvalWitness { p }
  }

  // This method panics unless all vectors in p_vec are of the same length
  fn batch(p_vec: &[&Vec<G::Scalar>], s: &G::Scalar) -> PolyEvalWitness<G> {
    p_vec
      .iter()
      .for_each(|p| assert_eq!(p.len(), p_vec[0].len()));

    let powers_of_s = powers::<G>(s, p_vec.len());

    let p = p_vec
      .par_iter()
      .zip(powers_of_s.par_iter())
      .map(|(v, &weight)| {
        // compute the weighted sum for each vector
        v.iter().map(|&x| x * weight).collect::<Vec<G::Scalar>>()
      })
      .reduce(
        || vec![G::Scalar::ZERO; p_vec[0].len()],
        |acc, v| {
          // perform vector addition to combine the weighted vectors
          acc.into_iter().zip(v).map(|(x, y)| x + y).collect()
        },
      );

    PolyEvalWitness { p }
  }
}

/// A type that holds a polynomial evaluation instance
pub struct PolyEvalInstance<G: Group> {
  c: Commitment<G>,  // commitment to the polynomial
  x: Vec<G::Scalar>, // evaluation point
  e: G::Scalar,      // claimed evaluation
}

impl<G: Group> PolyEvalInstance<G> {
  fn pad(U: &[PolyEvalInstance<G>]) -> Vec<PolyEvalInstance<G>> {
    // determine the maximum size
    if let Some(ell) = U.iter().map(|u| u.x.len()).max() {
      U.iter()
        .map(|u| {
          let mut x = vec![G::Scalar::ZERO; ell - u.x.len()];
          x.extend(u.x.clone());
          PolyEvalInstance { c: u.c, x, e: u.e }
        })
        .collect()
    } else {
      Vec::new()
    }
  }

  fn batch(
    c_vec: &[Commitment<G>],
    x: &[G::Scalar],
    e_vec: &[G::Scalar],
    s: &G::Scalar,
  ) -> PolyEvalInstance<G> {
    let powers_of_s = powers::<G>(s, c_vec.len());
    let e = e_vec
      .par_iter()
      .zip(powers_of_s.par_iter())
      .map(|(e, p)| *e * p)
      .sum();
    let c = c_vec
      .par_iter()
      .zip(powers_of_s.par_iter())
      .map(|(c, p)| *c * *p)
      .reduce(Commitment::<G>::default, |acc, item| acc + item);

    PolyEvalInstance {
      c,
      x: x.to_vec(),
      e,
    }
  }
}

/// Bounds "row" variables of (A, B, C) matrices viewed as 2d multilinear polynomials
pub fn compute_eval_table_sparse<G: Group>(
  S: &R1CSShape<G>,
  rx: &[G::Scalar],
) -> (Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>) {
  assert_eq!(rx.len(), S.num_cons);

  let inner = |M: &SparseMatrix<G::Scalar>, M_evals: &mut Vec<G::Scalar>| {
    for (row_idx, ptrs) in M.indptr.windows(2).enumerate() {
      for (val, col_idx) in M.get_row_unchecked(ptrs.try_into().unwrap()) {
        M_evals[*col_idx] += rx[row_idx] * val;
      }
    }
  };

  let (A_evals, (B_evals, C_evals)) = rayon::join(
    || {
      let mut A_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * S.num_vars];
      inner(&S.A, &mut A_evals);
      A_evals
    },
    || {
      rayon::join(
        || {
          let mut B_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * S.num_vars];
          inner(&S.B, &mut B_evals);
          B_evals
        },
        || {
          let mut C_evals: Vec<G::Scalar> = vec![G::Scalar::ZERO; 2 * S.num_vars];
          inner(&S.C, &mut C_evals);
          C_evals
        },
      )
    },
  );

  (A_evals, B_evals, C_evals)
}
