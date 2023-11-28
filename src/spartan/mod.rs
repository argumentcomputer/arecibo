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
  /// Given [Pᵢ] and [sᵢ], compute P = ∑ᵢ sᵢ⋅Pᵢ
  ///
  /// # Details
  ///
  /// We allow the input polynomials to have different sizes, and interpret smaller ones as
  /// being padded with 0 to the maximum size of all polynomials.
  fn batch_diff_size(W: Vec<PolyEvalWitness<G>>, s: G::Scalar) -> PolyEvalWitness<G> {
    let powers = powers::<G>(&s, W.len());

    let size_max = W.iter().map(|w| w.p.len()).max().unwrap();
    // Scale the input polynomials by the power of s
    let p = W
      .into_par_iter()
      .zip(powers.par_iter())
      .map(|(mut w, s)| {
        if *s != G::Scalar::ONE {
          w.p.par_iter_mut().for_each(|e| *e *= s);
        }
        w.p
      })
      .reduce(
        || vec![G::Scalar::ZERO; size_max],
        |left, right| {
          // Sum into the largest polynomial
          let (mut big, small) = if left.len() > right.len() {
            (left, right)
          } else {
            (right, left)
          };

          big
            .par_iter_mut()
            .zip(small.par_iter())
            .for_each(|(b, s)| *b += s);

          big
        },
      );

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
  fn batch_diff_size(
    c_vec: &[Commitment<G>],
    e_vec: &[G::Scalar],
    num_vars: &[usize],
    x: Vec<G::Scalar>,
    s: G::Scalar,
  ) -> PolyEvalInstance<G> {
    let num_instances = num_vars.len();
    assert_eq!(c_vec.len(), num_instances);
    assert_eq!(e_vec.len(), num_instances);

    let num_vars_max = x.len();
    let powers: Vec<G::Scalar> = powers::<G>(&s, num_instances);
    // Rescale evaluations by the first Lagrange polynomial,
    // so that we can check its evaluation against x
    let evals_scaled = e_vec
      .iter()
      .zip(num_vars.iter())
      .map(|(eval, num_rounds)| {
        // x_lo = [ x[0]   , ..., x[n-nᵢ-1] ]
        // x_hi = [ x[n-nᵢ], ..., x[n]      ]
        let (r_lo, _r_hi) = x.split_at(num_vars_max - num_rounds);
        // Compute L₀(x_lo)
        let lagrange_eval = r_lo
          .iter()
          .map(|r| G::Scalar::ONE - r)
          .product::<G::Scalar>();

        // vᵢ = L₀(x_lo)⋅Pᵢ(x_hi)
        lagrange_eval * eval
      })
      .collect::<Vec<_>>();

    // C = ∑ᵢ γⁱ⋅Cᵢ
    let comm_joint = c_vec
      .iter()
      .zip(powers.iter())
      .map(|(c, g_i)| *c * *g_i)
      .fold(Commitment::<G>::default(), |acc, item| acc + item);

    // v = ∑ᵢ γⁱ⋅vᵢ
    let eval_joint = evals_scaled
      .into_iter()
      .zip(powers.iter())
      .map(|(e, g_i)| e * g_i)
      .sum();

    PolyEvalInstance {
      c: comm_joint,
      x,
      e: eval_joint,
    }
  }

  fn batch(
    c_vec: &[Commitment<G>],
    x: &[G::Scalar],
    e_vec: &[G::Scalar],
    s: &G::Scalar,
  ) -> PolyEvalInstance<G> {
    let num_instances = c_vec.len();
    assert_eq!(e_vec.len(), num_instances);

    let powers_of_s = powers::<G>(s, num_instances);
    // Weighted sum of evaluations
    let e = e_vec
      .par_iter()
      .zip(powers_of_s.par_iter())
      .map(|(e, p)| *e * p)
      .sum();
    // Weighted sum of commitments
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
