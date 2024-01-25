//! # Sparse Matrices
//!
//! This module defines a custom implementation of CSR/CSC sparse matrices.
//! Specifically, we implement sparse matrix / dense vector multiplication
//! to compute the `A z`, `B z`, and `C z` in Nova.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use ff::PrimeField;
use itertools::Itertools as _;
use rand_core::{CryptoRng, RngCore};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// CSR format sparse matrix, We follow the names used by scipy.
/// Detailed explanation here: <https://stackoverflow.com/questions/52299420/scipy-csr-matrix-understand-indptr>
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
#[abomonation_bounds(where <F as PrimeField>::Repr: Abomonation)]
pub struct SparseMatrix<F: PrimeField> {
  #[abomonate_with(Vec<F::Repr>)]
  /// all non-zero values in the matrix
  pub data: Vec<F>,
  /// column indices
  pub indices: Vec<usize>,
  /// row information
  pub indptr: Vec<usize>,
  /// number of columns
  pub cols: usize,
}

/// [SparseMatrix]s are often large, and this helps with cloning bottlenecks
impl<F: PrimeField> Clone for SparseMatrix<F> {
  fn clone(&self) -> Self {
    Self {
      data: self.data.par_iter().cloned().collect(),
      indices: self.indices.par_iter().cloned().collect(),
      indptr: self.indptr.par_iter().cloned().collect(),
      cols: self.cols,
    }
  }
}

impl<F: PrimeField> SparseMatrix<F> {
  /// 0x0 empty matrix
  pub fn empty() -> Self {
    Self {
      data: vec![],
      indices: vec![],
      indptr: vec![0],
      cols: 0,
    }
  }

  /// Construct from the COO representation; Vec<usize(row), usize(col), F>.
  /// We assume that the rows are sorted during construction.
  pub fn new(matrix: &[(usize, usize, F)], rows: usize, cols: usize) -> Self {
    let mut new_matrix = vec![vec![]; rows];
    for (row, col, val) in matrix {
      new_matrix[*row].push((*col, *val));
    }

    for row in new_matrix.iter() {
      assert!(row.windows(2).all(|w| w[0].0 < w[1].0));
    }

    let mut indptr = vec![0; rows + 1];
    for (i, col) in new_matrix.iter().enumerate() {
      indptr[i + 1] = indptr[i] + col.len();
    }

    let mut indices = vec![];
    let mut data = vec![];
    for col in new_matrix {
      let (idx, val): (Vec<_>, Vec<_>) = col.into_iter().unzip();
      indices.extend(idx);
      data.extend(val);
    }

    Self {
      data,
      indices,
      indptr,
      cols,
    }
  }

  /// Samples a new random matrix of size `rows` x `cols` with `num_entries` non-zero entries.
  pub fn random<R: RngCore + CryptoRng>(
    rows: usize,
    cols: usize,
    num_entries: usize,
    mut rng: &mut R,
  ) -> Self {
    assert!(num_entries <= rows * cols);

    let mut indices = BTreeSet::<(usize, usize)>::new();
    while indices.len() < num_entries {
      let row = rng.next_u32() as usize % rows;
      let col = rng.next_u32() as usize % cols;
      indices.insert((row, col));
    }

    let matrix = indices
      .into_iter()
      .map(|(row, col)| (row, col, F::random(&mut rng)))
      .collect::<Vec<_>>();

    Self::new(&matrix, rows, cols)
  }

  /// Retrieves the data for row slice [i..j] from `ptrs`.
  /// We assume that `ptrs` is indexed from `indptrs` and do not check if the
  /// returned slice is actually a valid row.
  pub fn get_row_unchecked(&self, ptrs: &[usize; 2]) -> impl Iterator<Item = (&F, &usize)> {
    self.data[ptrs[0]..ptrs[1]]
      .iter()
      .zip_eq(&self.indices[ptrs[0]..ptrs[1]])
  }

  /// Multiply by a dense vector; uses rayon to parallelize.
  pub fn multiply_vec(&self, vector: &[F]) -> Vec<F> {
    assert_eq!(self.cols, vector.len(), "invalid shape");

    self.multiply_vec_unchecked(vector)
  }

  /// Multiply by a dense vector; uses rayon to parallelize.
  /// This does not check that the shape of the matrix/vector are compatible.
  #[tracing::instrument(
    skip_all,
    level = "trace",
    name = "SparseMatrix::multiply_vec_unchecked"
  )]
  pub fn multiply_vec_unchecked(&self, vector: &[F]) -> Vec<F> {
    self
      .indptr
      .par_windows(2)
      .map(|ptrs| {
        self
          .get_row_unchecked(ptrs.try_into().unwrap())
          .map(|(val, col_idx)| *val * vector[*col_idx])
          .sum()
      })
      .collect()
  }

  /// Multiply by a witness representing a dense vector; uses rayon to parallelize.
  pub fn multiply_witness(&self, W: &[F], u: &F, X: &[F]) -> Vec<F> {
    assert_eq!(self.cols, W.len() + X.len() + 1, "invalid shape");

    self.multiply_witness_unchecked(W, u, X)
  }

  /// Multiply by a witness representing a dense vector; uses rayon to parallelize.
  /// This does not check that the shape of the matrix/vector are compatible.
  #[tracing::instrument(
    skip_all,
    level = "trace",
    name = "SparseMatrix::multiply_vec_unchecked"
  )]
  pub fn multiply_witness_unchecked(&self, W: &[F], u: &F, X: &[F]) -> Vec<F> {
    // preallocate the result vector
    let mut sink = Vec::with_capacity(self.indptr.len() - 1);
    self.multiply_witness_into_unchecked(W, u, X, &mut sink);
    sink
  }

  /// Multiply by a witness representing a dense vector; uses rayon to parallelize.
  pub fn multiply_witness_into(&self, W: &[F], u: &F, X: &[F], sink: &mut Vec<F>) {
    assert_eq!(self.cols, W.len() + X.len() + 1, "invalid shape");

    self.multiply_witness_into_unchecked(W, u, X, sink);
  }

  /// Multiply by a witness representing a dense vector; uses rayon to parallelize.
  /// This does not check that the shape of the matrix/vector are compatible.
  pub fn multiply_witness_into_unchecked(&self, W: &[F], u: &F, X: &[F], sink: &mut Vec<F>) {
    let num_vars = W.len();
    self
      .indptr
      .par_windows(2)
      .map(|ptrs| {
        self
          .get_row_unchecked(ptrs.try_into().unwrap())
          .fold(F::ZERO, |acc, (val, col_idx)| {
            let val = match col_idx.cmp(&num_vars) {
              Ordering::Less => *val * W[*col_idx],
              Ordering::Equal => *val * *u,
              Ordering::Greater => *val * X[*col_idx - num_vars - 1],
            };
            acc + val
          })
      })
      .collect_into_vec(sink);
  }

  /// number of non-zero entries
  pub fn len(&self) -> usize {
    *self.indptr.last().unwrap()
  }

  /// empty matrix
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// returns a custom iterator
  pub fn iter(&self) -> Iter<'_, F> {
    let mut row = 0;
    while self.indptr[row + 1] == 0 {
      row += 1;
    }
    Iter {
      matrix: self,
      row,
      i: 0,
      nnz: *self.indptr.last().unwrap(),
    }
  }
}

/// Iterator for sparse matrix
#[derive(Debug)]
pub struct Iter<'a, F: PrimeField> {
  matrix: &'a SparseMatrix<F>,
  row: usize,
  i: usize,
  nnz: usize,
}

impl<'a, F: PrimeField> Iterator for Iter<'a, F> {
  type Item = (usize, usize, F);

  fn next(&mut self) -> Option<Self::Item> {
    // are we at the end?
    if self.i == self.nnz {
      return None;
    }

    // compute current item
    let curr_item = (
      self.row,
      self.matrix.indices[self.i],
      self.matrix.data[self.i],
    );

    // advance the iterator
    self.i += 1;
    // edge case at the end
    if self.i == self.nnz {
      return Some(curr_item);
    }
    // if `i` has moved to next row
    while self.i >= self.matrix.indptr[self.row + 1] {
      self.row += 1;
    }

    Some(curr_item)
  }
}

#[cfg(test)]
mod tests {
  use super::SparseMatrix;
  #[cfg(not(target_arch = "wasm32"))]
  use crate::r1cs::util::FWrap;
  use crate::{
    provider::PallasEngine,
    traits::{Engine, Group},
  };
  #[cfg(not(target_arch = "wasm32"))]
  use proptest::{
    prelude::*,
    strategy::{BoxedStrategy, Just, Strategy},
  };

  type G = <PallasEngine as Engine>::GE;
  type Fr = <G as Group>::Scalar;

  #[test]
  fn test_matrix_creation() {
    let matrix_data = vec![
      (0, 1, Fr::from(2)),
      (1, 2, Fr::from(3)),
      (2, 0, Fr::from(4)),
    ];
    let sparse_matrix = SparseMatrix::<Fr>::new(&matrix_data, 3, 3);

    assert_eq!(
      sparse_matrix.data,
      vec![Fr::from(2), Fr::from(3), Fr::from(4)]
    );
    assert_eq!(sparse_matrix.indices, vec![1, 2, 0]);
    assert_eq!(sparse_matrix.indptr, vec![0, 1, 2, 3]);
  }

  #[test]
  fn test_matrix_vector_multiplication() {
    let matrix_data = vec![
      (0, 1, Fr::from(2)),
      (0, 2, Fr::from(7)),
      (1, 2, Fr::from(3)),
      (2, 0, Fr::from(4)),
    ];
    let sparse_matrix = SparseMatrix::<Fr>::new(&matrix_data, 3, 3);
    let vector = vec![Fr::from(1), Fr::from(2), Fr::from(3)];

    let result = sparse_matrix.multiply_vec(&vector);

    assert_eq!(result, vec![Fr::from(25), Fr::from(9), Fr::from(4)]);
  }

  #[cfg(not(target_arch = "wasm32"))]
  fn coo_strategy() -> BoxedStrategy<Vec<(usize, usize, FWrap<Fr>)>> {
    let coo_strategy = any::<FWrap<Fr>>().prop_flat_map(|f| (0usize..100, 0usize..100, Just(f)));
    proptest::collection::vec(coo_strategy, 10).boxed()
  }

  #[cfg(not(target_arch = "wasm32"))]
  proptest! {
      #[test]
      fn test_matrix_iter(mut coo_matrix in coo_strategy()) {
        // process the randomly generated coo matrix
        coo_matrix.sort_by_key(|(row, col, _val)| (*row, *col));
        coo_matrix.dedup_by_key(|(row, col, _val)| (*row, *col));
        let coo_matrix = coo_matrix.into_iter().map(|(row, col, val)| { (row, col, val.0) }).collect::<Vec<_>>();

        let matrix = SparseMatrix::new(&coo_matrix, 100, 100);

        prop_assert_eq!(coo_matrix, matrix.iter().collect::<Vec<_>>());
    }
  }
}
