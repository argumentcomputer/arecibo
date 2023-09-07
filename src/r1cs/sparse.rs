//! # Sparse Matrices
//!
//! This module defines a custom implementation of CSR/CSC sparse matrices.
//! Specifically, we implement sparse matrix / dense vector multiplication
//! to compute the `A z`, `B z`, and `C z` in Nova.
//!
//! Notes:
//!
//! There are many sparse matrix crates available in rust. However, most of
//! these crates are do not parallelize, or are not compatiable with field elements.
//!
//! For example, [sprs](https://crates.io/crates/sprs/0.2.1) does not parallelize
//! its sparse matrix / dense vector multiplication. It's traits also require
//! `num_traits::Zero`, which is not compatiable with `ff::PrimeField`.

use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use ff::PrimeField;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// CSR format sparse matrix, We follow the names used by scipy.
/// Detailed explanation here: https://stackoverflow.com/questions/52299420/scipy-csr-matrix-understand-indptr
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
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

impl<F: PrimeField> SparseMatrix<F> {
  /// 0x0 empty matrix
  pub fn empty() -> Self {
    SparseMatrix {
      data: vec![],
      indices: vec![],
      indptr: vec![0],
      cols: 0,
    }
  }

  /// construct from Vec<usize(row), usize(col), F>
  pub fn new(matrix: &[(usize, usize, F)], rows: usize, cols: usize) -> Self {
    let mut new_matrix = vec![vec![]; rows];
    for (row, col, val) in matrix {
      new_matrix[*row].push((*col, *val));
    }

    for col in new_matrix.iter_mut() {
      col.sort_by(|(x, _), (y, _)| x.cmp(y));
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

    SparseMatrix {
      data,
      indices,
      indptr,
      cols,
    }
  }

  /// multiply by dense vector; should use rayon/gpu
  #[tracing::instrument(skip_all, name = "SparseMatrix::multiply_vec")]
  pub fn multiply_vec(&self, vector: &[F]) -> Vec<F> {
    assert_eq!(self.cols, vector.len(), "invalid shape");

    // naive implementation for now
    self
      .indptr
      .par_windows(2)
      .map(|ptrs| {
        let data = &self.data[ptrs[0]..ptrs[1]];
        let indices = &self.indices[ptrs[0]..ptrs[1]];
        data
          .iter()
          .zip(indices)
          .map(|(val, col_idx)| *val * vector[*col_idx])
          .sum()
      })
      .collect()
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

  /// pad to specific dimensions, which must be bigger
  pub fn pad(&mut self, rows: usize, num_vars_padded: usize, num_vars: usize) {
    assert!(rows + 1 >= self.indptr.len(), "row size must be bigger");

    self.indices.par_iter_mut().for_each(|c| {
      if *c >= num_vars {
        *c += num_vars_padded - num_vars
      }
    });

    self.cols += num_vars_padded - num_vars;

    let ex = {
      let nnz = self.indptr.last().unwrap();
      vec![*nnz; rows - self.indptr.len() + 1]
    };
    self.indptr.extend(ex);
  }
}

/// Iterator for sparse matrix
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

/// sorts a matrix by (row, col)
pub fn sort_sparse<F: PrimeField>(matrix: &mut [(usize, usize, F)]) {
  matrix.sort_by(|(r1, c1, _), (r2, c2, _)| (r1, c1).cmp(&(r2, c2)))
}

#[cfg(test)]
mod tests {
  use crate::traits::Group;

  use super::SparseMatrix;
  use pasta_curves::pallas::Point as G;

  #[test]
  fn test_matrix_creation() {
    type Fr = <G as Group>::Scalar;
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
    type Fr = <G as Group>::Scalar;
    let matrix_data = vec![
      (0, 1, Fr::from(2)),
      (1, 2, Fr::from(3)),
      (2, 0, Fr::from(4)),
    ];
    let sparse_matrix = SparseMatrix::<Fr>::new(&matrix_data, 3, 3);
    let vector = vec![Fr::from(1), Fr::from(2), Fr::from(3)];

    let result = sparse_matrix.multiply_vec(&vector);

    // Assuming the multiplication is done row by row,
    // Result[0] = 2.0 * 2.0 = 4.0
    // Result[1] = 3.0 * 3.0 = 9.0
    // Result[2] = 4.0 * 1.0 = 4.0
    assert_eq!(result, vec![Fr::from(4), Fr::from(9), Fr::from(4)]);
  }

  #[test]
  fn test_matrix_iter() {
    type Fr = <G as Group>::Scalar;
    let matrix_data = vec![
      (0, 1, Fr::from(2)),
      (1, 2, Fr::from(3)),
      (2, 0, Fr::from(4)),
    ];
    let sparse_matrix = SparseMatrix::<Fr>::new(&matrix_data, 3, 3);

    for val in sparse_matrix.iter() {
      println!("{:?}", val);
    }
  }
}
