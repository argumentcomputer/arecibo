//! Main components:
//! - `UniPoly`: an univariate dense polynomial in coefficient form (big endian),
//! - `CompressedUniPoly`: a univariate dense polynomial, compressed (omitted linear term), in coefficient form (little endian),
use std::ops::SubAssign;
use std::{
  cmp::Ordering,
  ops::{AddAssign, Index, IndexMut, MulAssign},
};

use ff::PrimeField;
use rand::{CryptoRng, RngCore};
use rayon::prelude::{IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator};
use ref_cast::RefCast;
use serde::{Deserialize, Serialize};

use crate::{
  provider::util::iterators::DoubleEndedIteratorExt as _,
  traits::{Group, TranscriptReprTrait},
};

// ax^2 + bx + c stored as vec![c, b, a]
// ax^3 + bx^2 + cx + d stored as vec![d, c, b, a]
#[derive(Debug, Clone, PartialEq, Eq, RefCast)]
#[repr(transparent)]
pub struct UniPoly<Scalar> {
  pub coeffs: Vec<Scalar>,
}

// ax^2 + bx + c stored as vec![c, a]
// ax^3 + bx^2 + cx + d stored as vec![d, c, a]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CompressedUniPoly<Scalar> {
  coeffs_except_linear_term: Vec<Scalar>,
}

impl<Scalar: PrimeField> UniPoly<Scalar> {
  pub fn new(coeffs: Vec<Scalar>) -> Self {
    let mut res = Self { coeffs };
    res.truncate_leading_zeros();
    res
  }

  fn zero() -> Self {
    Self::new(Vec::new())
  }

  /// Divide self by another polynomial, and returns the
  /// quotient and remainder.
  pub fn divide_with_q_and_r(&self, divisor: &Self) -> Option<(Self, Self)> {
    if self.is_zero() {
      Some((Self::zero(), Self::zero()))
    } else if divisor.is_zero() {
      None
    } else if self.degree() < divisor.degree() {
      Some((Self::zero(), self.clone()))
    } else {
      // Now we know that self.degree() >= divisor.degree();
      let mut quotient = vec![Scalar::ZERO; self.degree() - divisor.degree() + 1];
      let mut remainder: Self = self.clone();
      // Can unwrap here because we know self is not zero.
      let divisor_leading_inv = divisor.leading_coefficient().unwrap().invert().unwrap();
      while !remainder.is_zero() && remainder.degree() >= divisor.degree() {
        let cur_q_coeff = *remainder.leading_coefficient().unwrap() * divisor_leading_inv;
        let cur_q_degree = remainder.degree() - divisor.degree();
        quotient[cur_q_degree] = cur_q_coeff;

        for (i, div_coeff) in divisor.coeffs.iter().enumerate() {
          remainder.coeffs[cur_q_degree + i] -= &(cur_q_coeff * div_coeff);
        }
        while let Some(true) = remainder.coeffs.last().map(|c| c == &Scalar::ZERO) {
          remainder.coeffs.pop();
        }
      }
      Some((Self::new(quotient), remainder))
    }
  }

  /// Divides f(x) by x-a and returns quotient polynomial with no reminder
  /// This is a common use case for polynomial divisions in KZG-based PCS.
  pub fn divide_minus_u(&self, u: Scalar) -> Self {
    if self.is_zero() {
      Self::zero()
    } else {
      // On input f(x) and u compute the witness polynomial used to prove
      // that f(u) = v. The main part of this is to compute the
      // division (f(x) - f(u)) / (x - u), but we don't use a general
      // division algorithm, we make use of the fact that the division
      // never has a remainder, and that the denominator is always a linear
      // polynomial. The cost is (d-1) mults + (d-1) adds in E::Scalar, where
      // d is the degree of f.
      //
      // We use the fact that if we compute the quotient of f(x)/(x-u),
      // there will be a remainder, but it'll be v = f(u).  Put another way
      // the quotient of f(x)/(x-u) and (f(x) - f(v))/(x-u) is the
      // same.  One advantage is that computing f(u) could be decoupled
      // from kzg_open, it could be done later or separate from computing W.

      let d = self.coeffs.len();

      // Compute h(x) = f(x)/(x - u)
      let mut h = vec![Scalar::ZERO; d];
      for i in (1..d).rev() {
        h[i - 1] = self.coeffs[i] + h[i] * u;
      }
      Self::new(h)
    }
  }

  fn is_zero(&self) -> bool {
    self.coeffs.is_empty() || self.coeffs.iter().all(|c| c == &Scalar::ZERO)
  }

  fn truncate_leading_zeros(&mut self) {
    while self.coeffs.last().map_or(false, |c| c == &Scalar::ZERO) {
      self.coeffs.pop();
    }
  }

  fn leading_coefficient(&self) -> Option<&Scalar> {
    self.coeffs.last()
  }

  pub fn from_evals(evals: &[Scalar]) -> Self {
    // we only support degree-2 or degree-3 univariate polynomials
    assert!(evals.len() == 3 || evals.len() == 4);
    let two_inv = Scalar::from(2).invert().unwrap();
    let coeffs = if evals.len() == 3 {
      // ax^2 + bx + c
      let c = evals[0];
      let a = two_inv * (evals[2] - evals[1] - evals[1] + c);
      let b = evals[1] - c - a;
      vec![c, b, a]
    } else {
      // ax^3 + bx^2 + cx + d
      let six_inv = Scalar::from(6).invert().unwrap();

      let d = evals[0];
      let a = six_inv
        * (evals[3] - evals[2] - evals[2] - evals[2] + evals[1] + evals[1] + evals[1] - evals[0]);
      let b = two_inv
        * (evals[0] + evals[0] - evals[1] - evals[1] - evals[1] - evals[1] - evals[1]
          + evals[2]
          + evals[2]
          + evals[2]
          + evals[2]
          - evals[3]);
      let c = evals[1] - d - a - b;
      vec![d, c, b, a]
    };

    Self { coeffs }
  }

  pub fn degree(&self) -> usize {
    self.coeffs.len() - 1
  }

  pub fn eval_at_zero(&self) -> Scalar {
    self.coeffs[0]
  }

  pub fn eval_at_one(&self) -> Scalar {
    (0..self.coeffs.len())
      .into_par_iter()
      .map(|i| self.coeffs[i])
      .sum()
  }

  pub fn evaluate(&self, r: &Scalar) -> Scalar {
    self.coeffs.iter().rlc(r)
  }

  pub fn compress(&self) -> CompressedUniPoly<Scalar> {
    let coeffs_except_linear_term = [&self.coeffs[..1], &self.coeffs[2..]].concat();
    assert_eq!(coeffs_except_linear_term.len() + 1, self.coeffs.len());
    CompressedUniPoly {
      coeffs_except_linear_term,
    }
  }

  /// Returns a random polynomial
  pub fn random<R: RngCore + CryptoRng>(num_vars: usize, mut rng: &mut R) -> Self {
    Self::new(
      std::iter::from_fn(|| Some(Scalar::random(&mut rng)))
        .take(num_vars)
        .collect(),
    )
  }
}

impl<Scalar: PrimeField> CompressedUniPoly<Scalar> {
  // we require eval(0) + eval(1) = hint, so we can solve for the linear term as:
  // linear_term = hint - 2 * constant_term - deg2 term - deg3 term
  pub fn decompress(&self, hint: &Scalar) -> UniPoly<Scalar> {
    let mut linear_term =
      *hint - self.coeffs_except_linear_term[0] - self.coeffs_except_linear_term[0];
    for i in 1..self.coeffs_except_linear_term.len() {
      linear_term -= self.coeffs_except_linear_term[i];
    }

    let mut coeffs: Vec<Scalar> = Vec::new();
    coeffs.push(self.coeffs_except_linear_term[0]);
    coeffs.push(linear_term);
    coeffs.extend(&self.coeffs_except_linear_term[1..]);
    assert_eq!(self.coeffs_except_linear_term.len() + 1, coeffs.len());
    UniPoly { coeffs }
  }
}

impl<G: Group> TranscriptReprTrait<G> for UniPoly<G::Scalar> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    let coeffs = self.compress().coeffs_except_linear_term;
    coeffs
      .iter()
      .flat_map(|&t| t.to_repr().as_ref().to_vec())
      .collect::<Vec<u8>>()
  }
}

impl<Scalar: PrimeField> Index<usize> for UniPoly<Scalar> {
  type Output = Scalar;

  fn index(&self, index: usize) -> &Self::Output {
    &self.coeffs[index]
  }
}

impl<Scalar: PrimeField> IndexMut<usize> for UniPoly<Scalar> {
  fn index_mut(&mut self, index: usize) -> &mut Self::Output {
    &mut self.coeffs[index]
  }
}

impl<Scalar: PrimeField> AddAssign<&Scalar> for UniPoly<Scalar> {
  fn add_assign(&mut self, rhs: &Scalar) {
    self.coeffs.par_iter_mut().for_each(|c| *c += rhs);
  }
}

impl<Scalar: PrimeField> MulAssign<&Scalar> for UniPoly<Scalar> {
  fn mul_assign(&mut self, rhs: &Scalar) {
    self.coeffs.par_iter_mut().for_each(|c| *c *= rhs);
  }
}

impl<Scalar: PrimeField> AddAssign<&Self> for UniPoly<Scalar> {
  fn add_assign(&mut self, rhs: &Self) {
    let ordering = self.coeffs.len().cmp(&rhs.coeffs.len());
    #[allow(clippy::disallowed_methods)]
    for (lhs, rhs) in self.coeffs.iter_mut().zip(&rhs.coeffs) {
      *lhs += rhs;
    }
    if matches!(ordering, Ordering::Less) {
      self
        .coeffs
        .extend(rhs.coeffs[self.coeffs.len()..].iter().cloned());
    }
    if matches!(ordering, Ordering::Equal) {
      self.truncate_leading_zeros();
    }
  }
}

impl<Scalar: PrimeField> SubAssign<&Self> for UniPoly<Scalar> {
  fn sub_assign(&mut self, rhs: &Self) {
    let ordering = self.coeffs.len().cmp(&rhs.coeffs.len());
    #[allow(clippy::disallowed_methods)]
    for (lhs, rhs) in self.coeffs.iter_mut().zip(&rhs.coeffs) {
      *lhs -= rhs;
    }
    if matches!(ordering, Ordering::Less) {
      self
        .coeffs
        .extend(rhs.coeffs[self.coeffs.len()..].iter().cloned());
    }
    if matches!(ordering, Ordering::Equal) {
      self.truncate_leading_zeros();
    }
  }
}

impl<Scalar: PrimeField> AsRef<Vec<Scalar>> for UniPoly<Scalar> {
  fn as_ref(&self) -> &Vec<Scalar> {
    &self.coeffs
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::provider::{bn256_grumpkin, secp_secq::secp256k1};
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;

  fn test_from_evals_quad_with<F: PrimeField>() {
    // polynomial is 2x^2 + 3x + 1
    let e0 = F::ONE;
    let e1 = F::from(6);
    let e2 = F::from(15);
    let evals = vec![e0, e1, e2];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 3);
    assert_eq!(poly.coeffs[0], F::ONE);
    assert_eq!(poly.coeffs[1], F::from(3));
    assert_eq!(poly.coeffs[2], F::from(2));

    let hint = e0 + e1;
    let compressed_poly = poly.compress();
    let decompressed_poly = compressed_poly.decompress(&hint);
    for i in 0..decompressed_poly.coeffs.len() {
      assert_eq!(decompressed_poly.coeffs[i], poly.coeffs[i]);
    }

    let e3 = F::from(28);
    assert_eq!(poly.evaluate(&F::from(3)), e3);
  }

  #[test]
  fn test_from_evals_quad() {
    test_from_evals_quad_with::<pasta_curves::pallas::Scalar>();
    test_from_evals_quad_with::<bn256_grumpkin::bn256::Scalar>();
    test_from_evals_quad_with::<secp256k1::Scalar>();
  }

  fn test_from_evals_cubic_with<F: PrimeField>() {
    // polynomial is x^3 + 2x^2 + 3x + 1
    let e0 = F::ONE;
    let e1 = F::from(7);
    let e2 = F::from(23);
    let e3 = F::from(55);
    let evals = vec![e0, e1, e2, e3];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 4);

    assert_eq!(poly.coeffs[1], F::from(3));
    assert_eq!(poly.coeffs[2], F::from(2));
    assert_eq!(poly.coeffs[3], F::from(1));

    let hint = e0 + e1;
    let compressed_poly = poly.compress();
    let decompressed_poly = compressed_poly.decompress(&hint);
    for i in 0..decompressed_poly.coeffs.len() {
      assert_eq!(decompressed_poly.coeffs[i], poly.coeffs[i]);
    }

    let e4 = F::from(109);
    assert_eq!(poly.evaluate(&F::from(4)), e4);
  }

  #[test]
  fn test_from_evals_cubic() {
    test_from_evals_cubic_with::<pasta_curves::pallas::Scalar>();
    test_from_evals_cubic_with::<bn256_grumpkin::bn256::Scalar>();
    test_from_evals_cubic_with::<secp256k1::Scalar>()
  }

  /// Perform a naive n^2 multiplication of `self` by `other`.
  pub fn naive_mul<F: PrimeField>(ours: &UniPoly<F>, other: &UniPoly<F>) -> UniPoly<F> {
    if ours.is_zero() || other.is_zero() {
      UniPoly::zero()
    } else {
      let mut result = vec![F::ZERO; ours.degree() + other.degree() + 1];
      for (i, self_coeff) in ours.coeffs.iter().enumerate() {
        for (j, other_coeff) in other.coeffs.iter().enumerate() {
          result[i + j] += &(*self_coeff * other_coeff);
        }
      }
      UniPoly::new(result)
    }
  }

  fn divide_polynomials_random<Fr: PrimeField>() {
    let rng = &mut ChaCha20Rng::from_seed([0u8; 32]);

    for a_degree in 0..50 {
      for b_degree in 0..50 {
        let dividend = UniPoly::<Fr>::random(a_degree, rng);
        let divisor = UniPoly::<Fr>::random(b_degree, rng);

        if let Some((quotient, remainder)) = UniPoly::divide_with_q_and_r(&dividend, &divisor) {
          let mut prod = naive_mul(&divisor, &quotient);
          prod += &remainder;
          assert_eq!(dividend, prod)
        }
      }
    }
  }

  #[test]
  fn test_divide_minus_u() {
    fn test_inner<Fr: PrimeField>() {
      let rng = &mut ChaCha20Rng::from_seed([0u8; 32]);
      let dividend = UniPoly::<Fr>::random(50, rng);
      let u = Fr::random(rng);
      let divisor = UniPoly::new(vec![-u, Fr::ONE]);

      let (q1, _) = dividend.divide_with_q_and_r(&divisor).unwrap();
      let q2 = dividend.divide_minus_u(u);

      assert_eq!(q1, q2);
    }

    test_inner::<pasta_curves::pallas::Scalar>();
    test_inner::<bn256_grumpkin::bn256::Scalar>();
    test_inner::<secp256k1::Scalar>();
  }

  #[test]
  fn test_divide_polynomials_random() {
    divide_polynomials_random::<pasta_curves::pallas::Scalar>();
    divide_polynomials_random::<bn256_grumpkin::bn256::Scalar>();
    divide_polynomials_random::<secp256k1::Scalar>()
  }
}
