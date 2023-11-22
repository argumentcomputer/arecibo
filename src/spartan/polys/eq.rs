//! `EqPolynomial`: Represents multilinear extension of equality polynomials, evaluated based on binary input values.

use ff::PrimeField;
use rayon::prelude::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator};

/// Represents the multilinear extension polynomial (MLE) of the equality polynomial $eq(x,e)$, denoted as $\tilde{eq}(x, e)$.
///
/// The polynomial is defined by the formula:
/// $$
/// \tilde{eq}(x, e) = \prod_{i=1}^m(e_i * x_i + (1 - e_i) * (1 - x_i))
/// $$
///
/// Each element in the vector `r` corresponds to a component $e_i$, representing a bit from the binary representation of an input value $e$.
/// This polynomial evaluates to 1 if every component $x_i$ equals its corresponding $e_i$, and 0 otherwise.
///
/// For instance, for e = 6 (with a binary representation of 0b110), the vector r would be [1, 1, 0].
#[derive(Debug)]
pub struct EqPolynomial<Scalar: PrimeField> {
  pub(crate) r: Vec<Scalar>,
}

impl<Scalar: PrimeField> EqPolynomial<Scalar> {
  /// Creates a new `EqPolynomial` from a vector of Scalars `r`.
  ///
  /// Each Scalar in `r` corresponds to a bit from the binary representation of an input value `e`.
  ///
  /// Note that the `EqPolynomial` is fully-defined by its `evals`. We describe `r` in terms of the `EqPolynomial`'s
  /// evaluations on the boolean hypercube, but that does not imply that the elements of `r` must themselves be bits
  /// (`Scalar::ZERO` or `Scalar::ONE`). When evaluating `EqPolynomial` on the boolean hypercube, each Scalar in `r`
  /// contributes to the term associated with one bit of the input point, $$x_i$$. If the elements of `r` are indeed
  /// bits, then `EqPolynomial` acts as an equality predicate (testing each input point's equality with `e`). However,
  /// since `EqPolynomial` is just a polynomial, nothing requires that its defining inputs be provided as points of the
  /// boolean hypercube -- as long as its evals are calculated according to its defining formula.
  pub const fn new(r: Vec<Scalar>) -> Self {
    EqPolynomial { r }
  }

  /// Evaluates the `EqPolynomial` at a given point `rx`.
  ///
  /// This function computes the value of the polynomial at the point specified by `rx`.
  /// It expects `rx` to have the same length as the internal vector `r`.
  ///
  /// Panics if `rx` and `r` have different lengths.
  pub fn evaluate(&self, rx: &[Scalar]) -> Scalar {
    assert_eq!(self.r.len(), rx.len());
    (0..rx.len())
      .map(|i| self.r[i] * rx[i] + (Scalar::ONE - self.r[i]) * (Scalar::ONE - rx[i]))
      .fold(Scalar::ONE, |acc, item| acc * item)
  }

  /// Evaluates the `EqPolynomial` at all the `2^|r|` points in its domain.
  ///
  /// Returns a vector of Scalars, each corresponding to the polynomial evaluation at a specific point.
  pub fn evals(&self) -> Vec<Scalar> {
    Self::evals_from_points(&self.r)
  }

  /// Evaluates the `EqPolynomial` from the `2^|r|` points in its domain, without creating an intermediate polynomial
  /// representation.
  ///
  /// Returns a vector of Scalars, each corresponding to the polynomial evaluation at a specific point.
  pub fn evals_from_points(r: &[Scalar]) -> Vec<Scalar> {
    let ell = r.len();
    let mut evals: Vec<Scalar> = vec![Scalar::ZERO; (2_usize).pow(ell as u32)];
    let mut size = 1;
    evals[0] = Scalar::ONE;

    for r in r.iter().rev() {
      let (evals_left, evals_right) = evals.split_at_mut(size);
      let (evals_right, _) = evals_right.split_at_mut(size);

      evals_left
        .par_iter_mut()
        .zip_eq(evals_right.par_iter_mut())
        .for_each(|(running_product, term)| {
          // Most-significant bits' evals come first. Each new eval is a product of the previous, and this bit's term --
          // which is the evaluation, at 0 or 1, of (e_i * x_i + (1 - e_i) * (1 - x_i)).
          // Substituting r for e_i: (r * x_i + (1 - r) * (1 - x_i))
          // x_i is 'this bit', which is either 0 or 1.
          //
          // running_product is the product of all the more-significant bits' terms so far.
          // term represents this bit's term when x_i is 1, which by definition is r.
          // multiply them to get the total evaluation when this bit (x_i) is 1.
          *term = *running_product * r;
          // This bit's term when x_i = 0 is 1 - r.
          // (1 - r) * running_product = running_product - (r * running_product) = running_product - term
          *running_product -= *term;
        });

      // size doubles each iteration, because each new (less-significant) bit contributes an evaluation combining each
      // of the previous with a term evaluated with the new bit set to both 0 and 1.
      size *= 2;
    }

    evals
  }
}

impl<Scalar: PrimeField> FromIterator<Scalar> for EqPolynomial<Scalar> {
  fn from_iter<I: IntoIterator<Item = Scalar>>(iter: I) -> Self {
    let r: Vec<_> = iter.into_iter().collect();
    EqPolynomial { r }
  }
}

#[cfg(test)]
mod tests {
  use crate::provider;

  use super::*;
  use pasta_curves::Fp;

  fn test_eq_polynomial_with<F: PrimeField>() {
    // Most-significant 'bit' first.
    let eq_poly = EqPolynomial::<F>::new(vec![F::ONE, F::ZERO, F::ZERO]);
    let y = eq_poly.evaluate(vec![F::ONE, F::ONE, F::ONE].as_slice());
    assert_eq!(y, F::ZERO);

    let y = eq_poly.evaluate(vec![F::ONE, F::ZERO, F::ZERO].as_slice());
    assert_eq!(y, F::ONE);

    let eval_list = eq_poly.evals();
    assert_eq!((2_usize).pow(3), eval_list.len());

    for (i, &coeff) in eval_list.iter().enumerate() {
      // 0b100 corresponds to [F::ONE, F::ZERO, F::ZERO]
      if i == 0b100 {
        assert_eq!(coeff, F::ONE);
      } else {
        assert_eq!(coeff, F::ZERO);
      }
    }
  }

  #[test]
  fn test_eq_polynomial() {
    test_eq_polynomial_with::<Fp>();
    test_eq_polynomial_with::<provider::bn256_grumpkin::bn256::Scalar>();
    test_eq_polynomial_with::<provider::secp_secq::secp256k1::Scalar>();
  }
}
