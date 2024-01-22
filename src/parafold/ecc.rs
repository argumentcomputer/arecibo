use std::marker::PhantomData;

use bellpepper::gadgets::Assignment;
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::gadgets::utils::{
  alloc_num_equals, alloc_one, alloc_zero, conditionally_select, conditionally_select2,
  select_num_or_one, select_num_or_zero, select_num_or_zero2, select_one_or_diff2,
  select_one_or_num2, select_zero_or_num2,
};
use crate::parafold::transcript::circuit::TranscriptRepresentable;
use crate::traits::Group;

/// `AllocatedPoint` provides an elliptic curve abstraction inside a circuit.
#[derive(Debug, Clone)]
pub struct AllocatedPoint<F: PrimeField, G: Group> {
  pub(crate) x: AllocatedNum<F>,
  pub(crate) y: AllocatedNum<F>,
  pub(crate) is_infinity: AllocatedNum<F>,
  _marker: PhantomData<G>,
}

impl<F: PrimeField, G: Group> TranscriptRepresentable<F> for AllocatedPoint<F, G> {
  fn to_field_vec(&self) -> Vec<AllocatedNum<F>> {
    todo!()
  }
}

impl<F, G> AllocatedPoint<F, G>
where
  F: PrimeField,
  // G: Group,
  G: Group<Base = F>,
{
  /// Allocates a new point on the curve using coordinates provided by `coords`.
  /// If coords = None, it allocates the default infinity point
  pub fn alloc<CS>(mut cs: CS, coords: Option<(F, F, bool)>) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(coords.map_or(F::ZERO, |c| c.0)))?;
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(coords.map_or(F::ZERO, |c| c.1)))?;
    let is_infinity = AllocatedNum::alloc(cs.namespace(|| "is_infinity"), || {
      Ok(if coords.map_or(true, |c| c.2) {
        F::ONE
      } else {
        F::ZERO
      })
    })?;
    cs.enforce(
      || "is_infinity is bit",
      |lc| lc + is_infinity.get_variable(),
      |lc| lc + CS::one() - is_infinity.get_variable(),
      |lc| lc,
    );

    Ok(Self {
      x,
      y,
      is_infinity,
      _marker: PhantomData::default(),
    })
  }

  /// checks if `self` is on the curve or if it is infinity
  pub fn check_on_curve<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    // check that (x,y) is on the curve if it is not infinity
    // we will check that (1- is_infinity) * y^2 = (1-is_infinity) * (x^3 + Ax + B)
    // note that is_infinity is already restricted to be in the set {0, 1}
    let y_square = self.y.square(cs.namespace(|| "y_square"))?;
    let x_square = self.x.square(cs.namespace(|| "x_square"))?;
    let x_cube = self.x.mul(cs.namespace(|| "x_cube"), &x_square)?;

    let rhs = AllocatedNum::alloc(cs.namespace(|| "rhs"), || {
      if *self.is_infinity.get_value().get()? == F::ONE {
        Ok(F::ZERO)
      } else {
        Ok(
          *x_cube.get_value().get()?
            + *self.x.get_value().get()? * G::group_params().0
            + G::group_params().1,
        )
      }
    })?;

    cs.enforce(
      || "rhs = (1-is_infinity) * (x^3 + Ax + B)",
      |lc| {
        lc + x_cube.get_variable()
          + (G::group_params().0, self.x.get_variable())
          + (G::group_params().1, CS::one())
      },
      |lc| lc + CS::one() - self.is_infinity.get_variable(),
      |lc| lc + rhs.get_variable(),
    );

    // check that (1-infinity) * y_square = rhs
    cs.enforce(
      || "check that y_square * (1 - is_infinity) = rhs",
      |lc| lc + y_square.get_variable(),
      |lc| lc + CS::one() - self.is_infinity.get_variable(),
      |lc| lc + rhs.get_variable(),
    );

    Ok(())
  }

  /// Allocates a default point on the curve, set to the identity point.
  pub fn default<CS>(mut cs: CS) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let one = alloc_one(cs.namespace(|| "one"));

    Ok(Self {
      x: zero.clone(),
      y: zero,
      is_infinity: one,
      _marker: PhantomData::default(),
    })
  }

  /// Returns coordinates associated with the point.
  pub const fn get_coordinates(&self) -> (&AllocatedNum<F>, &AllocatedNum<F>, &AllocatedNum<F>) {
    (&self.x, &self.y, &self.is_infinity)
  }

  /// Negates the provided point
  pub fn negate<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(-*self.y.get_value().get()?))?;

    cs.enforce(
      || "check y = - self.y",
      |lc| lc + self.y.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc - y.get_variable(),
    );

    Ok(Self {
      x: self.x.clone(),
      y,
      is_infinity: self.is_infinity.clone(),
      _marker: PhantomData::default(),
    })
  }

  /// Add two points (may be equal)
  pub fn add<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    // Compute boolean equal indicating if self = other

    let equal_x = alloc_num_equals(
      cs.namespace(|| "check self.x == other.x"),
      &self.x,
      &other.x,
    )?;

    let equal_y = alloc_num_equals(
      cs.namespace(|| "check self.y == other.y"),
      &self.y,
      &other.y,
    )?;

    // Compute the result of the addition and the result of double self
    let result_from_add = self.add_internal(cs.namespace(|| "add internal"), other, &equal_x)?;
    let result_from_double = self.double(cs.namespace(|| "double"))?;

    // Output:
    // If (self == other) {
    //  return double(self)
    // }else {
    //  if (self.x == other.x){
    //      return infinity [negation]
    //  } else {
    //      return add(self, other)
    //  }
    // }
    let result_for_equal_x = Self::select_point_or_infinity(
      cs.namespace(|| "equal_y ? result_from_double : infinity"),
      &result_from_double,
      &Boolean::from(equal_y),
    )?;

    Self::conditionally_select(
      cs.namespace(|| "equal ? result_from_double : result_from_add"),
      &result_for_equal_x,
      &result_from_add,
      &Boolean::from(equal_x),
    )
  }

  /// Adds other point to this point and returns the result. Assumes that the two points are
  /// different and that both `other.is_infinity` and `this.is_infinty` are bits
  pub fn add_internal<CS>(
    &self,
    mut cs: CS,
    other: &Self,
    equal_x: &AllocatedBit,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    //************************************************************************/
    // lambda = (other.y - self.y) * (other.x - self.x).invert().unwrap();
    //************************************************************************/
    // First compute (other.x - self.x).inverse()
    // If either self or other are the infinity point or self.x = other.x  then compute bogus values
    // Specifically,
    // x_diff = self != inf && other != inf && self.x == other.x ? (other.x - self.x) : 1

    // Compute self.is_infinity OR other.is_infinity =
    // NOT(NOT(self.is_ifninity) AND NOT(other.is_infinity))
    let at_least_one_inf = AllocatedNum::alloc(cs.namespace(|| "at least one inf"), || {
      Ok(
        F::ONE
          - (F::ONE - *self.is_infinity.get_value().get()?)
            * (F::ONE - *other.is_infinity.get_value().get()?),
      )
    })?;
    cs.enforce(
      || "1 - at least one inf = (1-self.is_infinity) * (1-other.is_infinity)",
      |lc| lc + CS::one() - self.is_infinity.get_variable(),
      |lc| lc + CS::one() - other.is_infinity.get_variable(),
      |lc| lc + CS::one() - at_least_one_inf.get_variable(),
    );

    // Now compute x_diff_is_actual = at_least_one_inf OR equal_x
    let x_diff_is_actual =
      AllocatedNum::alloc(cs.namespace(|| "allocate x_diff_is_actual"), || {
        Ok(if *equal_x.get_value().get()? {
          F::ONE
        } else {
          *at_least_one_inf.get_value().get()?
        })
      })?;
    cs.enforce(
      || "1 - x_diff_is_actual = (1-equal_x) * (1-at_least_one_inf)",
      |lc| lc + CS::one() - at_least_one_inf.get_variable(),
      |lc| lc + CS::one() - equal_x.get_variable(),
      |lc| lc + CS::one() - x_diff_is_actual.get_variable(),
    );

    // x_diff = 1 if either self.is_infinity or other.is_infinity or self.x = other.x else self.x -
    // other.x
    let x_diff = select_one_or_diff2(
      cs.namespace(|| "Compute x_diff"),
      &other.x,
      &self.x,
      &x_diff_is_actual,
    )?;

    let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
      let x_diff_inv = if *x_diff_is_actual.get_value().get()? == F::ONE {
        // Set to default
        F::ONE
      } else {
        // Set to the actual inverse
        (*other.x.get_value().get()? - *self.x.get_value().get()?)
          .invert()
          .unwrap()
      };

      Ok((*other.y.get_value().get()? - *self.y.get_value().get()?) * x_diff_inv)
    })?;
    cs.enforce(
      || "Check that lambda is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + x_diff.get_variable(),
      |lc| lc + other.y.get_variable() - self.y.get_variable(),
    );

    //************************************************************************/
    // x = lambda * lambda - self.x - other.x;
    //************************************************************************/
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(
        *lambda.get_value().get()? * lambda.get_value().get()?
          - *self.x.get_value().get()?
          - *other.x.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "check that x is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + lambda.get_variable(),
      |lc| lc + x.get_variable() + self.x.get_variable() + other.x.get_variable(),
    );

    //************************************************************************/
    // y = lambda * (self.x - x) - self.y;
    //************************************************************************/
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(
        *lambda.get_value().get()? * (*self.x.get_value().get()? - *x.get_value().get()?)
          - *self.y.get_value().get()?,
      )
    })?;

    cs.enforce(
      || "Check that y is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + self.x.get_variable() - x.get_variable(),
      |lc| lc + y.get_variable() + self.y.get_variable(),
    );

    //************************************************************************/
    // We only return the computed x, y if neither of the points is infinity and self.x != other.y
    // if self.is_infinity return other.clone()
    // elif other.is_infinity return self.clone()
    // elif self.x == other.x return infinity
    // Otherwise return the computed points.
    //************************************************************************/
    // Now compute the output x

    let x1 = conditionally_select2(
      cs.namespace(|| "x1 = other.is_infinity ? self.x : x"),
      &self.x,
      &x,
      &other.is_infinity,
    )?;

    let x = conditionally_select2(
      cs.namespace(|| "x = self.is_infinity ? other.x : x1"),
      &other.x,
      &x1,
      &self.is_infinity,
    )?;

    let y1 = conditionally_select2(
      cs.namespace(|| "y1 = other.is_infinity ? self.y : y"),
      &self.y,
      &y,
      &other.is_infinity,
    )?;

    let y = conditionally_select2(
      cs.namespace(|| "y = self.is_infinity ? other.y : y1"),
      &other.y,
      &y1,
      &self.is_infinity,
    )?;

    let is_infinity1 = select_num_or_zero2(
      cs.namespace(|| "is_infinity1 = other.is_infinity ? self.is_infinity : 0"),
      &self.is_infinity,
      &other.is_infinity,
    )?;

    let is_infinity = conditionally_select2(
      cs.namespace(|| "is_infinity = self.is_infinity ? other.is_infinity : is_infinity1"),
      &other.is_infinity,
      &is_infinity1,
      &self.is_infinity,
    )?;

    Ok(Self {
      x,
      y,
      is_infinity,
      _marker: PhantomData::default(),
    })
  }

  /// Doubles the supplied point.
  pub fn double<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    //*************************************************************/
    // lambda = (G::Base::from(3) * self.x * self.x + G::A())
    //  * (G::Base::from(2)) * self.y).invert().unwrap();
    /*************************************************************/

    // Compute tmp = (G::Base::ONE + G::Base::ONE)* self.y ? self != inf : 1
    let tmp_actual = AllocatedNum::alloc(cs.namespace(|| "tmp_actual"), || {
      Ok(*self.y.get_value().get()? + *self.y.get_value().get()?)
    })?;
    cs.enforce(
      || "check tmp_actual",
      |lc| lc + CS::one() + CS::one(),
      |lc| lc + self.y.get_variable(),
      |lc| lc + tmp_actual.get_variable(),
    );

    let tmp = select_one_or_num2(cs.namespace(|| "tmp"), &tmp_actual, &self.is_infinity)?;

    // Now compute lambda as (G::Base::from(3) * self.x * self.x + G::A()) * tmp_inv

    let prod_1 = AllocatedNum::alloc(cs.namespace(|| "alloc prod 1"), || {
      Ok(F::from(3) * self.x.get_value().get()? * self.x.get_value().get()?)
    })?;
    cs.enforce(
      || "Check prod 1",
      |lc| lc + (F::from(3), self.x.get_variable()),
      |lc| lc + self.x.get_variable(),
      |lc| lc + prod_1.get_variable(),
    );

    let lambda = AllocatedNum::alloc(cs.namespace(|| "alloc lambda"), || {
      let tmp_inv = if *self.is_infinity.get_value().get()? == F::ONE {
        // Return default value 1
        F::ONE
      } else {
        // Return the actual inverse
        (*tmp.get_value().get()?).invert().unwrap()
      };

      Ok(tmp_inv * (*prod_1.get_value().get()? + G::group_params().0))
    })?;

    cs.enforce(
      || "Check lambda",
      |lc| lc + tmp.get_variable(),
      |lc| lc + lambda.get_variable(),
      |lc| lc + prod_1.get_variable() + (G::group_params().0, CS::one()),
    );

    /*************************************************************/
    //          x = lambda * lambda - self.x - self.x;
    /*************************************************************/

    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(
        ((*lambda.get_value().get()?) * (*lambda.get_value().get()?))
          - *self.x.get_value().get()?
          - self.x.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "Check x",
      |lc| lc + lambda.get_variable(),
      |lc| lc + lambda.get_variable(),
      |lc| lc + x.get_variable() + self.x.get_variable() + self.x.get_variable(),
    );

    /*************************************************************/
    //        y = lambda * (self.x - x) - self.y;
    /*************************************************************/

    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(
        (*lambda.get_value().get()?) * (*self.x.get_value().get()? - x.get_value().get()?)
          - self.y.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "Check y",
      |lc| lc + lambda.get_variable(),
      |lc| lc + self.x.get_variable() - x.get_variable(),
      |lc| lc + y.get_variable() + self.y.get_variable(),
    );

    /*************************************************************/
    // Only return the computed x and y if the point is not infinity
    /*************************************************************/

    // x
    let x = select_zero_or_num2(cs.namespace(|| "final x"), &x, &self.is_infinity)?;

    // y
    let y = select_zero_or_num2(cs.namespace(|| "final y"), &y, &self.is_infinity)?;

    // is_infinity
    let is_infinity = self.is_infinity.clone();

    Ok(Self {
      x,
      y,
      is_infinity,
      _marker: PhantomData::default(),
    })
  }

  /// A gadget for scalar multiplication, optimized to use incomplete addition law.
  /// The optimization here is analogous to <https://github.com/arkworks-rs/r1cs-std/blob/6d64f379a27011b3629cf4c9cb38b7b7b695d5a0/src/groups/curves/short_weierstrass/mod.rs#L295>,
  /// except we use complete addition law over affine coordinates instead of projective coordinates for the tail bits
  pub fn scalar_mul<CS>(
    &self,
    mut cs: CS,
    scalar_bits: &[AllocatedBit],
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    let split_len = core::cmp::min(scalar_bits.len(), (F::NUM_BITS - 2) as usize);
    let (incomplete_bits, complete_bits) = scalar_bits.split_at(split_len);

    // we convert AllocatedPoint into AllocatedPointNonInfinity; we deal with the case where self.is_infinity = 1 below
    let mut p = AllocatedPointNonInfinity::from_allocated_point(self);

    // we assume the first bit to be 1, so we must initialize acc to self and double it
    // we remove this assumption below
    let mut acc = p;
    p = acc.double_incomplete(cs.namespace(|| "double"))?;

    // perform the double-and-add loop to compute the scalar mul using incomplete addition law
    for (i, bit) in incomplete_bits.iter().enumerate().skip(1) {
      let temp = acc.add_incomplete(cs.namespace(|| format!("add {i}")), &p)?;
      acc = AllocatedPointNonInfinity::conditionally_select(
        cs.namespace(|| format!("acc_iteration_{i}")),
        &temp,
        &acc,
        &Boolean::from(bit.clone()),
      )?;

      p = p.double_incomplete(cs.namespace(|| format!("double {i}")))?;
    }

    // convert back to AllocatedPoint
    let res = {
      // we set acc.is_infinity = self.is_infinity
      let acc = acc.to_allocated_point(&self.is_infinity)?;

      // we remove the initial slack if bits[0] is as not as assumed (i.e., it is not 1)
      let acc_minus_initial = {
        let neg = self.negate(cs.namespace(|| "negate"))?;
        acc.add(cs.namespace(|| "res minus self"), &neg)
      }?;

      Self::conditionally_select(
        cs.namespace(|| "remove slack if necessary"),
        &acc,
        &acc_minus_initial,
        &Boolean::from(scalar_bits[0].clone()),
      )?
    };

    // when self.is_infinity = 1, return the default point, else return res
    // we already set res.is_infinity to be self.is_infinity, so we do not need to set it here
    let default = Self::default(cs.namespace(|| "default"))?;
    let x = conditionally_select2(
      cs.namespace(|| "check if self.is_infinity is zero (x)"),
      &default.x,
      &res.x,
      &self.is_infinity,
    )?;

    let y = conditionally_select2(
      cs.namespace(|| "check if self.is_infinity is zero (y)"),
      &default.y,
      &res.y,
      &self.is_infinity,
    )?;

    // we now perform the remaining scalar mul using complete addition law
    let mut acc = Self {
      x,
      y,
      is_infinity: res.is_infinity,
      _marker: PhantomData::default(),
    };
    let mut p_complete = p.to_allocated_point(&self.is_infinity)?;

    for (i, bit) in complete_bits.iter().enumerate() {
      let temp = acc.add(cs.namespace(|| format!("add_complete {i}")), &p_complete)?;
      acc = Self::conditionally_select(
        cs.namespace(|| format!("acc_complete_iteration_{i}")),
        &temp,
        &acc,
        &Boolean::from(bit.clone()),
      )?;

      p_complete = p_complete.double(cs.namespace(|| format!("double_complete {i}")))?;
    }

    Ok(acc)
  }

  /// If condition outputs a otherwise outputs b
  pub fn conditionally_select<CS>(
    mut cs: CS,
    a: &Self,
    b: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    let x = conditionally_select(cs.namespace(|| "select x"), &a.x, &b.x, condition)?;

    let y = conditionally_select(cs.namespace(|| "select y"), &a.y, &b.y, condition)?;

    let is_infinity = conditionally_select(
      cs.namespace(|| "select is_infinity"),
      &a.is_infinity,
      &b.is_infinity,
      condition,
    )?;

    Ok(Self {
      x,
      y,
      is_infinity,
      _marker: PhantomData::default(),
    })
  }

  /// If condition outputs a otherwise infinity
  pub fn select_point_or_infinity<CS>(
    mut cs: CS,
    a: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    let x = select_num_or_zero(cs.namespace(|| "select x"), &a.x, condition)?;

    let y = select_num_or_zero(cs.namespace(|| "select y"), &a.y, condition)?;

    let is_infinity = select_num_or_one(
      cs.namespace(|| "select is_infinity"),
      &a.is_infinity,
      condition,
    )?;

    Ok(Self {
      x,
      y,
      is_infinity,
      _marker: PhantomData::default(),
    })
  }
}

#[derive(Clone)]
/// `AllocatedPoint` but one that is guaranteed to be not infinity
pub struct AllocatedPointNonInfinity<F: PrimeField, G: Group> {
  x: AllocatedNum<F>,
  y: AllocatedNum<F>,
  _marker: PhantomData<G>,
}

impl<F, G> AllocatedPointNonInfinity<F, G>
where
  F: PrimeField,
  G: Group<Base = F>,
{
  /// Creates a new `AllocatedPointNonInfinity` from the specified coordinates
  pub fn new(x: AllocatedNum<F>, y: AllocatedNum<F>) -> Self {
    Self {
      x,
      y,
      _marker: PhantomData::default(),
    }
  }

  /// Allocates a new point on the curve using coordinates provided by `coords`.
  pub fn alloc<CS: ConstraintSystem<F>>(
    mut cs: CS,
    coords: Option<(F, F)>,
  ) -> Result<Self, SynthesisError> {
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      coords.map_or(Err(SynthesisError::AssignmentMissing), |c| Ok(c.0))
    })?;
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      coords.map_or(Err(SynthesisError::AssignmentMissing), |c| Ok(c.1))
    })?;

    Ok(Self {
      x,
      y,
      _marker: PhantomData::default(),
    })
  }

  /// Turns an `AllocatedPoint` into an `AllocatedPointNonInfinity` (assumes it is not infinity)
  pub fn from_allocated_point(p: &AllocatedPoint<F, G>) -> Self {
    Self {
      x: p.x.clone(),
      y: p.y.clone(),
      _marker: PhantomData::default(),
    }
  }

  /// Returns an `AllocatedPoint` from an `AllocatedPointNonInfinity`
  pub fn to_allocated_point(
    &self,
    is_infinity: &AllocatedNum<F>,
  ) -> Result<AllocatedPoint<F, G>, SynthesisError> {
    Ok(AllocatedPoint {
      x: self.x.clone(),
      y: self.y.clone(),
      is_infinity: is_infinity.clone(),
      _marker: PhantomData::default(),
    })
  }

  /// Returns coordinates associated with the point.
  pub const fn get_coordinates(&self) -> (&AllocatedNum<F>, &AllocatedNum<F>) {
    (&self.x, &self.y)
  }

  /// Add two points assuming self != +/- other
  pub fn add_incomplete<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    // allocate a free variable that an honest prover sets to lambda = (y2-y1)/(x2-x1)
    let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
      if *other.x.get_value().get()? == *self.x.get_value().get()? {
        Ok(F::ONE)
      } else {
        Ok(
          (*other.y.get_value().get()? - *self.y.get_value().get()?)
            * (*other.x.get_value().get()? - *self.x.get_value().get()?)
              .invert()
              .unwrap(),
        )
      }
    })?;
    cs.enforce(
      || "Check that lambda is computed correctly",
      |lc| lc + lambda.get_variable(),
      |lc| lc + other.x.get_variable() - self.x.get_variable(),
      |lc| lc + other.y.get_variable() - self.y.get_variable(),
    );

    //************************************************************************/
    // x = lambda * lambda - self.x - other.x;
    //************************************************************************/
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(
        *lambda.get_value().get()? * lambda.get_value().get()?
          - *self.x.get_value().get()?
          - *other.x.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "check that x is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + lambda.get_variable(),
      |lc| lc + x.get_variable() + self.x.get_variable() + other.x.get_variable(),
    );

    //************************************************************************/
    // y = lambda * (self.x - x) - self.y;
    //************************************************************************/
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(
        *lambda.get_value().get()? * (*self.x.get_value().get()? - *x.get_value().get()?)
          - *self.y.get_value().get()?,
      )
    })?;

    cs.enforce(
      || "Check that y is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + self.x.get_variable() - x.get_variable(),
      |lc| lc + y.get_variable() + self.y.get_variable(),
    );

    Ok(Self {
      x,
      y,
      _marker: PhantomData::default(),
    })
  }

  /// doubles the point; since this is called with a point not at infinity, it is guaranteed to be not infinity
  pub fn double_incomplete<CS: ConstraintSystem<F>>(
    &self,
    mut cs: CS,
  ) -> Result<Self, SynthesisError> {
    // lambda = (3 x^2 + a) / 2 * y

    let x_sq = self.x.square(cs.namespace(|| "x_sq"))?;

    let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
      let n = F::from(3) * x_sq.get_value().get()? + G::group_params().0;
      let d = F::from(2) * *self.y.get_value().get()?;
      if d == F::ZERO {
        Ok(F::ONE)
      } else {
        Ok(n * d.invert().unwrap())
      }
    })?;
    cs.enforce(
      || "Check that lambda is computed correctly",
      |lc| lc + lambda.get_variable(),
      |lc| lc + (F::from(2), self.y.get_variable()),
      |lc| lc + (F::from(3), x_sq.get_variable()) + (G::group_params().0, CS::one()),
    );

    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(
        *lambda.get_value().get()? * *lambda.get_value().get()?
          - *self.x.get_value().get()?
          - *self.x.get_value().get()?,
      )
    })?;

    cs.enforce(
      || "check that x is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + lambda.get_variable(),
      |lc| lc + x.get_variable() + (F::from(2), self.x.get_variable()),
    );

    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(
        *lambda.get_value().get()? * (*self.x.get_value().get()? - *x.get_value().get()?)
          - *self.y.get_value().get()?,
      )
    })?;

    cs.enforce(
      || "Check that y is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + self.x.get_variable() - x.get_variable(),
      |lc| lc + y.get_variable() + self.y.get_variable(),
    );

    Ok(Self {
      x,
      y,
      _marker: PhantomData::default(),
    })
  }

  /// If condition outputs a otherwise outputs b
  pub fn conditionally_select<CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Self,
    b: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError> {
    let x = conditionally_select(cs.namespace(|| "select x"), &a.x, &b.x, condition)?;
    let y = conditionally_select(cs.namespace(|| "select y"), &a.y, &b.y, condition)?;

    Ok(Self {
      x,
      y,
      _marker: PhantomData::default(),
    })
  }
}
