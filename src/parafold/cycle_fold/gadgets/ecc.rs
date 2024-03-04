use bellpepper::gadgets::Assignment;
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;

use bellpepper_core::SynthesisError::AssignmentMissing;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use neptune::circuit2::{Elt, PoseidonCircuit2};
use neptune::generic_array::typenum::U2;
use neptune::poseidon::PoseidonConstants;

use crate::gadgets::utils::{
  alloc_num_equals, alloc_one, alloc_zero, conditionally_select, conditionally_select2,
  select_num_or_one, select_num_or_zero, select_num_or_zero2, select_one_or_diff2,
  select_one_or_num2, select_zero_or_num2,
};
use crate::traits::Group;

/// `AllocatedPoint` provides an elliptic curve abstraction inside a circuit.
#[derive(Debug, Clone)]
pub struct AllocatedPoint<G: Group> {
  pub(crate) x: AllocatedNum<G::Base>,
  pub(crate) y: AllocatedNum<G::Base>,
  pub(crate) is_infinity: AllocatedNum<G::Base>,
}

impl<G: Group> AllocatedPoint<G> {
  pub fn select_default<CS>(self, mut cs: CS, is_default: &Boolean) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
  {
    let zero = alloc_zero(cs.namespace(|| "alloc 0"));
    let one = alloc_one(cs.namespace(|| "alloc 1"));
    let Self {
      x, y, is_infinity, ..
    } = self;
    let x = conditionally_select(cs.namespace(|| "select x"), &zero, &x, is_default)?;
    let y = conditionally_select(cs.namespace(|| "select y"), &zero, &y, is_default)?;
    let is_infinity = conditionally_select(
      cs.namespace(|| "select is_infinity"),
      &one,
      &is_infinity,
      is_default,
    )?;
    Ok(Self { x, y, is_infinity })
  }

  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &Boolean)
  where
    CS: ConstraintSystem<G::Base>,
  {
    // is_trivial => (is_identity == 1)
    // is_trivial == is_identity
    cs.enforce(
      || "is_trivial - E.is_infinity = 0",
      |lc| lc,
      |lc| lc,
      |_| is_trivial.lc(CS::one(), G::Base::ONE) - self.is_infinity.get_variable(),
    );
  }

  pub fn alloc<CS>(mut cs: CS, coords: (G::Base, G::Base, bool)) -> Self
  where
    CS: ConstraintSystem<G::Base>,
  {
    let commitment = Self::alloc_unchecked(cs.namespace(|| "alloc unchecked"), coords);
    cs.enforce(
      || "is_infinity => x = 0",
      |lc| lc + commitment.is_infinity.get_variable(),
      |lc| lc + commitment.x.get_variable(),
      |lc| lc,
    );
    cs.enforce(
      || "is_infinity => y = 0",
      |lc| lc + commitment.is_infinity.get_variable(),
      |lc| lc + commitment.y.get_variable(),
      |lc| lc,
    );
    commitment
      .check_on_curve(cs.namespace(|| "curve check"))
      .unwrap();
    commitment
  }

  pub fn alloc_hashed_input<CS>(
    mut cs: CS,
    coords: (G::Base, G::Base, bool),
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
  {
    let point = Self::alloc_unchecked(cs.namespace(|| "alloc"), coords);
    point.check_on_curve(cs.namespace(|| "check on curve"))?;
    point.inputize_hashed(cs.namespace(|| "inputize"))?;
    Ok(point)
  }

  /// Inputize a point by computing H(x,y), or 0 if `is_infinity = true`.
  pub fn inputize_hashed<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
  {
    let constants = PoseidonConstants::<G::Base, U2>::new();
    let hash = PoseidonCircuit2::new(
      vec![
        Elt::Allocated(self.x.clone()),
        Elt::Allocated(self.y.clone()),
      ],
      &constants,
    )
    .hash_to_allocated(cs.namespace(|| "hash"))?;

    let hash_final = AllocatedNum::alloc(cs.namespace(|| "alloc hash"), || {
      let is_infinity = self.is_infinity.get_value().ok_or(AssignmentMissing)?;
      if is_infinity == G::Base::ONE {
        Ok(G::Base::ZERO)
      } else {
        hash.get_value().ok_or(AssignmentMissing)
      }
    })?;

    // hash_final = (1-is_infinity)hash
    cs.enforce(
      || "select hash",
      |lc| lc + CS::one() - self.is_infinity.get_variable(),
      |lc| lc + hash.get_variable(),
      |lc| lc + hash_final.get_variable(),
    );
    hash_final.inputize(cs.namespace(|| "inputize"))
  }

  /// Allocates a new point on the curve using coordinates provided by `coords`.
  /// If coords = None, it allocates the default infinity point
  pub fn alloc_unchecked<CS>(mut cs: CS, coords: (G::Base, G::Base, bool)) -> Self
  where
    CS: ConstraintSystem<G::Base>,
  {
    let (x, y, is_infinity) = coords;
    let x = AllocatedNum::alloc_infallible(cs.namespace(|| "x"), || x);
    let y = AllocatedNum::alloc_infallible(cs.namespace(|| "y"), || y);

    let is_infinity = AllocatedNum::alloc_infallible(cs.namespace(|| "is_infinity"), || {
      if is_infinity {
        G::Base::ONE
      } else {
        G::Base::ZERO
      }
    });
    cs.enforce(
      || "is_infinity is bit",
      |lc| lc + is_infinity.get_variable(),
      |lc| lc + CS::one() - is_infinity.get_variable(),
      |lc| lc,
    );

    Self { x, y, is_infinity }
  }

  /// checks if `self` is on the curve or if it is infinity
  pub fn check_on_curve<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
  {
    // check that (x,y) is on the curve if it is not infinity
    // we will check that (1- is_infinity) * y^2 = (1-is_infinity) * (x^3 + Ax + B)
    // note that is_infinity is already restricted to be in the set {0, 1}
    let y_square = self.y.square(cs.namespace(|| "y_square"))?;
    let x_square = self.x.square(cs.namespace(|| "x_square"))?;
    let x_cube = self.x.mul(cs.namespace(|| "x_cube"), &x_square)?;

    let rhs = AllocatedNum::alloc(cs.namespace(|| "rhs"), || {
      if *self.is_infinity.get_value().get()? == G::Base::ONE {
        Ok(G::Base::ZERO)
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
  pub fn default<CS>(mut cs: CS) -> Self
  where
    CS: ConstraintSystem<G::Base>,
  {
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let one = alloc_one(cs.namespace(|| "one"));

    Self {
      x: zero.clone(),
      y: zero,
      is_infinity: one,
    }
  }

  /// Negates the provided point
  pub fn negate<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
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
    })
  }

  /// Add two points (may be equal)
  pub fn add<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
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
    CS: ConstraintSystem<G::Base>,
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
        G::Base::ONE
          - (G::Base::ONE - *self.is_infinity.get_value().get()?)
            * (G::Base::ONE - *other.is_infinity.get_value().get()?),
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
          G::Base::ONE
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
      let x_diff_inv = if *x_diff_is_actual.get_value().get()? == G::Base::ONE {
        // Set to default
        G::Base::ONE
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

    Ok(Self { x, y, is_infinity })
  }

  /// Doubles the supplied point.
  pub fn double<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
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
      Ok(G::Base::from(3) * self.x.get_value().get()? * self.x.get_value().get()?)
    })?;
    cs.enforce(
      || "Check prod 1",
      |lc| lc + (G::Base::from(3), self.x.get_variable()),
      |lc| lc + self.x.get_variable(),
      |lc| lc + prod_1.get_variable(),
    );

    let lambda = AllocatedNum::alloc(cs.namespace(|| "alloc lambda"), || {
      let tmp_inv = if *self.is_infinity.get_value().get()? == G::Base::ONE {
        // Return default value 1
        G::Base::ONE
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

    Ok(Self { x, y, is_infinity })
  }

  /// A gadget for scalar multiplication, optimized to use incomplete addition law.
  /// The optimization here is analogous to <https://github.com/arkworks-rs/r1cs-std/blob/6d64f379a27011b3629cf4c9cb38b7b7b695d5a0/src/groups/curves/short_weierstrass/mod.rs#L295>,
  /// except we use complete addition law over affine coordinates instead of projective coordinates for the tail bits
  pub fn scalar_mul<CS>(&self, mut cs: CS, scalar_bits: &[Boolean]) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
  {
    let split_len = core::cmp::min(scalar_bits.len(), (G::Base::NUM_BITS - 2) as usize);
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
      let acc = acc.to_allocated_point(&self.is_infinity);

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
    let default = Self::default(cs.namespace(|| "default"));
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
    };
    let mut p_complete = p.to_allocated_point(&self.is_infinity);

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
    CS: ConstraintSystem<G::Base>,
  {
    let x = conditionally_select(cs.namespace(|| "select x"), &a.x, &b.x, condition)?;

    let y = conditionally_select(cs.namespace(|| "select y"), &a.y, &b.y, condition)?;

    let is_infinity = conditionally_select(
      cs.namespace(|| "select is_infinity"),
      &a.is_infinity,
      &b.is_infinity,
      condition,
    )?;

    Ok(Self { x, y, is_infinity })
  }

  /// If condition outputs a otherwise infinity
  pub fn select_point_or_infinity<CS>(
    mut cs: CS,
    a: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
  {
    let x = select_num_or_zero(cs.namespace(|| "select x"), &a.x, condition)?;

    let y = select_num_or_zero(cs.namespace(|| "select y"), &a.y, condition)?;

    let is_infinity = select_num_or_one(
      cs.namespace(|| "select is_infinity"),
      &a.is_infinity,
      condition,
    )?;

    Ok(Self { x, y, is_infinity })
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<G::Base>> {
    [
      Elt::Allocated(self.x.clone()),
      Elt::Allocated(self.y.clone()),
    ]
  }
}

#[derive(Clone)]
/// `AllocatedPoint` but one that is guaranteed to be not infinity
pub struct AllocatedPointNonInfinity<G: Group> {
  x: AllocatedNum<G::Base>,
  y: AllocatedNum<G::Base>,
}

impl<G: Group> AllocatedPointNonInfinity<G> {
  /// Turns an `AllocatedPoint` into an `AllocatedPointNonInfinity` (assumes it is not infinity)
  pub fn from_allocated_point(p: &AllocatedPoint<G>) -> Self {
    Self {
      x: p.x.clone(),
      y: p.y.clone(),
    }
  }

  /// Returns an `AllocatedPoint` from an `AllocatedPointNonInfinity`
  pub fn to_allocated_point(&self, is_infinity: &AllocatedNum<G::Base>) -> AllocatedPoint<G> {
    AllocatedPoint {
      x: self.x.clone(),
      y: self.y.clone(),
      is_infinity: is_infinity.clone(),
    }
  }

  /// Add two points assuming self != +/- other
  pub fn add_incomplete<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<G::Base>,
  {
    // allocate a free variable that an honest prover sets to lambda = (y2-y1)/(x2-x1)
    let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
      if *other.x.get_value().get()? == *self.x.get_value().get()? {
        Ok(G::Base::ONE)
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

    Ok(Self { x, y })
  }

  /// doubles the point; since this is called with a point not at infinity, it is guaranteed to be not infinity
  pub fn double_incomplete<CS: ConstraintSystem<G::Base>>(
    &self,
    mut cs: CS,
  ) -> Result<Self, SynthesisError> {
    // lambda = (3 x^2 + a) / 2 * y

    let x_sq = self.x.square(cs.namespace(|| "x_sq"))?;

    let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
      let n = G::Base::from(3) * x_sq.get_value().get()? + G::group_params().0;
      let d = G::Base::from(2) * *self.y.get_value().get()?;
      if d == G::Base::ZERO {
        Ok(G::Base::ONE)
      } else {
        Ok(n * d.invert().unwrap())
      }
    })?;
    cs.enforce(
      || "Check that lambda is computed correctly",
      |lc| lc + lambda.get_variable(),
      |lc| lc + (G::Base::from(2), self.y.get_variable()),
      |lc| lc + (G::Base::from(3), x_sq.get_variable()) + (G::group_params().0, CS::one()),
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
      |lc| lc + x.get_variable() + (G::Base::from(2), self.x.get_variable()),
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

    Ok(Self { x, y })
  }

  /// If condition outputs a otherwise outputs b
  pub fn conditionally_select<CS: ConstraintSystem<G::Base>>(
    mut cs: CS,
    a: &Self,
    b: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError> {
    let x = conditionally_select(cs.namespace(|| "select x"), &a.x, &b.x, condition)?;
    let y = conditionally_select(cs.namespace(|| "select y"), &a.y, &b.y, condition)?;

    Ok(Self { x, y })
  }
}
