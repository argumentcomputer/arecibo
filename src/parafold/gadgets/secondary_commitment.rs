use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::Boolean;
use ff::Field;

use crate::Commitment;
use crate::parafold::gadgets::ecc::AllocatedPoint;
use crate::parafold::hash::{AllocatedHasher, AllocatedHashWriter};
use crate::traits::{CurveCycleEquipped, Engine};
use crate::traits::commitment::CommitmentTrait;

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryCommitment<E: CurveCycleEquipped> {
  value: Commitment<E::Secondary>,
  point: AllocatedPoint<<E::Secondary as Engine>::GE>,
}

impl<E: CurveCycleEquipped> AllocatedSecondaryCommitment<E> {
  /// Allocates a new point on the curve using coordinates provided by `coords`.
  /// If coords = None, it allocates the default infinity point
  pub fn alloc_unchecked<CS>(mut cs: CS, commitment: Commitment<E::Secondary>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let point = AllocatedPoint::<<E::Secondary as Engine>::GE>::alloc_unchecked(
      cs.namespace(|| "alloc point unchecked"),
      commitment.to_coordinates(),
    );
    Self {
      value: commitment,
      point,
    }
  }

  pub fn alloc<CS>(mut cs: CS, commitment: Commitment<E::Secondary>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Self {
      value: commitment,
      point: AllocatedPoint::alloc(cs.namespace(|| "alloc point"), commitment.to_coordinates()),
    }
  }

  pub fn lc<CS>(
    &self,
    mut cs: CS,
    scalar_bits: &[Boolean],
    other: &Self,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let point = other
      .point
      .scalar_mul(cs.namespace(|| "scalar * other"), scalar_bits)?
      .add(cs.namespace(|| "self + (scalar * other)"), &self.point)?;
    let scalar = scalar_bits
      .iter()
      .rev()
      .fold(E::Base::ZERO, |scalar: E::Base, bit| {
        if bit.get_value().unwrap_or_default() {
          scalar.double() + E::Base::ONE
        } else {
          scalar.double()
        }
      });
    let value = self.value + other.value * scalar;
    Ok(Self { value, point })
  }

  pub fn select_default<CS>(&self, mut cs: CS, is_default: &Boolean) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let value = if is_default.get_value().unwrap_or_default() {
      Commitment::<E::Secondary>::default()
    } else {
      self.value
    };
    let point = self
      .point
      .select_default(cs.namespace(|| "select default"), is_default)?;
    Ok(Self { value, point })
  }

  pub fn get_value(&self) -> Option<Commitment<E::Secondary>> {
    debug_assert_eq!(self.value.to_coordinates(), self.point.get_value()?);

    Some(self.value)
  }
}

impl<E: CurveCycleEquipped> AllocatedHashWriter<E::Scalar> for AllocatedSecondaryCommitment<E> {
  fn write<H: AllocatedHasher<E::Scalar>>(&self, hasher: &mut H) {
    self.point.x.write(hasher);
    self.point.y.write(hasher);
  }
}
