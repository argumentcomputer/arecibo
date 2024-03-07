use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bitvec::macros::internal::funty::Fundamental;
use neptune::circuit2::Elt;

use crate::parafold::cycle_fold::gadgets::ecc::AllocatedPoint;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::{CurveCycleEquipped, Engine};
use crate::Commitment;

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryCommitment<E: CurveCycleEquipped> {
  commitment: AllocatedPoint<<E::Secondary as Engine>::GE>,
}

impl<E: CurveCycleEquipped> AllocatedSecondaryCommitment<E> {
  /// Allocates a new point on the curve using coordinates provided by `coords`.
  /// If coords = None, it allocates the default infinity point
  pub fn alloc_unchecked<CS>(mut cs: CS, commitment: &Commitment<E::Secondary>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Self {
      commitment: AllocatedPoint::<<E::Secondary as Engine>::GE>::alloc_unchecked(
        cs.namespace(|| "alloc point unchecked"),
        commitment.to_coordinates(),
      ),
    }
  }

  pub fn alloc<CS>(mut cs: CS, commitment: Commitment<E::Secondary>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Self {
      commitment: AllocatedPoint::alloc(
        cs.namespace(|| "alloc point"),
        commitment.to_coordinates(),
      ),
    }
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> + '_ {
    self.commitment.as_preimage()
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
    let res = other
      .commitment
      .scalar_mul(cs.namespace(|| "scalar * other"), scalar_bits)?
      .add(cs.namespace(|| "self + (scalar * other)"), &self.commitment)?;
    Ok(Self { commitment: res })
  }

  pub fn select_default<CS>(&self, mut cs: CS, is_default: &Boolean) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let commitment = self
      .commitment
      .select_default(cs.namespace(|| "select default"), is_default)?;
    Ok(Self { commitment })
  }

  #[allow(unused)]
  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &Boolean)
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    self
      .commitment
      .enforce_trivial(cs.namespace(|| "enforce trivial"), is_trivial)
  }

  pub fn eq_native(&self, other: &Commitment<E::Secondary>) -> Option<bool> {
    let (x, y, is_infinity) = other.to_coordinates();
    let x_eq = self.commitment.x.get_value()? == x;
    let y_eq = self.commitment.y.get_value()? == y;
    let is_infinity_eq =
      self.commitment.is_infinity.get_value()? == E::Scalar::from(is_infinity.as_u64());

    Some(x_eq && y_eq && is_infinity_eq)
  }
}
