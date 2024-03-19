use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::Boolean;

use crate::Commitment;
use crate::parafold::cycle_fold::hash_commitment;
use crate::parafold::gadgets::emulated::AllocatedBase;
use crate::parafold::hash::{AllocatedHasher, AllocatedHashWriter};
use crate::traits::CurveCycleEquipped;

/// Allocated [HashedCommitment]
///
/// # Details
/// Inside the primary circuit, a [Commitment] C is represented by the limbs of the hash `h_C = H(C.x, C.y)`.
/// The limbs of `h_C` are not range-checked and we assume this check occurs during the conversion to a big integer.
///
/// # TODO
/// - Investigate whether a `is_infinity` flag is needed. It could be used to avoid synthesizing secondary circuits
///   when the scalar multiplication is trivial.
#[derive(Debug, Clone)]
pub struct AllocatedPrimaryCommitment<E: CurveCycleEquipped> {
  #[allow(unused)]
  value: Commitment<E>,
  pub(crate) hash: AllocatedBase<E>,
}

impl<E: CurveCycleEquipped> AllocatedPrimaryCommitment<E> {
  pub fn alloc<CS: ConstraintSystem<E::Scalar>>(mut cs: CS, commitment: Commitment<E>) -> Self {
    let hash = hash_commitment::<E>(&commitment);
    let hash = AllocatedBase::alloc(cs.namespace(|| "alloc hash"), &hash);
    Self {
      value: commitment,
      hash,
    }
  }

  #[allow(unused)]
  pub fn get_value(&self) -> Commitment<E> {
    debug_assert_eq!(hash_commitment::<E>(&self.value), self.hash.get_value());
    self.value
  }

  pub fn enforce_trivial<CS: ConstraintSystem<E::Scalar>>(
    &self,
    cs: CS,
    is_default: &Boolean,
  ) -> Result<(), SynthesisError> {
    self.hash.enforce_trivial(cs, is_default)
  }
}

impl<E: CurveCycleEquipped> AllocatedHashWriter<E::Scalar> for AllocatedPrimaryCommitment<E> {
  fn write<H: AllocatedHasher<E::Scalar>>(&self, hasher: &mut H) {
    self.hash.write(hasher)
  }
}
