use std::marker::PhantomData;

use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::Num;
use bellpepper_core::{ConstraintSystem, SynthesisError, Variable};
use bellpepper_emulated::field_element::{
  EmulatedFieldElement, EmulatedFieldParams, EmulatedLimbs, PseudoMersennePrime,
};
use ff::{Field, PrimeField};
use itertools::{zip_eq, Itertools};
use neptune::circuit2::Elt;
use num_bigint::{BigInt, Sign};
use num_traits::{Num as num_Num, One};

use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS};
use crate::traits::CurveCycleEquipped;

#[derive(Debug, Clone)]
pub struct BaseParams<E: CurveCycleEquipped>(PhantomData<E>);

impl<E: CurveCycleEquipped> EmulatedFieldParams for BaseParams<E> {
  fn num_limbs() -> usize {
    BN_N_LIMBS
  }

  fn bits_per_limb() -> usize {
    BN_LIMB_WIDTH
  }

  fn modulus() -> BigInt {
    BigInt::from_str_radix(&E::Base::MODULUS[2..], 16).unwrap()
  }

  fn is_modulus_pseudo_mersenne() -> bool {
    true
  }
  fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
    let p = Self::modulus();
    let e: u32 = p.bits().try_into().unwrap();
    let two_pow_e = BigInt::one() << e;
    let c = two_pow_e - p;
    Some(PseudoMersennePrime { e, c })
  }
}

#[derive(Debug, Clone)]
pub struct AllocatedBase<E: CurveCycleEquipped>(EmulatedFieldElement<E::Scalar, BaseParams<E>>);

impl<E: CurveCycleEquipped> AllocatedBase<E> {
  pub fn zero() -> Self {
    Self(EmulatedFieldElement::zero())
  }

  pub fn from_bits(one: Variable, bits: &[Boolean]) -> Self {
    let bases = std::iter::successors(Some(E::Scalar::ONE), |base| Some(base.double()))
      .take(BaseParams::<E>::bits_per_limb())
      .collect::<Vec<_>>();

    let limbs = bits
      .chunks(BaseParams::<E>::bits_per_limb())
      .map(|bits| {
        zip_eq(&bases, bits).fold(Num::<E::Scalar>::zero(), |num, (base, bit)| {
          num.add_bool_with_coeff(one, &bit, base.clone())
        })
      })
      .pad_using(BaseParams::<E>::num_limbs(), |_| Num::zero())
      .collect::<Vec<_>>();

    assert_eq!(limbs.len(), BaseParams::<E>::num_limbs());

    Self(EmulatedFieldElement::new_internal_element(
      EmulatedLimbs::Allocated(limbs),
      0,
    ))
  }

  pub fn alloc<CS: ConstraintSystem<E::Scalar>>(mut cs: CS, base: E::Base) -> Self {
    let base = Self::alloc_unchecked(cs.namespace(|| "alloc unchecked"), base);
    base
      .0
      .check_field_membership(&mut cs.namespace(|| "check membership"))
      .unwrap();
    base
  }

  pub fn alloc_unchecked<CS: ConstraintSystem<E::Scalar>>(mut cs: CS, base: E::Base) -> Self {
    let base = BigInt::from_bytes_le(Sign::Plus, base.to_repr().as_ref());
    let base = EmulatedFieldElement::from(&base)
      .allocate_field_element_unchecked(&mut cs.namespace(|| "alloc unchecked"))
      .unwrap();
    Self(base)
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> {
    // Merge into two 128-bit limbs for more efficient hashing
    let limbs = self.0.compact_limbs(2, 128).unwrap();
    let EmulatedLimbs::Allocated(limbs) = limbs else {
      unreachable!()
    };
    limbs.into_iter().map(Elt::Num)
  }

  pub fn add<CS: ConstraintSystem<E::Scalar>>(
    &self,
    mut cs: CS,
    other: &Self,
  ) -> Result<Self, SynthesisError> {
    let res = self.0.add(&mut cs.namespace(|| "add"), &other.0)?;
    let res = res.reduce(&mut cs.namespace(|| "reduce"))?;
    Ok(Self(res))
  }

  pub fn lc<CS: ConstraintSystem<E::Scalar>>(
    &self,
    mut cs: CS,
    scalar: &Self,
    other: &Self,
  ) -> Result<Self, SynthesisError> {
    let res = other.0.mul(&mut cs.namespace(|| "mul"), &scalar.0)?;
    let res = res.add(&mut cs.namespace(|| "add"), &self.0)?;
    let res = res.reduce(&mut cs.namespace(|| "reduce"))?;
    Ok(Self(res))
  }

  pub fn conditionally_select<CS>(
    mut cs: CS,
    a0: &Self,
    a1: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Ok(Self(EmulatedFieldElement::conditionally_select(
      &mut cs, &a0.0, &a1.0, condition,
    )?))
  }

  fn to_big_int(self) -> BigInt {
    (&self.0).into()
  }
}

#[cfg(test)]
mod tests {
  use bellpepper_core::test_cs::TestConstraintSystem;

  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;
  type Base = <E as Engine>::Base;

  #[test]
  fn test_alloc() {
    let cases = [Base::ZERO, Base::ONE, Base::ZERO - Base::ONE];
    let mut cs = TestConstraintSystem::<Scalar>::new();
    for (i, base) in cases.into_iter().enumerate() {
      let _base_allocated = AllocatedBase::<E>::alloc(cs.namespace(|| format!("alloc {i}")), base);
    }

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
