use std::marker::PhantomData;

use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::Num;
use bellpepper_core::{ConstraintSystem, SynthesisError, Variable};
use bellpepper_emulated::field_element::{
  EmulatedFieldElement, EmulatedFieldParams, EmulatedLimbs, PseudoMersennePrime,
};
use ff::{Field, PrimeField};
use itertools::zip_eq;
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

  pub fn from_bits_le(one: Variable, bits: &[Boolean]) -> Self {
    let num_bits = BaseParams::<E>::bits_per_limb() * BaseParams::<E>::num_limbs();
    let limb_bases =
      std::iter::successors(Some(E::Scalar::ONE), |base: &E::Scalar| Some(base.double()))
        .take(BaseParams::<E>::bits_per_limb())
        .collect::<Vec<_>>();

    assert!(bits.len() <= num_bits);

    let limbs = bits
      .chunks(BaseParams::<E>::bits_per_limb())
      .map(|limb_bits| {
        let limb_bases = limb_bases.iter().take(limb_bits.len());

        zip_eq(limb_bases, limb_bits).fold(Num::<E::Scalar>::zero(), |num, (base, bit)| {
          num.add_bool_with_coeff(one, &bit, base.clone())
        })
      })
      .collect::<Vec<_>>();

    assert!(limbs.len() <= BaseParams::<E>::num_limbs());

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
    let base = field_to_big_int(base);
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

fn field_to_big_int<F: PrimeField>(f: F) -> BigInt {
  BigInt::from_bytes_le(Sign::Plus, f.to_repr().as_ref())
}

#[cfg(test)]
mod tests {
  use bellpepper_core::boolean::AllocatedBit;
  use bellpepper_core::num::AllocatedNum;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use num_traits::Zero;
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;

  use crate::constants::NUM_CHALLENGE_BITS;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;
  type Base = <E as Engine>::Base;
  type CS = TestConstraintSystem<Scalar>;

  fn check_eq<F: PrimeField>(expected: F, actual: AllocatedBase<E>) {
    let value = actual.to_big_int();
    let expected = field_to_big_int(expected);
    assert_eq!(value, expected);
  }

  #[test]
  fn test_alloc() {
    let cases = [Base::ZERO, Base::ONE, Base::ZERO - Base::ONE];
    let mut cs = CS::new();
    for (i, base) in cases.into_iter().enumerate() {
      let base_allocated = AllocatedBase::<E>::alloc(cs.namespace(|| format!("alloc {i}")), base);
      check_eq(base, base_allocated);
    }

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_from_bits() {
    let cases = [Scalar::ZERO, Scalar::ONE, Scalar::ZERO - Scalar::ONE];
    let mut cs = CS::new();
    for (i, scalar) in cases.into_iter().enumerate() {
      let scalar_allocated =
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc scalar {i}")), || scalar);
      let scalar_bits = scalar_allocated
        .to_bits_le_strict(cs.namespace(|| format!("to_bits {i}")))
        .unwrap();
      let scalar_base = AllocatedBase::<E>::from_bits_le(CS::one(), &scalar_bits);
      check_eq(scalar, scalar_base);
    }

    let cases_bits = [
      std::iter::repeat(Boolean::constant(true))
        .take(NUM_CHALLENGE_BITS)
        .collect::<Vec<_>>(),
      std::iter::repeat(Boolean::constant(true))
        .take(NUM_CHALLENGE_BITS - 1)
        .collect::<Vec<_>>(),
      std::iter::repeat(Boolean::constant(true))
        .take(NUM_CHALLENGE_BITS + 1)
        .collect::<Vec<_>>(),
      (0..NUM_CHALLENGE_BITS)
        .map(|i| {
          Boolean::from(
            AllocatedBit::alloc(cs.namespace(|| format!("alloc bit {i}")), Some(true)).unwrap(),
          )
        })
        .collect::<Vec<_>>(),
    ];

    for bits in cases_bits {
      let allocated = AllocatedBase::<E>::from_bits_le(CS::one(), &bits);
      let expected = bits
        .iter()
        .enumerate()
        .fold(BigInt::zero(), |mut acc, (i, bit)| {
          let bit = bit.get_value().unwrap();
          if bit {
            acc |= BigInt::one() << i;
          }
          acc
        });
      assert_eq!(allocated.to_big_int(), expected);
    }

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_add() {
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    let a = Base::random(&mut rng);
    let b = Base::random(&mut rng);

    let mut cs = CS::new();

    let result_expected = AllocatedBase::<E>::alloc(cs.namespace(|| "result_expected"), a + b);

    let a = AllocatedBase::<E>::alloc(cs.namespace(|| "a"), a);
    let b = AllocatedBase::<E>::alloc(cs.namespace(|| "b"), b);
    let result = a.add(cs.namespace(|| "result"), &b).unwrap();

    assert_eq!(result.to_big_int(), result_expected.to_big_int());
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_lc() {
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    let a = Base::random(&mut rng);
    let b = Base::random(&mut rng);
    let result = a + b;

    let mut cs = CS::new();

    let a = AllocatedBase::<E>::alloc(cs.namespace(|| "a"), a);
    let b = AllocatedBase::<E>::alloc(cs.namespace(|| "b"), b);
    let c = a.add(cs.namespace(|| "c"), &b).unwrap();

    let c_expected = AllocatedBase::<E>::alloc(cs.namespace(|| "result"), result);

    assert_eq!(c.to_big_int(), c_expected.to_big_int());
    assert!(cs.is_satisfied());
  }
}
