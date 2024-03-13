use std::marker::PhantomData;
use std::ops::BitAnd;

use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::Num;
use bellpepper_core::{ConstraintSystem, SynthesisError, Variable};
use bellpepper_emulated::field_element::{
  EmulatedFieldElement, EmulatedFieldParams, EmulatedLimbs,
};
use bellpepper_emulated::util::bigint_to_scalar;
use ff::{Field, PrimeField, PrimeFieldBits};
use itertools::{zip_eq, Itertools};
use num_bigint::{BigInt, Sign};
use num_traits::{Num as num_Num, One, Zero};

use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS};
use crate::parafold::hash::{AllocatedHashWriter, AllocatedHasher};
use crate::traits::CurveCycleEquipped;

#[derive(Debug, Clone)]
/// Explicit parameters for performing base-field arithmetic in a circuit defined over the scalar field.
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
    false
  }
}

#[derive(Debug, Clone)]
/// Allocated base field element, represented as a non-native field element.
pub struct AllocatedBase<E: CurveCycleEquipped> {
  value: E::Base,
  element: EmulatedFieldElement<E::Scalar, BaseParams<E>>,
}

impl<E: CurveCycleEquipped> AllocatedBase<E> {
  pub fn zero() -> Self {
    Self {
      value: E::Base::ZERO,
      element: EmulatedFieldElement::zero(),
    }
  }

  fn alloc_limbs<CS: ConstraintSystem<E::Scalar>>(
    mut cs: CS,
    value: E::Base,
    limbs: Vec<E::Scalar>,
  ) -> Self {
    let element = EmulatedFieldElement::new_internal_element(EmulatedLimbs::Constant(limbs), 0)
      .allocate_field_element_unchecked(&mut cs.namespace(|| "alloc unchecked"))
      .unwrap();
    Self { value, element }
  }

  pub fn from_bits_le(one: Variable, bits: &[Boolean]) -> Self {
    let limb_bases =
      std::iter::successors(Some(E::Scalar::ONE), |base: &E::Scalar| Some(base.double()))
        .take(BaseParams::<E>::bits_per_limb())
        .collect::<Vec<_>>();

    assert!(bits.len() <= E::Base::NUM_BITS as usize);

    let limbs = bits
      .chunks(BaseParams::<E>::bits_per_limb())
      .map(|limb_bits| {
        let limb_bases = limb_bases.iter().take(limb_bits.len());

        zip_eq(limb_bases, limb_bits).fold(Num::<E::Scalar>::zero(), |num, (base, bit)| {
          num.add_bool_with_coeff(one, bit, *base)
        })
      })
      .collect::<Vec<_>>();

    let value = bits.iter().rev().fold(E::Base::ZERO, |v: E::Base, limb| {
      v.double() + E::Base::from(limb.get_value().unwrap_or_default() as u64)
    });

    assert!(limbs.len() <= BaseParams::<E>::num_limbs());

    Self {
      value,
      element: EmulatedFieldElement::new_internal_element(EmulatedLimbs::Allocated(limbs), 0),
    }
  }

  pub fn alloc<CS: ConstraintSystem<E::Scalar>>(mut cs: CS, base: &E::Base) -> Self {
    let base_bits = base
      .to_le_bits()
      .into_iter()
      .take(E::Base::NUM_BITS as usize)
      .enumerate()
      .map(|(i, bit)| {
        Boolean::from(
          AllocatedBit::alloc(cs.namespace(|| format!("alloc bit {i}")), Some(bit)).unwrap(),
        )
      })
      .collect::<Vec<_>>();
    Self::from_bits_le(CS::one(), &base_bits)
  }

  pub fn alloc_unchecked<CS: ConstraintSystem<E::Scalar>>(cs: CS, base: E::Base) -> Self {
    let limbs = BaseParams::<E>::base_to_limbs(&base);
    Self::alloc_limbs(cs, base, limbs)
  }

  pub fn add<CS: ConstraintSystem<E::Scalar>>(
    &self,
    mut cs: CS,
    other: &Self,
  ) -> Result<Self, SynthesisError> {
    let value = self.value + other.value;
    let element = self
      .element
      .add(&mut cs.namespace(|| "add"), &other.element)?;
    let element = element.reduce(&mut cs.namespace(|| "reduce"))?;
    Ok(Self { value, element })
  }

  pub fn lc<CS: ConstraintSystem<E::Scalar>>(
    &self,
    mut cs: CS,
    scalar: &Self,
    other: &Self,
  ) -> Result<Self, SynthesisError> {
    let value = self.value + scalar.value * other.value;
    let element = other
      .element
      .mul(&mut cs.namespace(|| "mul"), &scalar.element)?;
    let element = element.add(&mut cs.namespace(|| "add"), &self.element)?;
    let element = element.reduce(&mut cs.namespace(|| "reduce"))?;
    Ok(Self { value, element })
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
    let value = if condition.get_value().unwrap_or_default() {
      a1.value
    } else {
      a0.value
    };
    let element =
      EmulatedFieldElement::conditionally_select(&mut cs, &a0.element, &a1.element, condition)?;
    Ok(Self { value, element })
  }

  pub fn to_big_int(&self) -> BigInt {
    (&self.element).into()
  }

  // fn alloc_big_int<CS: ConstraintSystem<E::Scalar>>(mut cs: CS, value: BigInt) -> Self {
  //   let limbs = BaseParams::<E>::big_int_to_limbs(value);
  //   let limbs = limbs
  //     .into_iter()
  //     .enumerate()
  //     .map(|(i, limb)| {
  //       Num::from(AllocatedNum::alloc_infallible(
  //         cs.namespace(|| format!("alloc limb {i}")),
  //         || limb,
  //       ))
  //     })
  //     .collect::<Vec<_>>();
  //   Self(EmulatedFieldElement::new_internal_element(
  //     EmulatedLimbs::Allocated(limbs),
  //     0,
  //   ))
  // }

  pub fn get_value(&self) -> Option<E::Base> {
    debug_assert_eq!(field_to_big_int(&self.value), self.to_big_int());
    Some(self.value)
  }
}

impl<E: CurveCycleEquipped> AllocatedHashWriter<E::Scalar> for AllocatedBase<E> {
  fn write<H: AllocatedHasher<E::Scalar>>(&self, hasher: &mut H) {
    let limbs = self
      .element
      .compact_limbs(
        BaseParams::<E>::num_limbs(),
        BaseParams::<E>::bits_per_limb(),
      )
      .unwrap();

    if let EmulatedLimbs::Allocated(limbs) = limbs {
      for limb in limbs
        .into_iter()
        .pad_using(BaseParams::<E>::num_limbs(), |_| Num::zero())
      {
        limb.write(hasher);
      }
    } else {
      unreachable!()
    };
  }
}

impl<E: CurveCycleEquipped> BaseParams<E> {
  pub fn base_to_limbs(base: &E::Base) -> Vec<E::Scalar> {
    Self::big_int_to_limbs(field_to_big_int(base))
  }

  fn big_int_to_limbs(mut base: BigInt) -> Vec<E::Scalar> {
    let num_bits = Self::bits_per_limb() as u32;
    let num_limbs = Self::num_limbs() as u32;
    let mask = BigInt::from(2).pow(num_bits) - BigInt::one();

    let limbs = (0..num_limbs)
      .map(|_| {
        let limb = base.clone().bitand(&mask);
        base >>= num_bits;
        bigint_to_scalar::<E::Scalar>(&limb)
      })
      .collect();
    assert!(
      base.is_zero(),
      "input must be at most {} bits",
      num_bits * num_limbs
    );
    limbs
  }
}

pub fn field_to_big_int<F: PrimeField>(f: &F) -> BigInt {
  let repr = f.to_repr();
  BigInt::from_bytes_le(Sign::Plus, repr.as_ref())
}

#[cfg(test)]
mod tests {
  use bellpepper_core::boolean::AllocatedBit;
  use bellpepper_core::num::AllocatedNum;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use expect_test::expect;
  use num_traits::Zero;
  use rand_chacha::ChaCha20Rng;
  use rand_core::SeedableRng;

  use crate::constants::NUM_CHALLENGE_BITS;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;
  type Base = <E as Engine>::Base;
  // type P = BaseParams<E>;
  type CS = TestConstraintSystem<Scalar>;

  fn check_eq<F: PrimeField>(expected: &F, actual: &AllocatedBase<E>) {
    let value = actual.to_big_int();
    let expected = field_to_big_int(expected);
    assert_eq!(value, expected);
  }

  #[test]
  fn test_alloc() {
    let cases = [Base::ZERO, Base::ONE, Base::ZERO - Base::ONE];
    let mut cs = CS::new();
    for (i, base) in cases.iter().enumerate() {
      let base_allocated = AllocatedBase::<E>::alloc(cs.namespace(|| format!("alloc {i}")), base);
      check_eq(base, &base_allocated);
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
    for (i, scalar) in cases.iter().enumerate() {
      let scalar_allocated =
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc scalar {i}")), || *scalar);
      let scalar_bits = scalar_allocated
        .to_bits_le_strict(cs.namespace(|| format!("to_bits {i}")))
        .unwrap();
      let scalar_base = AllocatedBase::<E>::from_bits_le(CS::one(), &scalar_bits);
      check_eq(scalar, &scalar_base);
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
    let c = a + b;

    let mut cs = CS::new();

    let result_expected =
      AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "result_expected"), c);

    let a = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "a"), a);
    let b = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "b"), b);
    let result = a.add(cs.namespace(|| "result"), &b).unwrap();

    assert_eq!(result.to_big_int(), result_expected.to_big_int());
    assert!(cs.is_satisfied());
    expect!["450"].assert_eq(&cs.num_constraints().to_string());
    expect!["460"].assert_eq(&cs.scalar_aux().len().to_string());
  }

  #[test]
  fn test_lc() {
    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    let a = Base::random(&mut rng);
    let b = Base::random(&mut rng);
    let r = Base::random(&mut rng);
    let result = a + r * b;

    let mut cs = CS::new();

    let a = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "a"), a);
    let b = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "b"), b);
    let r = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "r"), r);
    let c = a.lc(cs.namespace(|| "c"), &r, &b).unwrap();

    let c_expected = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "result"), result);

    assert_eq!(c.to_big_int(), c_expected.to_big_int());
    assert!(cs.is_satisfied());
    expect!["723"].assert_eq(&cs.num_constraints().to_string());
    expect!["737"].assert_eq(&cs.scalar_aux().len().to_string());
  }

  // #[test]
  // fn test_lc_overflow() {
  //   let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
  //
  //   let a = Base::random(&mut rng);
  //   let b = Base::random(&mut rng);
  //   let r = Base::random(&mut rng);
  //   let result = a + r * b;
  //
  //   // Add a multiple of the modulus while staying in the limb bounds
  //   let b_bi = field_to_big_int(&b) + P::modulus() * BigInt::from(4);
  //
  //   let mut cs = CS::new();
  //
  //   let a = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "a"), &a);
  //   let b = AllocatedBase::<E>::alloc_big_int(cs.namespace(|| "b"), b_bi.clone());
  //   let r = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "r"), &r);
  //   let c = a.lc(cs.namespace(|| "c"), &r, &b).unwrap();
  //
  //   let c_expected = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "result"), &result);
  //
  //   assert_eq!(c.to_big_int(), c_expected.to_big_int());
  //   assert!(cs.is_satisfied());
  //   expect!["723"].assert_eq(&cs.num_constraints().to_string());
  //   expect!["737"].assert_eq(&cs.scalar_aux().len().to_string());
  // }
  //
  // #[test]
  // fn test_alloc_big_int() {
  //   // let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
  //
  //   let a = P::modulus().sub(BigInt::one());
  //
  //   let mut cs = CS::new();
  //
  //   let a_alloc = AllocatedBase::<E>::alloc_big_int(cs.namespace(|| "a"), a.clone());
  //   assert_eq!(a, a_alloc.to_big_int());
  // }
  //
  // #[test]
  // fn test_conversions() {
  //   let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
  //
  //   let mut cs = CS::new();
  //
  //   let base = Base::random(&mut rng);
  //   let base_big_int = field_to_big_int(&base);
  //   let base_limbs = P::base_to_limbs(&base);
  //
  //   let alloc_base_big_int =
  //     AllocatedBase::<E>::alloc_big_int(cs.namespace(|| "big int"), base_big_int.clone());
  //   let alloc_base_limbs = AllocatedBase::<E>::alloc_limbs(cs.namespace(|| "limbs"), base_limbs);
  //
  //   assert_eq!(alloc_base_big_int.to_big_int(), base_big_int);
  //   assert_eq!(alloc_base_limbs.to_big_int(), base_big_int);
  //
  //   assert!(cs.is_satisfied());
  // }
}
