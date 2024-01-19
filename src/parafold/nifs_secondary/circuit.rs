use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::zip_eq;
use num_bigint::BigInt;
use num_traits::Num as numTraitsNum;

use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS};
use crate::gadgets::nonnative::bignat::BigNat;
use crate::gadgets::nonnative::util::Num;
use crate::gadgets::utils::{alloc_bignat_constant, le_bits_to_num};
use crate::parafold::ecc::AllocatedPoint;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::Engine;

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryRelaxedR1CSInstance<E2: Engine> {
  u: BigNat<E2::Base>,
  X: Vec<BigNat<E2::Base>>,
  W: AllocatedPoint<E2::Base, E2::GE>,
  E: AllocatedPoint<E2::Base, E2::GE>,
}

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryFoldProof<E2: Engine> {
  W: AllocatedPoint<E2::Base, E2::GE>,
  T: AllocatedPoint<E2::Base, E2::GE>,
}

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryMergeProof<E2: Engine> {
  T: AllocatedPoint<E2::Base, E2::GE>,
}

impl<E2: Engine> AllocatedSecondaryRelaxedR1CSInstance<E2> {
  pub fn fold<CS, E1>(
    self,
    mut cs: CS,
    X_new: Vec<BigNat<E1::Scalar>>,
    fold_proof: AllocatedSecondaryFoldProof<E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    E1: Engine<Scalar = E2::Base>,
    CS: ConstraintSystem<E1::Scalar>,
  {
    // Allocate the order of the non-native field as a constant
    let q_bn = alloc_bignat_constant(
      cs.namespace(|| "alloc G::Base::modulus"),
      &BigInt::from_str_radix(E2::Scalar::MODULUS, 16).unwrap(),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;

    let AllocatedSecondaryFoldProof { W: W_new, T } = fold_proof;
    transcript.absorb(&W_new);
    transcript.absorb(&T);

    let r_bits = transcript.squeeze_bits(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
    let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;
    let r_bn = BigNat::from_num(
      cs.namespace(|| "allocate r_bn"),
      &Num::from(r),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    let Self {
      u: u_curr,
      X: X_curr,
      W: W_curr,
      E: E_curr,
    } = self;

    let u_next = u_curr
      .add(&r_bn)?
      .red_mod(cs.namespace(|| "u_next = u_curr + r % q"), &q_bn)?;
    let X_next = zip_eq(X_curr, X_new)
      .enumerate()
      .map(|(i, (x_curr_bn, x_new_bn))| {
        add_mul_bn(
          cs.namespace(|| format!("x_next[{i}]")),
          &x_curr_bn,
          &x_new_bn,
          &r_bn,
          &q_bn,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    let W_next = W_new
      .scalar_mul(cs.namespace(|| "r * W_new"), &r_bits)?
      .add(cs.namespace(|| "W_curr + r * W_new"), &W_curr)?;
    let E_next = T
      .scalar_mul(cs.namespace(|| "r * T"), &r_bits)?
      .add(cs.namespace(|| "W_curr + r * T"), &E_curr)?;

    Ok(Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    })
  }
  pub fn merge<CS, E1>(
    self,
    mut cs: CS,
    other: Self,
    merge_proof: AllocatedSecondaryMergeProof<E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    E1: Engine<Scalar = E2::Base>,
    CS: ConstraintSystem<E1::Scalar>,
  {
    // Allocate the order of the non-native field as a constant
    let q_bn = alloc_bignat_constant(
      cs.namespace(|| "alloc G::Base::modulus"),
      &BigInt::from_str_radix(E2::Scalar::MODULUS, 16).unwrap(),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;

    let AllocatedSecondaryMergeProof { T } = merge_proof;
    transcript.absorb(&T);

    let r_bits = transcript.squeeze_bits(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
    let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;
    let r_bn = BigNat::from_num(
      cs.namespace(|| "allocate r_bn"),
      &Num::from(r),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;

    let Self {
      u: u_L,
      X: X_L,
      W: W_L,
      E: E_L,
    } = self;
    let Self {
      u: u_R,
      X: X_R,
      W: W_R,
      E: E_R,
    } = other;

    let u_next = add_mul_bn(cs.namespace(|| "u_next"), &u_L, &u_R, &r_bn, &q_bn)?;
    let X_next = zip_eq(X_L, X_R)
      .enumerate()
      .map(|(i, (x_L_bn, x_R_bn))| {
        add_mul_bn(
          cs.namespace(|| format!("x_next[{i}]")),
          &x_L_bn,
          &x_R_bn,
          &r_bn,
          &q_bn,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    let W_next = W_R
      .scalar_mul(cs.namespace(|| "r * W_R"), &r_bits)?
      .add(cs.namespace(|| "W_L + r * W_R"), &W_L)?;
    let E_next = {
      let E_tmp = E_R
        .scalar_mul(cs.namespace(|| "r * E_R"), &r_bits)?
        .add(cs.namespace(|| "T + r * E_R"), &T)?;
      E_tmp
        .scalar_mul(cs.namespace(|| "r * E_tmp"), &r_bits)?
        .add(cs.namespace(|| "E_L + r * E_tmp"), &E_L)?
    };

    Ok(Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    })
  }
}

fn add_mul_bn<F, CS>(
  mut cs: CS,
  a: &BigNat<F>,
  b: &BigNat<F>,
  r: &BigNat<F>,
  q: &BigNat<F>,
) -> Result<BigNat<F>, SynthesisError>
where
  F: PrimeField,
  CS: ConstraintSystem<F>,
{
  // tmp = r * b
  let (_, tmp) = b.mult_mod(cs.namespace(|| "r * b"), b, r)?;
  // tmp += a
  // tmp = a + r * b;
  let tmp = tmp.add(a)?;
  // tmp %= q
  tmp.red_mod(cs.namespace(|| "a + r * b % q"), q)
}
