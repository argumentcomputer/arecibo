use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::zip_eq;
use num_bigint::BigInt;
use num_traits::{Num as numTraitsNum, Zero};

use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS};
use crate::gadgets::nonnative::bignat::BigNat;
use crate::gadgets::nonnative::util::Num;
use crate::gadgets::utils::{alloc_bignat_constant, conditionally_select_bignat, le_bits_to_num};
use crate::parafold::ecc::AllocatedPoint;
use crate::parafold::nifs::{FoldProof, MergeProof, RelaxedR1CSInstance};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::Engine;

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryRelaxedR1CSInstance<E1: Engine, E2: Engine> {
  pub u: BigNat<E1::Scalar>,
  pub X: Vec<BigNat<E1::Scalar>>,
  pub W: AllocatedPoint<E1::Scalar, E2::GE>,
  pub E: AllocatedPoint<E1::Scalar, E2::GE>,
  // q: BigNat<E1::Scalar>, // = E2::Base::MODULUS
}

impl<E1, E2> AllocatedSecondaryRelaxedR1CSInstance<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn fold<CS>(
    &mut self,
    mut cs: CS,
    X_new: Vec<BigNat<E1::Scalar>>,
    fold_proof: FoldProof<E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // Allocate the order of the non-native field as a constant
    let q_bn = alloc_bignat_constant(
      cs.namespace(|| "alloc G::Base::modulus"),
      &BigInt::from_str_radix(E2::Scalar::MODULUS, 16).unwrap(),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;

    let FoldProof { W: W_new, T } = fold_proof;

    // Allocate W_new, T and add them to the transcript
    let W_new = AllocatedPoint::alloc_transcript::<_, E1, E2>(
      cs.namespace(|| "alloc W_new"),
      W_new,
      transcript,
    );
    let T =
      AllocatedPoint::alloc_transcript::<_, E1, E2>(cs.namespace(|| "alloc T"), T, transcript);

    // Get challenge `r` but truncate the bits for more efficient scalar multiplication
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

    // We have to do a full modular reduction since merging will make `u` full-sized
    let u_next = u_curr
      .add(&r_bn)?
      .red_mod(cs.namespace(|| "u_next = u_curr + r % q"), &q_bn)?;
    let X_next = zip_eq(X_curr, X_new)
      .enumerate()
      .map(|(i, (x_curr_bn, x_new_bn))| {
        add_mul_bn(
          cs.namespace(|| format!("x_next[{i}]")),
          x_curr_bn,
          &x_new_bn,
          &r_bn,
          &q_bn,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    // Scalar multiplications
    let W_next = W_new
      .scalar_mul(cs.namespace(|| "r * W_new"), &r_bits)?
      .add(cs.namespace(|| "W_curr + r * W_new"), W_curr)?;
    let E_next = T
      .scalar_mul(cs.namespace(|| "r * T"), &r_bits)?
      .add(cs.namespace(|| "W_curr + r * T"), E_curr)?;

    *self = Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    };

    Ok(())
  }
  pub fn merge<CS>(
    mut cs: CS,
    self_L: Self,
    self_R: Self,
    merge_proof: MergeProof<E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // Allocate the order of the non-native field as a constant
    let q_bn = alloc_bignat_constant(
      cs.namespace(|| "alloc G::Base::modulus"),
      &BigInt::from_str_radix(E2::Scalar::MODULUS, 16).unwrap(),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;

    let MergeProof { T } = merge_proof;

    // Allocate T and add to transcript
    let T =
      AllocatedPoint::alloc_transcript::<_, E1, E2>(cs.namespace(|| "alloc T"), T, transcript);
    transcript.absorb(T.as_preimage());

    // Get truncated challenge
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
    } = self_L;
    let Self {
      u: u_R,
      X: X_R,
      W: W_R,
      E: E_R,
    } = self_R;

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

  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &Boolean)
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // TODO: If is_trivial
    // u = 0
    // X = [0, ..., 0]
    self
      .W
      .enforce_trivial(cs.namespace(|| "enforce trivial W"), is_trivial);
    self
      .E
      .enforce_trivial(cs.namespace(|| "enforce trivial E"), is_trivial);
  }

  fn alloc<CS>(/*mut*/ _cs: CS, _instance: RelaxedR1CSInstance<E2>) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // Both u, X need to be allocated as BigInt
    todo!()
    // let SecondaryRelaxedR1CSInstance { u, X, W, E } = instance();
    // let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || u);
    // let X = X
    //   .into_iter()
    //   .enumerate()
    //   .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
    //   .collect();
    // let W = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    // let E = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc E"), || E);
    //
    // Self {
    //   u: BigNat::alloc_from_nat(),
    //   X: vec![],
    //   W: (),
    //   E: (),
    // }
  }

  /// Allocate and add the result to the transcript
  pub fn alloc_transcript<CS>(
    mut cs: CS,
    instance: RelaxedR1CSInstance<E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let instance = Self::alloc(&mut cs, instance);
    transcript.absorb(instance.as_preimage());
    instance
  }

  pub fn select_default<CS>(self, mut cs: CS, is_default: &Boolean) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E2::Base>,
  {
    let bn_zero = alloc_bignat_constant(
      cs.namespace(|| "alloc zero"),
      &BigInt::zero(),
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )?;
    let Self { u, X, W, E } = self;
    let u = conditionally_select_bignat(cs.namespace(|| "select u"), &bn_zero, &u, is_default)?;
    let X = X
      .into_iter()
      .map(|x| conditionally_select_bignat(cs.namespace(|| "select x"), &bn_zero, &x, is_default))
      .collect::<Result<Vec<_>, _>>()?;
    let W = W.select_default(cs.namespace(|| "select W"), is_default)?;
    let E = E.select_default(cs.namespace(|| "select E"), is_default)?;
    Ok(Self { u, X, W, E })
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = AllocatedNum<E1::Scalar>> {
    vec![]
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
