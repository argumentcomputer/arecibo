use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::Boolean;
use itertools::{chain, zip_eq};
use neptune::circuit2::Elt;

use crate::constants::NUM_CHALLENGE_BITS;
use crate::parafold::cycle_fold::gadgets::emulated::AllocatedBase;
use crate::parafold::cycle_fold::gadgets::secondary_commitment::AllocatedSecondaryCommitment;
use crate::parafold::cycle_fold::nifs::NUM_IO_SECONDARY;
use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CSInstance;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::CurveCycleEquipped;

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryRelaxedR1CSInstance<E: CurveCycleEquipped> {
  pub u: AllocatedBase<E>,
  pub X: Vec<AllocatedBase<E>>,
  pub W: AllocatedSecondaryCommitment<E>,
  pub E: AllocatedSecondaryCommitment<E>,
}

impl<E: CurveCycleEquipped> AllocatedSecondaryRelaxedR1CSInstance<E> {
  pub fn fold<CS>(
    &mut self,
    mut cs: CS,
    X_new: [AllocatedBase<E>; NUM_IO_SECONDARY],
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let W_new = transcript.read_commitment_secondary(cs.namespace(|| "transcript W_new"))?;
    let T = transcript.read_commitment_secondary(cs.namespace(|| "transcript T"))?;

    // Get challenge `r` but truncate the bits for more efficient scalar multiplication
    let r_bits = transcript.squeeze_bits(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;

    let r = AllocatedBase::from_bits_le(CS::one(), &r_bits);

    let Self {
      u: u_curr,
      X: X_curr,
      W: W_curr,
      E: E_curr,
    } = self;

    // We have to do a full modular reduction since merging will make `u` full-sized
    let u_next = u_curr.add(cs.namespace(|| "u_next = u_curr + r % q"), &r)?;
    let X_next = zip_eq(X_curr, X_new)
      .enumerate()
      .map(|(i, (x_curr, x_new))| {
        x_curr.lc(
          cs.namespace(|| format!("(x_curr[{i}] + (x_new[{i}] * r)) % q")),
          &r,
          &x_new,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    // Scalar multiplications
    let W_next = W_curr.lc(cs.namespace(|| "W_curr + r * W_new"), &r_bits, &W_new)?;
    let E_next = E_curr.lc(cs.namespace(|| "E_curr + r * T"), &r_bits, &T)?;

    *self = Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    };

    Ok(())
  }

  // pub fn merge<CS>(
  //   mut cs: CS,
  //   self_L: Self,
  //   self_R: Self,
  //   transcript: &mut AllocatedTranscript<E>,
  // ) -> Result<Self, SynthesisError>
  // where
  //   CS: ConstraintSystem<E::Scalar>,
  // {
  //   // Allocate T from transcript
  //   let T = AllocatedPoint::<<E::Secondary as Engine>::GE>::alloc_transcript(
  //     cs.namespace(|| "alloc T"),
  //     transcript,
  //   );
  //
  //   // Get truncated challenge
  //   let r_bits = transcript.squeeze_bits(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
  //   let r = BaseParams::base_from_bits(CS::one(), &r_bits);
  //
  //   let Self {
  //     u: u_L,
  //     X: X_L,
  //     W: W_L,
  //     E: E_L,
  //   } = self_L;
  //   let Self {
  //     u: u_R,
  //     X: X_R,
  //     W: W_R,
  //     E: E_R,
  //   } = self_R;
  //
  //   let u_next = u_R
  //     .mul(&mut cs.namespace(|| "u_R * r"), &r)?
  //     .add(&mut cs.namespace(|| "(u_R * r) + u_L"), &u_L)?
  //     .reduce(&mut cs.namespace(|| "((u_R * r) + u_L) % q"))?;
  //   let X_next = zip_eq(X_L, X_R)
  //     .enumerate()
  //     .map(|(i, (x_L, x_R))| {
  //       x_R
  //         .mul(&mut cs.namespace(|| "x_R * r"), &r)?
  //         .add(&mut cs.namespace(|| "(x_R * r) + x_L"), &x_L)?
  //         .reduce(&mut cs.namespace(|| "((x_R * r) + x_L) % q"))
  //     })
  //     .collect::<Result<Vec<_>, _>>()?;
  //
  //   let W_next = W_R
  //     .scalar_mul(cs.namespace(|| "r * W_R"), &r_bits)?
  //     .add(cs.namespace(|| "W_L + r * W_R"), &W_L)?;
  //   let E_next = {
  //     let E_tmp = E_R
  //       .scalar_mul(cs.namespace(|| "r * E_R"), &r_bits)?
  //       .add(cs.namespace(|| "T + r * E_R"), &T)?;
  //     E_tmp
  //       .scalar_mul(cs.namespace(|| "r * E_tmp"), &r_bits)?
  //       .add(cs.namespace(|| "E_L + r * E_tmp"), &E_L)?
  //   };
  //
  //   Ok(Self {
  //     u: u_next,
  //     X: X_next,
  //     W: W_next,
  //     E: E_next,
  //   })
  // }

  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &Boolean)
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    self
      .u
      .enforce_zero(cs.namespace(|| "enforce u = 0"), is_trivial);
    for (i, x) in self.X.iter().enumerate() {
      x.enforce_zero(cs.namespace(|| format!("enforce X[{i}] = 0")), is_trivial);
    }
    self
      .W
      .enforce_trivial(cs.namespace(|| "enforce trivial W"), is_trivial);
    self
      .E
      .enforce_trivial(cs.namespace(|| "enforce trivial E"), is_trivial);
  }

  /// Allocate and add the result to the transcript
  pub fn alloc_unchecked<CS>(mut cs: CS, instance: RelaxedSecondaryR1CSInstance<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let u = AllocatedBase::alloc_unchecked(cs.namespace(|| "read u"), instance.u);
    let X = instance
      .X
      .into_iter()
      .enumerate()
      .map(|(i, x)| AllocatedBase::alloc_unchecked(cs.namespace(|| format!("read x[{i}]")), x))
      .collect();
    let W =
      AllocatedSecondaryCommitment::<E>::alloc_unchecked(cs.namespace(|| "read W"), instance.W);
    let E =
      AllocatedSecondaryCommitment::<E>::alloc_unchecked(cs.namespace(|| "read E"), instance.E);
    Self { u, X, W, E }
  }

  pub fn select_default<CS>(self, mut cs: CS, is_default: &Boolean) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let zero = AllocatedBase::<E>::zero();
    let u = AllocatedBase::conditionally_select(
      &mut cs.namespace(|| "select u"),
      &self.u,
      &zero,
      is_default,
    )?;
    let X = self
      .X
      .iter()
      .enumerate()
      .map(|(i, x)| {
        AllocatedBase::conditionally_select(
          &mut cs.namespace(|| format!("select X[{i}]")),
          &x,
          &zero,
          is_default,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    let W = self
      .W
      .select_default(cs.namespace(|| "select W"), is_default)?;
    let E = self
      .E
      .select_default(cs.namespace(|| "select E"), is_default)?;
    Ok(Self { u, X, W, E })
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> + '_ {
    chain![
      self.u.as_preimage(),
      self.X.iter().map(|x| x.as_preimage()).flatten(),
      self.W.as_preimage(),
      self.E.as_preimage()
    ]
  }

  #[allow(unused)]
  pub fn eq_native(&self, other: &RelaxedSecondaryR1CSInstance<E>) -> Option<bool> {
    if !self.u.eq_native(&other.u) {
      return Some(false);
    };

    for (x, x_expected) in zip_eq(&self.X, &other.X) {
      if !x.eq_native(x_expected) {
        return Some(false);
      }
    }

    if !self.W.eq_native(&other.W)? {
      return Some(false);
    };
    if !self.E.eq_native(&other.E)? {
      return Some(false);
    };

    return Some(true);
  }
}
