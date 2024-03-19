use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use itertools::{enumerate, zip_eq};

use crate::constants::NUM_CHALLENGE_BITS;
use crate::parafold::gadgets::emulated::AllocatedBase;
use crate::parafold::gadgets::secondary_commitment::AllocatedSecondaryCommitment;
use crate::parafold::hash::{AllocatedHashWriter, AllocatedHasher};
use crate::parafold::nifs_secondary::{RelaxedSecondaryR1CSInstance, NUM_IO_SECONDARY};
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

  pub fn merge<CS>(
    mut cs: CS,
    self_L: Self,
    self_R: Self,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // Allocate T from transcript
    let T = transcript.read_commitment_secondary(cs.namespace(|| "transcript T"))?;

    // Get truncated challenge
    let r_bits = transcript.squeeze_bits(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
    let r = AllocatedBase::from_bits_le(CS::one(), &r_bits);

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

    let u_next = u_L.lc(&mut cs.namespace(|| "u_L + r * u_R % q"), &r, &u_R)?;
    let X_next = zip_eq(X_L, X_R)
      .enumerate()
      .map(|(i, (x_L, x_R))| {
        x_L.lc(
          &mut cs.namespace(|| format!("X_L[{i}] + r * x_R[{i}] % q")),
          &r,
          &x_R,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    let W_next = W_L.lc(cs.namespace(|| "W_L + r * W_R"), &r_bits, &W_R)?;
    let E_tmp = T.lc(cs.namespace(|| "T + r * E_R"), &r_bits, &E_R)?;
    let E_next = E_L.lc(cs.namespace(|| "E_L + r * E_tmp"), &r_bits, &E_tmp)?;

    Ok(Self {
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    })
  }

  /// Allocate and add the result to the transcript
  pub fn alloc_unchecked<CS>(mut cs: CS, instance: &RelaxedSecondaryR1CSInstance<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let u = AllocatedBase::alloc_unchecked(cs.namespace(|| "read u"), instance.u);
    let X = enumerate(&instance.X)
      .map(|(i, x)| AllocatedBase::alloc_unchecked(cs.namespace(|| format!("read x[{i}]")), *x))
      .collect();
    let W =
      AllocatedSecondaryCommitment::<E>::alloc_unchecked(cs.namespace(|| "read W"), instance.W);
    let E =
      AllocatedSecondaryCommitment::<E>::alloc_unchecked(cs.namespace(|| "read E"), instance.E);
    Self { u, X, W, E }
  }

  pub fn select_default<CS>(&self, mut cs: CS, is_default: &Boolean) -> Result<Self, SynthesisError>
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
    let X = enumerate(&self.X)
      .map(|(i, x)| {
        let cs = &mut cs.namespace(|| format!("select X[{i}]"));
        AllocatedBase::conditionally_select(cs, x, &zero, is_default)
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

  pub fn get_value(&self) -> Option<RelaxedSecondaryR1CSInstance<E>> {
    let u = self.u.get_value();
    let X = self.X.iter().map(|x| x.get_value()).collect();
    let W = self.W.get_value()?;
    let E = self.E.get_value()?;
    Some(RelaxedSecondaryR1CSInstance { u, X, W, E })
  }
}

impl<E: CurveCycleEquipped> AllocatedHashWriter<E::Scalar>
  for AllocatedSecondaryRelaxedR1CSInstance<E>
{
  fn write<H: AllocatedHasher<E::Scalar>>(&self, hasher: &mut H) {
    self.u.write(hasher);
    self.X.write(hasher);
    self.W.write(hasher);
    self.E.write(hasher);
  }
}
