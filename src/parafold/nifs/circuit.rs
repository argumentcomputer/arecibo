use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::{AllocatedNum, Num};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_emulated::util::alloc_num_equals_constant;
use ff::{Field, PrimeField};
use itertools::*;

use crate::gadgets::utils::{alloc_zero, conditionally_select};
use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::gadgets::primary_commitment::AllocatedPrimaryCommitment;
use crate::parafold::hash::{AllocatedHashWriter, AllocatedHasher};
use crate::parafold::nifs::{PrimaryR1CSConstants, RelaxedR1CSInstance};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::CurveCycleEquipped;

/// Allocated [RelaxedR1CSInstance] for a circuit over the primary curve.
#[derive(Debug, Clone)]
pub struct AllocatedRelaxedR1CSInstance<E: CurveCycleEquipped> {
  pp: AllocatedNum<E::Scalar>,
  u: AllocatedNum<E::Scalar>,
  X: AllocatedNum<E::Scalar>,
  W: AllocatedPrimaryCommitment<E>,
  E: AllocatedPrimaryCommitment<E>,
}

impl<E: CurveCycleEquipped> AllocatedRelaxedR1CSInstance<E> {
  /// Folds an R1CSInstance into `self`
  pub fn fold<CS>(
    &mut self,
    mut cs: CS,
    X_new: &AllocatedNum<E::Scalar>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E>,
    transcript: &mut AllocatedTranscript<E>,
    is_trivial: &Boolean,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let W_new = transcript.read_commitment_primary(cs.namespace(|| "transcript W_new"))?;
    let T = transcript.read_commitment_primary(cs.namespace(|| "transcript T"))?;

    let r = transcript.squeeze(&mut cs.namespace(|| "squeeze r"))?;
    let zero = alloc_zero(cs.namespace(|| "alloc zero"));
    let r = conditionally_select(cs.namespace(|| "trivial => r = 0"), &zero, &r, is_trivial)?;
    let r_bits = r.to_bits_le(cs.namespace(|| "r_bits"))?;

    let Self {
      u: u_curr,
      X: X_curr,
      W: W_curr,
      E: E_curr,
      ..
    } = self;

    // Linear combination of acc with new
    self.u = u_curr.add(cs.namespace(|| "u_new"), &r)?;
    self.X = mul_add(cs.namespace(|| "X_next"), X_curr, X_new, &r)?;
    // W_next = W_curr + r * W_new
    self.W = acc_sm.scalar_mul(
      cs.namespace(|| "W_next"),
      W_curr.clone(),
      W_new.clone(),
      r_bits.clone(),
      transcript,
    )?;
    self.E = acc_sm.scalar_mul(
      cs.namespace(|| "E_next"),
      E_curr.clone(),
      T.clone(),
      r_bits,
      transcript,
    )?;
    Ok(())
  }

  /// Optimized merge over the primary curve, where the same `r` is used across many accumulators.
  pub fn merge_many<CS>(
    mut cs: CS,
    accs_L: Vec<Self>,
    accs_R: Vec<Self>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Vec<Self>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    assert_eq!(accs_L.len(), accs_R.len());

    // Add all cross-term commitments to the transcript.
    let Ts = (0..accs_L.len())
      .map(|i| transcript.read_commitment_primary(cs.namespace(|| format!("transcript T[{i}]"))))
      .collect::<Result<Vec<_>, _>>()?;

    // Get common challenge
    let r = transcript.squeeze(cs.namespace(|| "squeeze r"))?;
    let r_bits = r.to_bits_le(cs.namespace(|| "r_bits"))?;

    // Merge all accumulators
    zip_eq(accs_L, accs_R)
      .zip_eq(Ts)
      .enumerate()
      .map(|(i, ((acc_L, acc_R), T))| {
        let mut cs = cs.namespace(|| format!("merge {i}"));
        cs.enforce(
          || "pp_L = pp_R",
          |lc| lc,
          |lc| lc,
          |lc| lc + acc_L.pp.get_variable() - acc_R.pp.get_variable(),
        );

        let u_next = mul_add(cs.namespace(|| "u_next"), &acc_L.u, &acc_R.u, &r)?;
        let X_next = mul_add(cs.namespace(|| "X_next"), &acc_L.X, &acc_R.X, &r)?;
        let W_next = acc_sm.scalar_mul(
          cs.namespace(|| "W_next"),
          acc_L.W.clone(),
          acc_R.W.clone(),
          r_bits.clone(),
          transcript,
        )?;
        let E1_next = acc_sm.scalar_mul(
          cs.namespace(|| "E1_next"),
          T,
          acc_R.E.clone(),
          r_bits.clone(),
          transcript,
        )?;
        let E_next = acc_sm.scalar_mul(
          cs.namespace(|| "E_next"),
          acc_L.E.clone(),
          E1_next.clone(),
          r_bits.clone(),
          transcript,
        )?;

        Ok::<Self, SynthesisError>(Self {
          pp: acc_L.pp,
          u: u_next,
          X: X_next,
          W: W_next,
          E: E_next,
        })
      })
      .collect::<Result<Vec<_>, _>>()
  }

  pub fn alloc<CS>(mut cs: CS, instance: &RelaxedR1CSInstance<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let pp = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pp"), || instance.pp);
    let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || instance.u);
    let X = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc X"), || instance.X);

    let W = AllocatedPrimaryCommitment::alloc(cs.namespace(|| "alloc W"), instance.W);
    let E = AllocatedPrimaryCommitment::alloc(cs.namespace(|| "alloc E"), instance.E);

    Self { pp, u, X, W, E }
  }

  pub fn alloc_from_hash<CS>(
    mut cs: CS,
    hash: &AllocatedNum<E::Scalar>,
    instance: &RelaxedR1CSInstance<E>,
    constants: &PrimaryR1CSConstants<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let acc = Self::alloc(cs.namespace(|| "alloc"), instance);

    let hash_is_zero: Boolean = alloc_num_equals_constant(
      cs.namespace(|| "hash_is_zero"),
      &Num::from(hash.clone()),
      E::Scalar::ZERO,
    )?
    .into();

    acc.enforce_trivial(
      cs.namespace(|| "hash_is_zero => acc.is_trivial"),
      &hash_is_zero,
    )?;

    let acc_hash = acc.hash(cs.namespace(|| "acc_hash"), constants)?;

    // cs.enforce(
    //   || "(hash = 0) OR (hash = acc_hash)",
    //   |lc| lc + hash.get_variable(),
    //   |lc| lc + hash.get_variable() - acc_hash.get_variable(),
    //   |lc| lc,
    // );

    cs.enforce(
      || "!hash_is_zero => (hash = acc_hash)",
      |_| hash_is_zero.not().lc(CS::one(), E::Scalar::ZERO),
      |lc| lc + hash.get_variable() - acc_hash.get_variable(),
      |lc| lc,
    );

    Ok(acc)
  }

  #[allow(unused)]
  pub fn enforce_trivial<CS: ConstraintSystem<E::Scalar>>(
    &self,
    mut cs: CS,
    is_default: &Boolean,
  ) -> Result<(), SynthesisError> {
    cs.enforce(
      || "is_default => u = 0",
      |_| is_default.lc(CS::one(), E::Scalar::ONE),
      |lc| lc + self.u.get_variable(),
      |lc| lc,
    );
    cs.enforce(
      || "is_default => X = 0",
      |_| is_default.lc(CS::one(), E::Scalar::ONE),
      |lc| lc + self.X.get_variable(),
      |lc| lc,
    );
    self
      .W
      .enforce_trivial(cs.namespace(|| "is_default => W = id"), is_default)?;
    self
      .E
      .enforce_trivial(cs.namespace(|| "is_default => E = id"), is_default)?;
    Ok(())
  }
}

impl<E: CurveCycleEquipped> AllocatedHashWriter<E::Scalar> for AllocatedRelaxedR1CSInstance<E> {
  fn write<H: AllocatedHasher<E::Scalar>>(&self, hasher: &mut H) {
    self.pp.write(hasher);
    self.u.write(hasher);
    self.X.write(hasher);
    self.W.write(hasher);
    self.E.write(hasher);
  }
}

fn mul_add<F, CS>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
  r: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError>
where
  F: PrimeField,
  CS: ConstraintSystem<F>,
{
  let c = AllocatedNum::alloc(cs.namespace(|| "alloc c"), || {
    let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    let b_val = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    let r_val = r.get_value().ok_or(SynthesisError::AssignmentMissing)?;

    Ok(a_val + r_val * b_val)
  })?;

  cs.enforce(
    || "c = a + r * b",
    |lc| lc + r.get_variable(),
    |lc| lc + b.get_variable(),
    |lc| lc + c.get_variable() - a.get_variable(),
  );
  Ok(c)
}
