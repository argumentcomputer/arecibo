use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::*;
use neptune::circuit2::{Elt, PoseidonCircuit2};

use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::cycle_fold::AllocatedPrimaryCommitment;
use crate::parafold::nifs::{R1CSPoseidonConstants, RelaxedR1CSInstance};
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
    self,
    mut cs: CS,
    X_new: AllocatedNum<E::Scalar>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let W_new = transcript.read_commitment_primary(cs.namespace(|| "transcript W_new"))?;
    let T = transcript.read_commitment_primary(cs.namespace(|| "transcript T"))?;

    let r = transcript.squeeze(&mut cs.namespace(|| "squeeze r"))?;
    let r_bits = r.to_bits_le(cs.namespace(|| "r_bits"))?;

    let Self {
      pp,
      W: W_curr,
      E: E_curr,
      u: u_curr,
      X: X_curr,
    } = self;

    // Linear combination of acc with new
    let u_next = u_curr.add(cs.namespace(|| "u_next"), &r)?;
    let X_next = mul_add(cs.namespace(|| "X_next"), &X_curr, &X_new, &r)?;
    // W_next = W_curr + r * W_new
    let W_next = acc_sm.scalar_mul(
      cs.namespace(|| "W_next"),
      W_curr.clone(),
      W_new.clone(),
      r_bits.clone(),
      transcript,
    )?;
    let E_next = acc_sm.scalar_mul(
      cs.namespace(|| "E_next"),
      E_curr.clone(),
      T.clone(),
      r_bits,
      transcript,
    )?;

    Ok(Self {
      pp,
      u: u_next,
      X: X_next,
      W: W_next,
      E: E_next,
    })
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
    let accs_next = zip_eq(accs_L, accs_R)
      .zip_eq(Ts)
      .map(|((acc_L, acc_R), T)| {
        let Self {
          pp: pp_L,
          u: u_L,
          X: X_L,
          W: W_L,
          E: E_L,
          ..
        } = acc_L;
        let Self {
          pp: pp_R,
          u: u_R,
          X: X_R,
          W: W_R,
          E: E_R,
          ..
        } = acc_R;

        cs.enforce(
          || "pp_L = pp_R",
          |lc| lc,
          |lc| lc,
          |lc| lc + pp_L.get_variable() - pp_R.get_variable(),
        );

        let u_next = mul_add(cs.namespace(|| "u_new"), &u_L, &u_R, &r)?;
        let X_next = mul_add(cs.namespace(|| "X_new[{i}]"), &X_L, &X_R, &r)?;
        let W_next = acc_sm.scalar_mul(
          cs.namespace(|| "W_next"),
          W_L.clone(),
          W_R.clone(),
          r_bits.clone(),
          transcript,
        )?;
        let E1_next = acc_sm.scalar_mul(
          cs.namespace(|| "E1_next"),
          T.clone(),
          E_R.clone(),
          r_bits.clone(),
          transcript,
        )?;
        let E_next = acc_sm.scalar_mul(
          cs.namespace(|| "E_next"),
          E_L.clone(),
          E1_next.clone(),
          r_bits.clone(),
          transcript,
        )?;

        Ok::<Self, SynthesisError>(Self {
          pp: pp_L,
          u: u_next,
          X: X_next,
          W: W_next,
          E: E_next,
        })
      })
      .collect::<Result<Vec<_>, _>>()?;

    Ok(accs_next)
  }

  /// Compute the hash of the accumulator over the primary curve.  
  pub fn hash<CS>(&self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let constants = R1CSPoseidonConstants::<E>::new();
    let elements = chain!(
      [self.pp.clone(), self.u.clone(), self.X.clone()].map(Elt::Allocated),
      self.W.as_preimage(),
      self.E.as_preimage()
    )
    .collect::<Vec<_>>();
    PoseidonCircuit2::new(elements, &constants).hash_to_allocated(cs.namespace(|| "hash"))
  }

  pub fn alloc<CS>(mut cs: CS, instance: RelaxedR1CSInstance<E>) -> Self
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

    Ok(a_val + r_val + b_val)
  })?;

  cs.enforce(
    || "c = a + r * b",
    |lc| lc + r.get_variable(),
    |lc| lc + b.get_variable(),
    |lc| lc + c.get_variable() - a.get_variable(),
  );
  Ok(c)
}
