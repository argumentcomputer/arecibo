use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::num::AllocatedNum;
use ff::PrimeField;
use itertools::*;
use neptune::circuit2::{Elt, poseidon_hash_allocated};

use crate::parafold::cycle_fold::AllocatedPrimaryCommitment;
use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::nifs::{
  PRIMARY_R1CS_INSTANCE_SIZE, R1CSPoseidonConstants, RelaxedR1CSInstance,
};
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
    X_new: AllocatedNum<E::Scalar>,
    acc_sm: &mut AllocatedScalarMulAccumulator<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let W_new = transcript.read_commitment_primary(cs.namespace(|| "transcript W_new"))?;
    let T = transcript.read_commitment_primary(cs.namespace(|| "transcript T"))?;

    let r = transcript.squeeze(&mut cs.namespace(|| "squeeze r"))?;
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
    self.X = mul_add(cs.namespace(|| "X_next"), X_curr, &X_new, &r)?;
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
    if let Some(r) = r.get_value() {
      println!("c mm: {:?}", r);
    }

    // Merge all accumulators
    zip_eq(accs_L.into_iter(), accs_R.into_iter())
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

  /// Compute the hash of the accumulator over the primary curve.  
  pub fn hash<CS>(&self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let elements = self
      .as_preimage()
      .into_iter()
      .enumerate()
      .map(|(i, x)| x.ensure_allocated(&mut cs.namespace(|| format!("alloc {i}")), true))
      .collect::<Result<Vec<_>, _>>()?;
    let constants = R1CSPoseidonConstants::<E>::new_constant_length(PRIMARY_R1CS_INSTANCE_SIZE);
    poseidon_hash_allocated(cs.namespace(|| "hash"), elements, &constants)
  }

  pub fn alloc<CS>(mut cs: CS, instance: &RelaxedR1CSInstance<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let pp = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pp"), || instance.pp);
    let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || instance.u);
    let X = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc X"), || instance.X);

    let W = AllocatedPrimaryCommitment::alloc(cs.namespace(|| "alloc W"), &instance.W);
    let E = AllocatedPrimaryCommitment::alloc(cs.namespace(|| "alloc E"), &instance.E);

    Self { pp, u, X, W, E }
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> {
    chain!(
      [
        Elt::Allocated(self.pp.clone()),
        Elt::Allocated(self.u.clone()),
        Elt::Allocated(self.X.clone()),
      ],
      self.W.as_preimage(),
      self.E.as_preimage()
    )
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
