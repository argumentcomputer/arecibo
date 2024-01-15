use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::zip_eq;

use crate::parafold::circuit::scalar_mul::{AllocatedCommitment, AllocatedScalarMulInstance};
use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::nifs::{FoldProof, RelaxedR1CSInstance};
use crate::traits::Engine;

/// Allocated [R1CSInstance] to be folded into an [AllocatedRelaxedR1CSInstance].
#[derive(Debug, Clone)]
pub(in parafold) struct AllocatedR1CSInstance<'a, E: Engine> {
  X: Vec<&'a AllocatedNum<E::Scalar>>,
  W: AllocatedCommitment<E>,
}

/// Allocated [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub(in parafold) struct AllocatedRelaxedR1CSInstance<E: Engine> {
  u: AllocatedNum<E::Scalar>,
  X: Vec<AllocatedNum<E::Scalar>>,
  W: AllocatedCommitment<E>,
  E: AllocatedCommitment<E>,
}

/// An allocated Nova folding proof, for either folding an [R1CSInstance] or a [RelaxedR1CSInstance] into
/// another [RelaxedR1CSInstance]
#[derive(Debug, Clone)]
pub(in parafold) struct AllocatedProof<E: Engine> {
  T: AllocatedCommitment<E>,
}

impl<E: Engine> AllocatedProof<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, fold_proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> FoldProof<E>,
  {
    let FoldProof { T } = fold_proof();
    let T = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc T"), || T);
    Self { T }
  }
}

impl<'a, E: Engine> AllocatedR1CSInstance<'a, E> {
  pub fn new(X: Vec<&AllocatedNum<E::Scalar>>, W: AllocatedCommitment<E::Scalar>) -> Self {
    Self { X, W }
  }
}

impl<E: Engine> AllocatedRelaxedR1CSInstance<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, instance: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> RelaxedR1CSInstance<E>,
  {
    let RelaxedR1CSInstance { u, X, W, E } = instance();
    let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || u);
    let X = X
      .into_iter()
      .enumerate()
      .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
      .collect();
    let W = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let E = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc E"), || E);

    Self { u, X, W, E }
  }

  /// Folds an R1CSInstance into `self`
  pub fn fold<CS>(
    self,
    mut cs: CS,
    circuit_new: AllocatedR1CSInstance<E>,
    fold_proof: AllocatedProof<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Self, [AllocatedScalarMulInstance<E>; 2]), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    transcript.absorb(cs.namespace("absorb circuit_new"), &circuit_new)?;
    transcript.absorb(cs.namespace("absorb fold_proof"), &fold_proof)?;

    let AllocatedR1CSInstance { X: X_new, W: W_new } = circuit_new;
    let Self {
      W: W_curr,
      E: E_curr,
      u: u_curr,
      X: X_curr,
    } = self;
    let AllocatedProof { T } = fold_proof;

    let r = transcript.squeeze(cs.namespace("squeeze r"))?;

    // Linear combination of acc with new
    let u_next = u_curr.add(cs.namespace(|| "u_next"), &r)?;
    let X_next = zip_eq(X_curr, &X_new)
      .enumerate()
      .map(|(i, (x_curr, x_new))| {
        mul_add(cs.namespace(|| format!("X_next[{i}]")), &x_curr, x_new, &r)
      })
      .collect::<Result<Vec<_>, _>>()?;
    let (W_next, W_next_instance) = AllocatedScalarMulInstance::new(
      cs.namespace(|| "W_next"),
      W_curr.clone(),
      W_new.clone(),
      r.clone(),
      transcript,
    )?;
    let (E_next, E_next_instance) = AllocatedScalarMulInstance::new(
      cs.namespace(|| "E_next"),
      E_curr.clone(),
      T.clone(),
      r.clone(),
      transcript,
    )?;

    Ok((
      Self {
        u: u_next,
        X: X_next,
        W: W_next,
        E: E_next,
      },
      [W_next_instance, E_next_instance],
    ))
  }

  pub fn merge<CS>(
    self,
    mut cs: CS,
    acc_new: &Self,
    fold_proof: AllocatedProof<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Self, [AllocatedScalarMulInstance<E>; 3]), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    transcript.absorb(cs.namespace("absorb acc_new"), &acc_new)?;
    transcript.absorb(cs.namespace("absorb fold_proofT"), &fold_proof)?;

    let r = transcript.squeeze(cs.namespace("squeeze r"))?;

    let Self {
      W: W_curr,
      E: E_curr,
      u: u_curr,
      X: X_curr,
    } = self;
    let Self {
      u: u_new,
      X: X_new,
      W: W_new,
      E: E_new,
    } = acc_new;
    let AllocatedProof { T } = fold_proof;

    let u_next = mul_add(cs.namespace(|| "u_new"), &u_curr, u_new, &r)?;
    let X_next = zip_eq(X_curr, X_new)
      .enumerate()
      .map(|(i, (x_curr, x_new))| {
        mul_add(cs.namespace(|| format!("X_new[{i}]")), &x_curr, x_new, &r)
      })
      .collect::<Result<Vec<_>, _>>()?;
    let (W_next, W_next_instance) = AllocatedScalarMulInstance::new(
      cs.namespace(|| "W_next"),
      W_curr.clone(),
      W_new.clone(),
      r.clone(),
      transcript,
    )?;
    let (E1_next, E1_next_instance) = AllocatedScalarMulInstance::new(
      cs.namespace(|| "E1_next"),
      T.clone(),
      E_new.clone(),
      r.clone(),
      transcript,
    )?;
    let (E_next, E_next_instance) = AllocatedScalarMulInstance::new(
      cs.namespace(|| "E2_next"),
      E_curr.clone(),
      E1_next.clone(),
      r.clone(),
      transcript,
    )?;

    Ok((
      Self {
        W: W_next,
        E: E_next,
        u: u_next,
        X: X_next,
      },
      [W_next_instance, E1_next_instance, E_next_instance],
    ))
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
    let a_val = a.get_value()?;
    let b_val = b.get_value()?;
    let r_val = r.get_value()?;

    a_val + r_val + b_val
  })?;

  cs.enforce(
    || "c = a + r * b",
    |lc| lc + r.get_variable(),
    |lc| lc + b.get_variable(),
    |lc| lc + c.get_variable() - a.get_variable(),
  );
  Ok(c)
}
