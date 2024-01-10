use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::zip_eq;

use crate::parafold::circuit::scalar_mul::{AllocatedCommitment, AllocatedScalarMulInstance};
use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::nifs::{FoldProofInstance, RelaxedR1CSInstance};
use crate::traits::Engine;

#[derive(Debug, Clone)]
pub(in parafold) struct AllocatedR1CSInstance<E: Engine> {
  X: Vec<AllocatedNum<E::Scalar>>,
  W: AllocatedCommitment<E>,
}

#[derive(Debug, Clone)]
pub(in parafold) struct AllocatedRelaxedR1CSInstance<E: Engine> {
  u: AllocatedNum<E::Scalar>,
  X: Vec<AllocatedNum<E::Scalar>>,
  W: AllocatedCommitment<E>,
  E: AllocatedCommitment<E>,
}

#[derive(Debug, Clone)]
pub(in parafold) struct AllocatedFoldProofInstance<E: Engine> {
  T: AllocatedCommitment<E>,
}

impl<E: Engine> AllocatedFoldProofInstance<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, fold_proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> FoldProofInstance<E>,
  {
    let FoldProofInstance { T } = fold_proof();
    let T = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc T"), || T);
    Self { T }
  }
}

impl<E: Engine> AllocatedR1CSInstance<E> {
  pub fn new(X: Vec<AllocatedNum<E::Scalar>>, W: AllocatedCommitment<E::Scalar>) -> Self {
    Self { X, W }
  }
  // pub fn alloc_infallible<CS, F>(mut cs: CS, instance: F) -> Self
  // where
  //   CS: ConstraintSystem<E::Scalar>,
  //   F: FnOnce() -> R1CSInstance<E>,
  // {
  //   let R1CSInstance { io, W } = instance();
  //
  //   let io = AllocatedNIVCState::alloc_infallible(cs.namespace(|| "alloc io"), || io);
  //   let W = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
  //
  //   Self { io, W }
  // }
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

  pub fn fold<CS>(
    mut cs: CS,
    acc_curr: Self,
    circuit_new: AllocatedR1CSInstance<E>,
    fold_proof: AllocatedFoldProofInstance<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Self, [AllocatedScalarMulInstance<E>; 2]), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    transcript.absorb(cs.namespace("absorb circuit_new"), &circuit_new)?;
    transcript.absorb(cs.namespace("absorb fold_proofT"), &fold_proof)?;

    let r = transcript.squeeze(cs.namespace("squeeze r"))?;

    let AllocatedR1CSInstance { X: X_new, W: W_new } = circuit_new;
    let Self {
      W: W_curr,
      E: E_curr,
      u: u_curr,
      X: X_curr,
    } = acc_curr;
    let AllocatedFoldProofInstance { T } = fold_proof;

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

    let u_next = u_curr.add(cs.namespace(|| "u_new"), &r)?;

    let X_next = zip_eq(X_curr, X_new)
      .enumerate()
      .map(|(i, (x_curr, x_new))| mul_add(cs.namespace(|| format!("X_new[{i}]")), x_curr, x_new, r))
      .collect::<Result<Vec<_>, _>>()?;

    Ok((
      Self {
        W: W_next,
        E: E_next,
        u: u_next,
        X: X_next,
      },
      [W_next_instance, E_next_instance],
    ))
  }

  pub fn merge<CS>(
    mut cs: CS,
    acc_curr: Self,
    acc_new: Self,
    fold_proof: AllocatedFoldProofInstance<E>,
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
    } = acc_curr;
    let Self {
      u: u_new,
      X: X_new,
      W: W_new,
      E: E_new,
    } = acc_new;
    let AllocatedFoldProofInstance { T } = fold_proof;

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

    let u_next = mul_add(cs.namespace(|| "u_new"), u_curr, u_new, r.clone())?;

    let X_next = zip_eq(X_curr, X_new)
      .enumerate()
      .map(|(i, (x_curr, x_new))| mul_add(cs.namespace(|| format!("X_new[{i}]")), x_curr, x_new, r))
      .collect::<Result<Vec<_>, _>>()?;

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

  //   pub fn fold_many<CS>(
  //     mut cs: CS,
  //     mut accs_curr: Vec<Self>,
  //     circuit_new: AllocatedR1CSInstance<E>,
  //     fold_proof: AllocatedFoldProofInstance<E>,
  //     transcript: &mut AllocatedTranscript<E>,
  //   ) -> Result<
  //     (
  //       Vec<Self>,
  //       // AllocatedNIVCState<E::Scalar>,
  //       [AllocatedScalarMulInstance<E>; 2],
  //     ),
  //     SynthesisError,
  //   >
  //   where
  //     CS: ConstraintSystem<E::Scalar>,
  //   {
  //     let _index = circuit_new.io.program_counter();
  //
  //     // let selector = AllocatedSelector::new(index, accs_curr.len());
  //     // let acc_curr = selector.get(accs)
  //     let acc_curr = accs_curr[0].clone();
  //     // let (acc_next, nivc_state_next, scalar_mul_instances) = Self::fold(
  //     let (acc_next, scalar_mul_instances) = Self::fold(
  //       cs.namespace(|| "fold_many"),
  //       acc_curr,
  //       circuit_new,
  //       fold_proof,
  //       transcript,
  //     )?;
  //
  //     // let accs_next = selector.update(acc_curr);
  //     accs_curr[0] = acc_next;
  //     Ok((accs_curr, nivc_state_next, scalar_mul_instances))
  //   }
}

fn mul_add<F, CS>(
  mut cs: CS,
  a: AllocatedNum<F>,
  b: AllocatedNum<F>,
  r: AllocatedNum<F>,
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
    |lc| lc - a.get_variable() + c.get_variable(),
  );
  Ok(c)
}
