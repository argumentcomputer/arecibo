use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::{chain, zip_eq};
use pairing::Engine;

use crate::parafold::circuit::nifs::{
  AllocatedFoldProofInstance, AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance,
};
use crate::parafold::circuit::scalar_mul::{AllocatedCommitment, AllocatedScalarMulInstance};
use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::nivc::NIVCIO;
use crate::zip_with;

#[derive(Debug, Clone)]
pub struct AllocatedNIVCState<E: Engine> {
  io: AllocatedNIVCIO<E::Scalar>,
  accs: Vec<AllocatedRelaxedR1CSInstance<E>>,
}

#[derive(Debug, Clone)]
pub struct AllocatedNIVCStep<E: Engine> {
  io: AllocatedNIVCIO<E::Scalar>,
  W: AllocatedCommitment<E>,
}

#[derive(Debug, Clone)]
pub(crate) struct AllocatedNIVCIO<F: PrimeField> {
  pc_in: AllocatedNum<F>,
  z_in: Vec<AllocatedNum<F>>,
  pc_out: AllocatedNum<F>,
  z_out: Vec<AllocatedNum<F>>,
}

impl<E: Engine> AllocatedNIVCState<E> {
  pub fn fold<CS>(
    mut cs: CS,
    nivc_curr: Self,
    nivc_new: AllocatedNIVCStep<E>,
    fold_proof: AllocatedFoldProofInstance<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Self, [AllocatedScalarMulInstance<E>; 2]), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let Self {
      io: io_curr,
      accs: mut accs_curr,
    } = nivc_curr;
    let AllocatedNIVCStep {
      io: io_new,
      W: W_new,
    } = nivc_new;

    let circuit_new = AllocatedR1CSInstance::new(io_new.X(), W_new);

    // TODO: Use selector
    // let index = io_new.program_counter();
    // let selector = AllocatedSelector::new(index, accs_curr.len());
    // let acc_curr = selector.get(accs)
    let acc_curr = accs_curr[0].clone();

    let (acc_next, scalar_mul_instances) = AllocatedRelaxedR1CSInstance::fold(
      cs.namespace(|| "fold"),
      acc_curr,
      circuit_new,
      fold_proof,
      transcript,
    )?;

    // let accs_next = selector.update(acc_curr);
    let accs_next = accs_curr.clone();
    accs_next[0] = acc_next;

    let io_next = io_curr.merge(cs.namespace(|| "merge io"), io_new)?;

    Ok((Self { io: io_next, accs }, scalar_mul_instances))
  }

  pub fn merge<CS>(
    mut cs: CS,
    nivc_L: Self,
    nivc_R: Self,
    fold_proofs: Vec<AllocatedFoldProofInstance<E>>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Self, Vec<AllocatedScalarMulInstance<E>>), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let Self {
      io: io_L,
      accs: mut accs_L,
    } = nivc_L;
    let Self {
      io: io_R,
      accs: accs_R,
    } = nivc_R;

    let num_accs = fold_proofs.len();
    assert_eq!(accs_L.len(), num_accs);
    assert_eq!(accs_R.len(), num_accs);

    let mut all_scalar_mul_instances = Vec::with_capacity(2 * num_accs);

    let accs_next = zip_with!((accs_L, accs_R, fold_proofs), |acc_L, acc_R, fold_proof| {
      let (acc_next, scalar_mul_instances) = AllocatedRelaxedR1CSInstance::merge(
        cs.namespace(|| "fold"),
        acc_L,
        acc_R,
        fold_proof,
        transcript,
      )?;

      all_scalar_mul_instances.extend(scalar_mul_instances);

      Ok(acc_next)
    })
    .collect::<Result<Vec<_>, _>>()?;

    let io_next = io_L.merge(cs.namespace(|| "merge io"), io_R)?;

    Ok((
      Self {
        io: io_next,
        accs: accs_next,
      },
      all_scalar_mul_instances,
    ))
  }
}

impl<F: PrimeField> AllocatedNIVCIO<F> {
  pub fn alloc_infallible<CS, N>(mut cs: CS, state: N) -> Self
  where
    CS: ConstraintSystem<F>,
    N: FnOnce() -> NIVCIO<F>,
  {
    let NIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    } = state();

    let pc_in =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_in"), || F::from(pc_in as u64));
    let z_in = z_in
      .into_iter()
      .enumerate()
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || z)
      })
      .collect();
    let pc_out =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_out"), || F::from(pc_out as u64));
    let z_out = z_out
      .into_iter()
      .enumerate()
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_out[{i}]")), || z)
      })
      .collect();

    Self {
      pc_in,
      z_in,
      pc_out,
      z_out,
    }
  }

  pub fn merge<CS>(self, mut cs: CS, other: Self) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    // self.pc_out = other.pc_in
    cs.enforce(
      || "self.pc_out = other.pc_in",
      |lc| lc,
      |lc| lc,
      |lc| self.pc_out.get_variable() - other.pc_in.get_variable(),
    );

    // self.z_out = other.z_in
    zip_eq(&self.z_out, &other.z_in)
      .enumerate()
      .for_each(|(i, (z_L_i, z_R_i))| {
        cs.enforce(
          || format!("self.z_out[{i}] = other.z_in[{i}]"),
          |lc| lc,
          |lc| lc,
          |lc| z_L_i.get_variable() - z_R_i.get_variable(),
        );
      });

    Ok(Self {
      pc_in: self.pc_in,
      z_in: self.z_in,
      pc_out: other.pc_out,
      z_out: other.z_out,
    })
  }

  pub fn X(&self) -> Vec<AllocatedNum<F>> {
    let AllocatedNIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    } = self;

    chain!([pc_in], z_in.iter(), [pc_out], z_out.iter())
      .cloned()
      .collect()
  }

  pub fn program_counter(&self) -> AllocatedNum<F> {
    self.pc_in.clone()
  }
}
