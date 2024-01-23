use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::parafold::cycle_fold::AllocatedScalarMulAccumulator;
use crate::parafold::nifs_primary::{AllocatedFoldProof, AllocatedRelaxedR1CSInstance};
use crate::parafold::nivc::{AllocatedNIVCIO, AllocatedNIVCState, AllocatedNIVCUpdateProof};
use crate::parafold::nivc::{NIVCStateInstance, NIVCUpdateProof, NIVCIO};
use crate::traits::Engine;

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

    let pc_in = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_in"), || pc_in);
    let z_in = z_in
      .into_iter()
      .enumerate()
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || z)
      })
      .collect();
    let pc_out = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_out"), || pc_out);
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

  pub fn to_native(&self) -> Result<NIVCIO<F>, SynthesisError> {
    let pc_in = self
      .pc_in
      .get_value()
      .ok_or(SynthesisError::AssignmentMissing)?;
    let pc_out = self
      .pc_out
      .get_value()
      .ok_or(SynthesisError::AssignmentMissing)?;
    let z_in = self
      .z_in
      .iter()
      .map(|z| z.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;
    let z_out = self
      .z_out
      .iter()
      .map(|z| z.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;

    Ok(NIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    })
  }
}

impl<E1, E2> AllocatedNIVCState<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FI>(mut cs: CS, state: FI) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FI: FnOnce() -> NIVCStateInstance<E1, E2>,
  {
    let NIVCStateInstance::<E1, E2> {
      hash_input: [h_L, h_R],
      io,
      accs,
      acc_sm,
      ..
    } = state();

    let h_L = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc h_L"), || h_L);
    let h_R = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc h_R"), || h_R);
    let io = AllocatedNIVCIO::alloc_infallible(cs.namespace(|| "alloc io"), || io);
    let accs = accs
      .into_iter()
      .enumerate()
      .map(|(i, acc)| {
        AllocatedRelaxedR1CSInstance::alloc_infallible(
          cs.namespace(|| format!("alloc acc[{i}]")),
          || acc,
        )
      })
      .collect();
    let acc_sm =
      AllocatedScalarMulAccumulator::<E1, E2>::alloc_infallible(cs.namespace(|| "alloc W"), || {
        acc_sm
      });

    Self {
      hash_input: [h_L, h_R],
      io,
      accs,
      acc_sm,
    }
  }

  pub fn to_native(&self) -> Result<NIVCStateInstance<E1, E2>, SynthesisError> {
    let [h_L, h_R] = &self.hash_input;
    let h_L = h_L.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    let h_R = h_R.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    let io = self.io.to_native()?;
    let accs = self
      .accs
      .iter()
      .map(|acc| acc.to_native())
      .collect::<Result<Vec<_>, _>>()?;
    let acc_sm = self.acc_sm.to_native()?;

    Ok(NIVCStateInstance {
      hash_input: [h_L, h_R],
      io,
      accs,
      acc_sm,
    })
  }
}

impl<E1, E2> AllocatedNIVCUpdateProof<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FP>(mut cs: CS, proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> NIVCUpdateProof<E1, E2>,
  {
    let NIVCUpdateProof {
      state,
      index,
      nifs_fold_proof,
    } = proof();

    let state = AllocatedNIVCState::alloc_infallible(cs.namespace(|| "alloc state"), || state);
    let fold_proof =
      AllocatedFoldProof::alloc_infallible(cs.namespace(|| "alloc fold_proof"), || nifs_fold_proof);

    Self {
      state,
      index,
      fold_proof,
    }
  }
}
