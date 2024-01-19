use bellpepper_core::num::AllocatedNum;
use bellpepper_core::ConstraintSystem;

use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::nifs_primary::circuit::{AllocatedFoldProof, AllocatedRelaxedR1CSInstance};
use crate::parafold::nivc::circuit::{
  AllocatedNIVCIO, AllocatedNIVCState, AllocatedNIVCStateProof,
};
use crate::parafold::nivc::prover::{NIVCStateInstance, NIVCStateProof};
use crate::traits::Engine;

impl<E1: Engine, E2: Engine> AllocatedNIVCState<E1, E2> {
  pub fn alloc_infallible<CS, FI>(mut cs: CS, state: FI) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FI: FnOnce() -> NIVCStateInstance<E1, E2>,
  {
    let NIVCStateInstance { io, accs, acc_sm } = state();

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
      AllocatedScalarMulAccumulator::alloc_infallible(cs.namespace(|| "alloc W"), || acc_sm);

    Self { io, accs, acc_sm }
  }
}

impl<E1: Engine, E2: Engine> AllocatedNIVCStateProof<E1, E2> {
  pub fn alloc_infallible<CS, FP>(mut cs: CS, proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> NIVCStateProof<E1, E2>,
  {
    let NIVCStateProof {
      state,
      hash_input,
      index,
      nifs_fold_proof,
    } = proof();

    let state = AllocatedNIVCState::alloc_infallible(cs.namespace(|| "alloc state"), || state);
    let hash_input =
      hash_input.map(|h| AllocatedNum::alloc_infallible(cs.namespace(|| "alloc hash input"), || h));
    let fold_proof =
      AllocatedFoldProof::alloc_infallible(cs.namespace(|| "alloc fold_proof"), || nifs_fold_proof);

    Self {
      state,
      hash_input,
      index,
      fold_proof,
    }
  }
}
