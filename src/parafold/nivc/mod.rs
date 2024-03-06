use bellpepper_core::num::AllocatedNum;
use ff::Field;
use neptune::generic_array::typenum::U16;
use neptune::poseidon::PoseidonConstants;

use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CSInstance;
use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::transcript::{TranscriptConstants, TranscriptElement};
use crate::parafold::transcript::prover::Transcript;
use crate::traits::{CurveCycleEquipped, Engine};

pub mod circuit;
pub mod prover;

/// The input and output of a NIVC computation over one or more steps.
///
/// # Note
/// - An IO result is trivial if {pc, z}_in == {pc, z}_out
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NIVCIO<E: CurveCycleEquipped> {
  pc_in: E::Scalar,
  z_in: Vec<E::Scalar>,
  pc_out: E::Scalar,
  z_out: Vec<E::Scalar>,
}

/// The input and output of a NIVC computation over one or more steps.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCIO<E: CurveCycleEquipped> {
  pc_in: AllocatedNum<E::Scalar>,
  z_in: Vec<AllocatedNum<E::Scalar>>,
  pc_out: AllocatedNum<E::Scalar>,
  z_out: Vec<AllocatedNum<E::Scalar>>,
}

type NIVCPoseidonConstants<E> = PoseidonConstants<<E as Engine>::Scalar, U16>;

/// Succinct representation of the recursive NIVC state that is known
#[derive(Clone, Debug, PartialEq)]
pub struct NIVCStateInstance<E: CurveCycleEquipped> {
  io: NIVCIO<E>,
  accs: Vec<RelaxedR1CSInstance<E>>,
  acc_cf: RelaxedSecondaryR1CSInstance<E>,
}

/// A proof for loading a previous NIVC output inside a circuit.
#[derive(Debug, Clone)]
pub struct NIVCUpdateProof<E: CurveCycleEquipped> {
  transcript_prev: E::Scalar,
  transcript_buffer: Vec<TranscriptElement<E>>,

  state: NIVCStateInstance<E>,

  acc_prev: RelaxedR1CSInstance<E>,
  index_prev: Option<usize>,
}

impl<E: CurveCycleEquipped> NIVCUpdateProof<E> {
  pub fn dummy(
    ro_consts: TranscriptConstants<E::Scalar>,
    arity: usize,
    num_circuit: usize,
  ) -> Self {
    let state = NIVCStateInstance::<E>::dummy(arity, num_circuit);

    let state_hash: E::Scalar = E::Scalar::ZERO;
    let transcript_init: E::Scalar = E::Scalar::ZERO;

    let mut transcript = Transcript::new(ro_consts.clone(), [state_hash, transcript_init]);

    let mut acc_sm = ScalarMulAccumulator::dummy();
    RelaxedR1CS::simulate_fold(&mut acc_sm, &mut transcript);
    let _ = acc_sm.simulate_finalize(&mut transcript);

    let (_, transcript_buffer) = transcript.seal();

    Self {
      transcript_prev: transcript_init,
      transcript_buffer,
      state,
      acc_prev: RelaxedR1CSInstance::dummy(),
      index_prev: None,
    }
  }
}

// #[derive(Debug, Clone)]
// pub struct NIVCMergeProof<E: CurveCycleEquipped> {
//   transcript_buffer: Vec<E::Scalar>,
//   accs_L: Vec<RelaxedR1CSInstance<E>>,
//   accs_R: Vec<RelaxedR1CSInstance<E>>,
// }

#[cfg(test)]
mod tests {
  use bellpepper_core::ConstraintSystem;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use itertools::zip_eq;

  use crate::parafold::nivc::circuit::AllocatedNIVCState;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;

  type CS = TestConstraintSystem<Scalar>;

  #[test]
  fn test_from_proof() {
    let mut cs = CS::new();

    let ro_consts = TranscriptConstants::<Scalar>::new();
    let dummy_proof = NIVCUpdateProof::<E>::dummy(ro_consts.clone(), 4, 4);

    let _state =
      AllocatedNIVCState::from_proof(cs.namespace(|| "from proof"), &ro_consts, dummy_proof)
        .unwrap();

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_hash() {
    let mut cs = CS::new();

    let state = NIVCStateInstance::<E>::dummy(4, 4);
    let allocated_state =
      AllocatedNIVCState::<E>::alloc_unchecked(cs.namespace(|| "alloc state"), state.clone());

    let state_hash = state.hash();
    let allocated_state_hash = allocated_state.hash(cs.namespace(|| "hash")).unwrap();

    let state_field = state
      .as_preimage()
      .into_iter()
      .map(|x| x.to_field())
      .flatten()
      .collect::<Vec<_>>();
    let allocated_state_field = allocated_state
      .as_preimage()
      .into_iter()
      .enumerate()
      .map(|(i, x)| {
        x.ensure_allocated(&mut cs.namespace(|| format!("alloc x[{i}]")), true)
          .unwrap()
      })
      .collect::<Vec<_>>();

    assert_eq!(state_field.len(), allocated_state_field.len());

    for (_i, (x, allocated_x)) in zip_eq(&state_field, &allocated_state_field).enumerate() {
      assert_eq!(*x, allocated_x.get_value().unwrap());
    }

    assert_eq!(state_hash, allocated_state_hash.get_value().unwrap());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
