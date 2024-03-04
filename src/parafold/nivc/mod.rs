use bellpepper_core::num::AllocatedNum;
use ff::Field;
use neptune::generic_array::typenum::U24;
use neptune::poseidon::PoseidonConstants;

use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CSInstance;
use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::{TranscriptConstants, TranscriptElement};
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

type NIVCPoseidonConstants<E> = PoseidonConstants<<E as Engine>::Scalar, U24>;

/// Succinct representation of the recursive NIVC state that is known
#[derive(Clone, Debug)]
pub struct NIVCStateInstance<E: CurveCycleEquipped> {
  transcript_state: E::Scalar,
  io: NIVCIO<E>,
  accs_hash: Vec<E::Scalar>,
  acc_cf: RelaxedSecondaryR1CSInstance<E>,
}

/// A proof for loading a previous NIVC output inside a circuit.
#[derive(Debug, Clone)]
pub struct NIVCUpdateProof<E: CurveCycleEquipped> {
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
    let state_instance = NIVCStateInstance::<E>::dummy(arity, num_circuit);

    let state_hash = E::Scalar::ZERO;

    let mut transcript = Transcript::new(ro_consts.clone(), [state_hash]);

    let mut acc_sm = ScalarMulAccumulator::dummy();
    RelaxedR1CS::simulate_fold(&mut acc_sm, &mut transcript);
    let _ = acc_sm.simulate_finalize(&mut transcript);

    let (_, transcript_buffer) = transcript.seal();
    Self {
      transcript_buffer,
      state: state_instance,
      acc_prev: RelaxedR1CSInstance::default(),
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
  use crate::parafold::nivc::circuit::AllocatedNIVCState;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use bellpepper_core::ConstraintSystem;

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
}
