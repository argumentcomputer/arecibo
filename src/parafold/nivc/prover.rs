use ff::PrimeField;

use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs_primary::prover::RelaxedR1CS;
use crate::parafold::nivc::{NIVCMergeProof, NIVCStateInstance, NIVCUpdateProof, NIVCIO};
use crate::parafold::prover::CommitmentKey;
use crate::parafold::transcript::prover::Transcript;
use crate::r1cs::R1CSShape;
use crate::traits::{Engine, ROConstants};

#[derive(Debug)]
pub struct NIVCState<E1: Engine, E2: Engine> {
  accs: Vec<RelaxedR1CS<E1>>,
  acc_sm: ScalarMulAccumulator<E2>,
}

#[derive(Debug)]
pub struct NIVCUpdateWitness<E1: Engine, E2: Engine> {
  state: NIVCStateInstance<E1, E2>,
  index: usize,
  W: Vec<E1::Scalar>,
}

impl<E1, E2> NIVCState<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn update(
    &mut self,
    ck: &CommitmentKey<E1>,
    shapes: &[R1CSShape<E1>],
    hasher: &NIVCHasher<E1>,
    witness_prev: &NIVCUpdateWitness<E1, E2>,
    transcript: &mut Transcript<E1>,
  ) -> NIVCUpdateProof<E1, E2> {
    let Self { accs, acc_sm, .. } = self;

    let NIVCUpdateWitness {
      state: instance_prev,
      index: index_prev,
      W: W_prev,
    } = witness_prev;
    let index_prev = *index_prev;

    let hash_prev = instance_prev.hash(hasher);

    let shape_prev = &shapes[index_prev];

    // Add the R1CS IO to the transcript
    let X_prev = vec![hash_prev];
    for x_prev in &X_prev {
      transcript.absorb(x_prev);
    }

    // Fold the proof for the previous iteration into the correct accumulator
    let nifs_fold_proof = accs[index_prev].fold(ck, shape_prev, X_prev, W_prev, acc_sm, transcript);

    let nivc_fold_proof = NIVCUpdateProof {
      state: instance_prev.clone(),
      index: index_prev,
      nifs_fold_proof,
    };

    nivc_fold_proof
  }

  pub fn merge(
    ck: &CommitmentKey<E1>,
    shapes: &[R1CSShape<E1>],
    hasher: &NIVCHasher<E1>,
    mut self_L: Self,
    mut self_R: Self, // reference?
    witness_L: &NIVCUpdateWitness<E1, E2>,
    witness_R: &NIVCUpdateWitness<E1, E2>,
    transcript: &mut Transcript<E1>,
  ) -> (Self, NIVCMergeProof<E1, E2>) {
    let proof_L = self_L.update(ck, shapes, hasher, witness_L, transcript);
    let proof_R = self_R.update(ck, shapes, hasher, witness_R, transcript);

    let Self {
      accs: accs_L,
      acc_sm: acc_sm_L,
      ..
    } = self_L;
    let Self {
      accs: accs_R,
      acc_sm: acc_sm_R,
      ..
    } = self_R;

    let (mut acc_sm, sm_merge_proof) = ScalarMulAccumulator::merge(acc_sm_L, acc_sm_R, transcript);

    let (accs, nivc_merge_proof) =
      RelaxedR1CS::merge_many(ck, shapes, accs_L, accs_R, &mut acc_sm, transcript);

    let merge_proof = NIVCMergeProof {
      nivc_update_proof_L: proof_L,
      nivc_update_proof_R: proof_R,
      sm_merge_proof,
      nivc_merge_proof,
    };

    let self_next = Self { accs, acc_sm };
    (self_next, merge_proof)
  }
}

impl<E1: Engine, E2: Engine> NIVCStateInstance<E1, E2> {
  /// compute the hash of the state to be passed as public input/output
  fn hash(&self, _hasher: &NIVCHasher<E1>) -> E1::Scalar {
    todo!()
  }
}

pub struct NIVCHasher<E: Engine> {
  ro_consts: ROConstants<E>,
  pp: E::Scalar,
  arity: usize,
}

impl<F: PrimeField> NIVCIO<F> {
  pub fn default(arity: usize) -> Self {
    Self {
      pc_in: F::ZERO,
      z_in: vec![F::default(); arity],
      pc_out: F::ZERO,
      z_out: vec![F::default(); arity],
    }
  }
}
