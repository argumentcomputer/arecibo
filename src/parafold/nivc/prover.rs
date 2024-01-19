use ff::PrimeField;

use crate::parafold::cycle_fold::prover::{
  ScalarMulAccumulator, ScalarMulAccumulatorInstance, ScalarMulMergeProof,
};
use crate::parafold::nifs_primary::prover::{
  FoldProof, MergeProof, RelaxedR1CS, RelaxedR1CSInstance,
};
use crate::parafold::prover::CommitmentKey;
use crate::parafold::transcript::prover::Transcript;
use crate::r1cs::R1CSShape;
use crate::traits::{Engine, ROConstants};

#[derive(Debug, Clone)]
pub struct NIVCIO<F> {
  pub pc_in: usize,
  pub z_in: Vec<F>,
  pub pc_out: usize,
  pub z_out: Vec<F>,
}

impl<F: PrimeField> NIVCIO<F> {
  pub fn default(arity: usize) -> Self {
    Self {
      pc_in: 0,
      z_in: vec![F::default(); arity],
      pc_out: 0,
      z_out: vec![F::default(); arity],
    }
  }
}

#[derive(Debug, Clone)]
pub struct NIVCStateProof<E1: Engine, E2: Engine> {
  pub state: NIVCStateInstance<E1, E2>,
  pub hash_input: [E1::Scalar; 2],
  pub index: usize,
  pub nifs_fold_proof: FoldProof<E1, E2>,
}

#[derive(Debug, Clone)]
pub struct NIVCMergeProof<E1: Engine, E2: Engine> {
  sm_merge_proof: ScalarMulMergeProof<E1, E2>,
  nivc_merge_proof: Vec<MergeProof<E1, E2>>,
}

#[derive(Debug, Clone)]
pub struct NIVCStateInstance<E1: Engine, E2: Engine> {
  pub io: NIVCIO<E1::Scalar>,
  pub accs: Vec<RelaxedR1CSInstance<E1>>,
  pub acc_sm: ScalarMulAccumulatorInstance<E1, E2>,
}

#[derive(Debug)]
pub struct NIVCState<E1: Engine, E2: Engine> {
  io: NIVCIO<E1::Scalar>,
  accs: Vec<RelaxedR1CS<E1>>,
  acc_sm: ScalarMulAccumulator<E1, E2>,
}

#[derive(Debug)]
pub struct NIVCStateUpdateProof<E1: Engine> {
  index: usize,
  hash_input: [E1::Scalar; 2],
  W: Vec<E1::Scalar>,
}

impl<E1, E2> NIVCState<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn update(
    self,
    ck: &CommitmentKey<E1>,
    hasher: &NIVCHasher<E1>,
    shapes: &[R1CSShape<E1>],
    proof: NIVCStateUpdateProof<E1>,
    transcript: &mut Transcript<E1>,
  ) -> (Self, NIVCStateProof<E1, E2>)
where {
    let self_instance_curr = self.instance();
    let hash_curr = self_instance_curr.hash(hasher);

    let Self {
      io,
      mut accs,
      acc_sm,
    } = self;

    let NIVCStateUpdateProof {
      index,
      hash_input: [hash_init, hash_prev],
      W: W_curr,
    } = proof;

    let shape_new = &shapes[index];
    // TODO: remove clone
    let acc = accs[index].clone();

    // Add the R1CS IO to the transcript
    let X_curr = vec![hash_init, hash_prev, hash_curr];
    for x_curr in &X_curr {
      transcript.absorb(x_curr);
    }

    // Fold the proof for the previous iteration into the correct accumulator
    let (acc_curr, acc_sm, nifs_fold_proof) =
      acc.fold(ck, shape_new, X_curr, W_curr, acc_sm, transcript);

    accs[index] = acc_curr;

    let self_next = Self { io, accs, acc_sm };

    let nivc_fold_proof = NIVCStateProof {
      state: self_instance_curr,
      hash_input: [hash_init, hash_prev],
      index,
      nifs_fold_proof,
    };

    (self_next, nivc_fold_proof)
  }

  fn merge(
    self,
    other: Self,
    ck: &CommitmentKey<E1>,
    shapes: &[R1CSShape<E1>],
    transcript: &mut Transcript<E1>,
  ) -> (Self, NIVCMergeProof<E1, E2>) {
    let Self {
      io: io_L,
      accs: accs_L,
      acc_sm: acc_sm_L,
    } = self;
    let Self {
      io: io_R,
      accs: accs_R,
      acc_sm: acc_sm_R,
    } = other;

    let (acc_sm_merged, sm_merge_proof) = acc_sm_L.merge(acc_sm_R, transcript);

    let (accs_next, acc_sm_next, nivc_merge_proof) =
      RelaxedR1CS::merge_many(ck, shapes, accs_L, accs_R, acc_sm_merged, transcript);

    let io_next = io_L.merge(io_R);
    let self_next = Self {
      io: io_next,
      accs: accs_next,
      acc_sm: acc_sm_next,
    };
    let merge_proof = NIVCMergeProof {
      sm_merge_proof,
      nivc_merge_proof,
    };
    (self_next, merge_proof)
  }

  fn instance(&self) -> NIVCStateInstance<E1, E2> {
    NIVCStateInstance {
      io: self.io.clone(),
      accs: self.accs.iter().map(|acc| acc.instance().clone()).collect(),
      acc_sm: self.acc_sm.instance(),
    }
  }
}

impl<E1: Engine, E2: Engine> NIVCStateInstance<E1, E2> {
  /// compute the hash of the state to be passed as public input/output
  fn hash(&self, _hasher: &NIVCHasher<E1>) -> E1::Scalar {
    todo!()
  }
}

impl<F: PrimeField> NIVCIO<F> {
  pub fn merge(self, other: Self) -> Self {
    assert_eq!(self.pc_out, other.pc_in);
    assert_eq!(self.z_out, other.z_in);
    Self {
      pc_in: self.pc_in,
      z_in: self.z_in,
      pc_out: other.pc_out,
      z_out: other.z_out,
    }
  }
}

pub struct NIVCHasher<E: Engine> {
  ro_consts: ROConstants<E>,
  pp: E::Scalar,
  arity: usize,
}
