use ff::PrimeField;

use crate::parafold::nifs::{FoldProof, MergeProof, RelaxedR1CS, RelaxedR1CSInstance, R1CS};
use crate::parafold::prover::cyclefold::{
  ScalarMulAccumulator, ScalarMulAccumulatorInstance, ScalarMulMergeProof,
};
use crate::provider::pedersen::Commitment;
use crate::r1cs::R1CSShape;
use crate::traits::{Engine, ROConstants};
use crate::CommitmentKey;

#[derive(Debug, Clone)]
pub struct NIVCIO<F: PrimeField> {
  pc_in: usize,
  z_in: Vec<F>,
  pc_out: usize,
  z_out: Vec<F>,
}

#[derive(Debug)]
pub struct NIVCState<E: Engine> {
  io: NIVCIO<E::Scalar>,
  accs: Vec<RelaxedR1CS<E>>,
  acc_sm: ScalarMulAccumulator<E>,
}

#[derive(Debug)]
pub struct NIVCStateInstance<E: Engine> {
  io: NIVCIO<E::Scalar>,
  accs: Vec<RelaxedR1CSInstance<E>>,
  acc_sm: ScalarMulAccumulatorInstance<E>,
}

pub struct NIVCStateUpdateProof<E: Engine> {
  index: usize,
  hash_input: [E::Scalar; 2],
  W: Vec<E::Scalar>,
  W_comm: Commitment<E>,
}

pub struct NIVCStateProof<E: Engine> {
  state: NIVCStateInstance<E>,
  hash_input: [E::Scalar; 2],
  W: Commitment<E>,
  index: usize,
  nifs_fold_proof: FoldProof<E>,
}

pub struct NIVCMergeProof<E: Engine> {
  sm_merge_proof: ScalarMulMergeProof<E>,
  nivc_merge_proof: Vec<MergeProof<E>>,
}

impl<E: Engine> NIVCState<E> {
  pub fn update(
    mut self,
    ck: &CommitmentKey<E>,
    hasher: &NIVCHasher<E>,
    shapes: &[R1CSShape<E>],
    proof: NIVCStateProof<E>,
    transcript: &mut E::TE,
  ) -> (Self, NIVCStateProof<E>) {
    let self_instance_curr = self.instance();
    let hash_curr = self_instance_curr.hash(hasher);

    let NIVCState { io, accs, acc_sm } = self;

    let NIVCStateUpdateProof {
      index,
      hash_input,
      W,
      W_comm,
    } = proof;

    let [hash_init, hash_prev] = &hash_input;
    let X = vec![*hash_init, *hash_prev, hash_curr];

    let circuit_new = R1CS::new(X, W_comm.clone(), W);

    let shape_new = &shapes[index];
    // TODO: remove clone
    let acc = accs[index].clone();

    let (acc_curr, acc_sm, nifs_fold_proof) =
      acc.fold(ck, shape_new, &circuit_new, acc_sm, transcript);

    accs[index] = acc_curr;

    let self_next = Self { io, accs, acc_sm };

    let nivc_fold_proof = NIVCStateProof {
      state: self_instance_curr,
      hash_input,
      W: W_comm,
      index,
      nifs_fold_proof,
    };

    (self_next, nivc_fold_proof)
  }

  fn merge(
    mut self,
    other: Self,
    ck: &CommitmentKey<E>,
    shapes: &[R1CSShape<E>],
    transcript: &mut E::TE,
  ) -> (Self, NIVCMergeProof<E>) {
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

  fn instance(&self) -> NIVCStateInstance<E> {
    NIVCStateInstance {
      io: self.io.clone(),
      accs: self.accs.iter().map(|acc| acc.instance().clone()).collect(),
      acc_sm: self.acc_sm.instance(),
    }
  }
}

impl<E: Engine> NIVCStateInstance<E> {
  /// compute the hash of the state to be passed as public input/output
  fn hash(&self, _hasher: &NIVCHasher<E>) -> E::Scalar {
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
