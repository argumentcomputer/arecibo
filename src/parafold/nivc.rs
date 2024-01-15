use ff::PrimeField;
use itertools::{chain, Itertools};

use crate::parafold::nifs::{FoldProof, RelaxedR1CS, R1CS};
use crate::parafold::prover::cyclefold::{ScalarMulAccumulator, ScalarMulInstance};
use crate::provider::pedersen::Commitment;
use crate::r1cs::R1CSShape;
use crate::traits::Engine;
use crate::{zip_with, CommitmentKey};

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
  accs: Vec<Option<RelaxedR1CS<E>>>,
  acc_sm: ScalarMulAccumulator<E>,
}

pub struct NIVCStateProof<E: Engine> {
  state: NIVCState<E>,
  hash_input_prev: [E::Scalar; 2],
  W: Vec<E::Scalar>,
  W_comm: Commitment<E>,
  index_prev: usize,
}

#[derive(Debug)]
pub struct NIVCStep<E: Engine> {
  io: NIVCIO<E::Scalar>,
  W: Vec<E::Scalar>,
  W_comm: Commitment<E>,
}

pub struct NIVCFoldProof<E: Engine> {
  W: Commitment<E>,
  T: Commitment<E>,
}

pub struct NIVCMergeProof<E: Engine> {
  Ts: Vec<Commitment<E>>,
}

impl<E: Engine> NIVCState<E> {
  pub fn fold(
    ck: &CommitmentKey<E>,
    shapes: &[R1CSShape<E>],
    mut nivc_curr: Self,
    // TODO: This should be a reference to not release the memory
    nivc_new: NIVCStep<E>,
    transcript: &mut E::TE,
  ) -> (Self, FoldProof<E>, [ScalarMulInstance<E>; 2]) {
    let Self {
      io: io_curr,
      accs: mut accs,
    } = nivc_curr;
    let NIVCStep {
      io: io_new,
      W: W_new,
      W_comm: W_comm_new,
    } = nivc_new;

    let circuit_new = R1CS::new(io_new.X(), W_comm_new, W_new);

    let index = io_new.program_counter();
    let shape = &shapes[index];
    let acc_curr = accs[index].unwrap_or_else(|| RelaxedR1CS::default(shape));

    let (acc_next, fold_proof, scalar_mul_instances) =
      acc_curr.fold(ck, shape, &circuit_new, transcript);

    let io_next = io_curr.merge(io_new);

    accs[index] = Some(acc_next);

    (Self { io: io_next, accs }, fold_proof, scalar_mul_instances)
  }
  //
  // pub fn merge(
  //   ck: &CommitmentKey<E>,
  //   shapes: &[R1CSShape<E>],
  //   mut nivc_curr: Self,
  //   nivc_new: &Self,
  //   transcript: &mut E::TE,
  // ) -> (Self, Vec<FoldProof<E>>, Vec<ScalarMulInstance<E>>) {
  //   let Self {
  //     io: io_curr,
  //     accs: mut accs_curr,
  //   } = nivc_curr;
  //   let Self {
  //     io: io_new,
  //     accs: accs_new,
  //   } = nivc_new;
  //
  //   let io_next = io_curr.merge(io_new.clone());
  //
  //   let (accs_new, merge_proofs, scalar_mul_instances): (Vec<_>, Vec<_>, Vec<_>) =
  //     zip_with!((accs_curr, accs_new, shapes), |acc_curr, acc_new, shape| {
  //       acc_curr.merge(ck, shape, acc_new, transcript)
  //     })
  //     .multiunzip();
  //   let scalar_mul_instances = scalar_mul_instances.into_iter().flatten().collect();
  //
  //   (
  //     Self {
  //       io: io_next,
  //       accs: accs_new,
  //     },
  //     merge_proofs,
  //     scalar_mul_instances,
  //   )
  // }
}

impl<F: PrimeField> NIVCIO<F> {
  pub fn program_counter(&self) -> usize {
    self.pc_in
  }
  pub fn X(&self) -> Vec<F> {
    let Self {
      pc_in,
      z_in,
      pc_out,
      z_out,
    } = self;

    chain!(
      [F::from(*pc_in as u64)],
      z_in.iter().cloned(),
      [F::from(*pc_out as u64)],
      z_out.iter().cloned()
    )
    .collect()
  }

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
