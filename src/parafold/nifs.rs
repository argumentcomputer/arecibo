use ff::Field;
use itertools::zip_eq;
use rayon::prelude::*;

use crate::parafold::nivc::NIVCState;
use crate::parafold::prover::cyclefold::ScalarMulInstance;
use crate::r1cs::R1CSShape;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::{Engine, TranscriptEngineTrait};
use crate::{Commitment, CommitmentKey};

/// A full R1CS accumulator for a circuit
pub struct R1CS<E: Engine> {
  instance: R1CSInstance<E>,
  W: Vec<E::Scalar>,
}

/// Instance of an R1CS accumulator for a circuit
#[derive(Clone)]
pub struct R1CSInstance<E: Engine> {
  // TODO: This could be an arbitrary PCD IO
  io: NIVCState<E::Scalar>,
  W: Commitment<E>,
}

/// A full Relaxed-R1CS accumulator for a circuit
pub struct RelaxedR1CS<E: Engine> {
  instance: RelaxedR1CSInstance<E>,
  W: Vec<E::Scalar>,
  E: Vec<E::Scalar>,
  //   // TODO: store cache for Folding T
}

/// Instance of a Relaxed-R1CS accumulator for a circuit
#[derive(Clone)]
pub struct RelaxedR1CSInstance<E: Engine> {
  u: E::Scalar,
  X: Vec<E::Scalar>,
  W: Commitment<E>,
  E: Commitment<E>,
}

/// 
#[derive(Clone)]
pub struct FoldProof<E: Engine> {
  instance: FoldProofInstance<E>,
  T: Vec<E::Scalar>,
}

/// A Nova proof for merging two (Relaxed-)R1CS instances over the primary curve.
#[derive(Clone)]
pub struct FoldProofInstance<E: Engine> {
  T: Commitment<E>,
}

impl<E: Engine> RelaxedR1CS<E> {
  pub fn default(shape: &R1CSShape<E>) -> Self {
    Self {
      instance: RelaxedR1CSInstance::default(shape),
      W: vec![E::Scalar::ZERO; shape.num_vars],
      E: vec![E::Scalar::ZERO; shape.num_cons],
    }
  }

  /// Fold the proof for the previous state transition, producing an accumulator for the current state,
  /// and a proof to be consumed by the verifier.
  pub fn fold(
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    mut acc_curr: Self,
    circuit_new: &R1CS<E>,
    transcript: &mut E::TE,
  ) -> (
    Self,
    NIVCState<E::Scalar>,
    FoldProof<E>,
    [ScalarMulInstance<E>; 2],
  ) {
    transcript.absorb(b"circuit_new", &circuit_new);

    let fold_proof = acc_curr.prove(ck, shape, &circuit_new);
    transcript.absorb(b"fold_proof", &fold_proof);
    let r = transcript.squeeze(b"r").unwrap();

    let (acc_next, nivc_state_next, scalar_mul_instances) =
      Self::combine(acc_curr, &circuit_new, &fold_proof, r, transcript);
    (acc_next, nivc_state_next, fold_proof, scalar_mul_instances)
  }

  pub fn fold_many(
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    mut accs: Vec<Option<Self>>,
    circuit_new: &R1CS<E>,
    transcript: &mut E::TE,
  ) -> (
    Vec<Option<Self>>,
    NIVCState<E::Scalar>,
    FoldProof<E>,
    [ScalarMulInstance<E>; 2],
  ) {
    let index = circuit_new.instance.io.program_counter();
    let acc_curr = accs[index].unwrap_or_else(|| Self::default(shape));
    let (acc_next, nivc_state_next, fold_proof, scalar_mul_instances) =
      Self::fold(ck, shape, acc_curr, circuit_new, transcript);
    accs[index] = Some(acc_next);
    (accs, nivc_state_next, fold_proof, scalar_mul_instances)
  }

  fn combine(
    mut acc_curr: Self,
    circuit_new: &R1CS<E>,
    fold_proof: &FoldProof<E>,
    r: E::Scalar,
    transcript: &mut E::TE,
  ) -> (Self, NIVCState<E::Scalar>, [ScalarMulInstance<E>; 2]) {
    let R1CS {
      instance: instance_new,
      W: W_new,
    } = circuit_new;

    let Self {
      instance: instance_curr,
      W: W_curr,
      E: E_curr,
    } = acc_curr;

    let W_next = zip_eq(W_curr.into_par_iter(), W_new.par_iter())
      .map(|(w_curr, w_new)| w_curr + r * w_new)
      .collect::<Vec<_>>();
    let E_next = zip_eq(E_curr.into_par_iter(), fold_proof.T.par_iter())
      .map(|(e_curr, e_new)| e_curr + r * e_new)
      .collect::<Vec<_>>();

    let (instance_next, nivc_state_next, scalar_mul_instances) = RelaxedR1CSInstance::combine(
      instance_curr,
      instance_new,
      &fold_proof.instance,
      r,
      transcript,
    );

    let acc_next = Self {
      instance: instance_next,
      W: W_next,
      E: E_next,
    };
    (acc_next, nivc_state_next, scalar_mul_instances)
  }

  fn prove<E: Engine>(
    self: &mut RelaxedR1CS<E>,
    _ck: &CommitmentKey<E>,
    _shape: &R1CSShape<E>,
    _witness_new: &R1CS<E>,
  ) -> FoldProof<E> {
    // let T_comm = CE::<E>::commit(ck, &T);
    todo!()
  }
}

impl<E: Engine> RelaxedR1CSInstance<E> {
  fn default(shape: &R1CSShape<E>) -> Self {
    Self {
      u: E::Scalar::ZERO,
      X: vec![E::Scalar::ZERO; shape.num_io],
      W: Commitment::<E>::default(),
      E: Commitment::<E>::default(),
    }
  }

  pub fn fold(
    acc_curr: Self,
    circuit_new: &R1CSInstance<E>,
    fold_proof: &FoldProofInstance<E>,
    transcript: &mut E::TE,
  ) -> (Self, NIVCState<E::Scalar>, [ScalarMulInstance<E>; 2]) {
    transcript.absorb(b"circuit_new", circuit_new);
    transcript.absorb(b"fold_proof", &fold_proof);
    let r = transcript.squeeze(b"r").unwrap();

    Self::combine(acc_curr, &circuit_new, &fold_proof, r, transcript)
  }

  pub fn fold_many(
    mut accs: Vec<Self>,
    circuit_new: &R1CSInstance<E>,
    fold_proof: &FoldProofInstance<E>,
    transcript: &mut E::TE,
  ) -> (Vec<Self>, NIVCState<E::Scalar>, [ScalarMulInstance<E>; 2]) {
    let index = circuit_new.io.program_counter();
    // TODO: Why can't we move?
    let acc_curr = accs[index].clone();
    let (acc_next, nivc_state_next, scalar_mul_instances) =
      Self::fold(acc_curr, circuit_new, fold_proof, transcript);
    accs[index] = acc_next;
    (accs, nivc_state_next, scalar_mul_instances)
  }

  fn combine(
    acc_curr: Self,
    circuit_new: &R1CSInstance<E>,
    fold_proof: &FoldProof<E>,
    r: E::Scalar,
    transcript: &mut E::TE,
  ) -> (Self, NIVCState<E::Scalar>, [ScalarMulInstance<E>; 2]) {
    // Unpack accumulator
    let Self {
      W: W_curr,
      X: X_curr,
      u: u_curr,
      E: E_curr,
    } = acc_curr;

    // Unpack fresh proof
    let R1CSInstance {
      io: io_new,
      W: W_new,
    } = circuit_new;

    // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
    // W_next = W_curr + r * W_new
    let (W_next, W_next_instance) = ScalarMulInstance::new(W_curr, W_new.clone(), r, transcript);
    // E_comm_next = E_comm_curr + r * T
    let (E_next, E_next_instance) =
      ScalarMulInstance::new(E_curr, &fold_proof.T.clone(), r, transcript);

    let X_next = zip_eq(X_curr.into_iter(), io_new.iter())
      .map(|(x_curr, x_new)| x_curr + r * x_new)
      .collect::<Vec<_>>();

    // For relaxed instances, u_new = 1
    let u_next = u_curr + r;

    (
      Self {
        W: W_next,
        X: X_next,
        u: u_next,
        E: E_next,
      },
      io_new.clone(),
      [W_next_instance, E_next_instance],
    )
  }
}

impl<E: Engine> AsRef<R1CSInstance<E>> for R1CS<E> {
  fn as_ref(&self) -> &R1CSInstance<E> {
    &self.instance
  }
}

impl<E: Engine> AsRef<RelaxedR1CSInstance<E>> for RelaxedR1CS<E> {
  fn as_ref(&self) -> &RelaxedR1CSInstance<E> {
    &self.instance
  }
}

impl<E: Engine> AsRef<FoldProofInstance<E>> for FoldProof<E> {
  fn as_ref(&self) -> &FoldProofInstance<E> {
    &self.instance
  }
}
