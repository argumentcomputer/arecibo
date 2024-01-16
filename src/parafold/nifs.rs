use ff::Field;
use itertools::*;
use rayon::prelude::*;

use crate::parafold::scalar_mul::{ScalarMulAccumulator, ScalarMulFoldProof};
use crate::r1cs::R1CSShape;
use crate::traits::{Engine, TranscriptEngineTrait, TranscriptReprTrait};
use crate::{zip_with, Commitment, CommitmentKey};

/// A full R1CS accumulator for a circuit
#[derive(Debug)]
pub struct R1CS<E: Engine> {
  instance: R1CSInstance<E>,
  // TODO: this could be a reference to a witness vector computed and stored by the application
  // W is not consumed by the fold step, so a reference would avoid dropping the memory
  W: Vec<E::Scalar>,
}

impl<E: Engine> R1CS<E> {
  pub fn new(X: Vec<E::Scalar>, W_comm: Commitment<E>, W: Vec<E::Scalar>) -> Self {
    Self {
      instance: R1CSInstance { X, W: W_comm },
      W,
    }
  }
}

impl<E: Engine> TranscriptReprTrait<E::GE> for &R1CS<E> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    vec![]
  }
}

/// Instance of an R1CS accumulator for a circuit
#[derive(Debug, Clone)]
pub struct R1CSInstance<E: Engine> {
  X: Vec<E::Scalar>,
  W: Commitment<E>,
}

/// A full Relaxed-R1CS accumulator for a circuit
/// FIXME: We should not need to clone this, but required in nivc.rs
#[derive(Debug, Clone)]
pub struct RelaxedR1CS<E: Engine> {
  instance: RelaxedR1CSInstance<E>,
  W: Vec<E::Scalar>,
  E: Vec<E::Scalar>,
  // TODO: store cache for Folding T
}

/// Instance of a Relaxed-R1CS accumulator for a circuit
#[derive(Debug, Clone)]
pub struct RelaxedR1CSInstance<E: Engine> {
  pub u: E::Scalar,
  pub X: Vec<E::Scalar>,
  pub W: Commitment<E>,
  pub E: Commitment<E>,
}

/// A Nova proof for merging two (Relaxed-)R1CS instances over the primary curve.
#[derive(Debug, Clone)]
pub struct FoldProof<E: Engine> {
  pub T: Commitment<E>,
  pub W_sm_proof: ScalarMulFoldProof<E>,
  pub E_sm_proof: ScalarMulFoldProof<E>,
}

#[derive(Debug, Clone)]
pub struct MergeProof<E: Engine> {
  T: Commitment<E>,
  W_sm_proof: ScalarMulFoldProof<E>,
  E1_sm_proof: ScalarMulFoldProof<E>,
  E2_sm_proof: ScalarMulFoldProof<E>,
}

impl<E: Engine> RelaxedR1CS<E> {
  pub fn default(shape: &R1CSShape<E>) -> Self {
    Self {
      instance: RelaxedR1CSInstance::default(shape),
      W: vec![E::Scalar::ZERO; shape.num_vars],
      E: vec![E::Scalar::ZERO; shape.num_cons],
    }
  }

  pub fn instance(&self) -> &RelaxedR1CSInstance<E> {
    &self.instance
  }

  /// Fold the proof for the previous state transition, producing an accumulator for the current state,
  /// and a proof to be consumed by the verifier.
  pub fn fold(
    self,
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    circuit_new: &R1CS<E>,
    mut acc_sm: ScalarMulAccumulator<E>,
    transcript: &mut E::TE,
  ) -> (Self, ScalarMulAccumulator<E>, FoldProof<E>) {
    transcript.absorb(b"circuit_new", &circuit_new);

    let (T, T_comm) =
      self.compute_fold_proof(ck, shape, None, &circuit_new.instance.X, &circuit_new.W);
    transcript.absorb(b"T", &T_comm);
    let r = transcript.squeeze(b"r").unwrap();

    let Self {
      instance: instance_curr,
      W: W_curr,
      E: E_curr,
    } = self;
    let R1CS {
      instance: instance_new,
      W: W_new,
    } = circuit_new;

    let (instance_next, W_sm_proof, E_sm_proof) = {
      // Unpack accumulator
      let RelaxedR1CSInstance {
        u: u_curr,
        X: X_curr,
        W: W_curr,
        E: E_curr,
      } = instance_curr;
      // Unpack fresh proof
      let R1CSInstance { X: X_new, W: W_new } = instance_new;

      // For relaxed instances, u_new = 1
      let u_next = u_curr + r;
      let X_next = zip_eq(X_curr, X_new)
        .map(|(x_curr, x_new)| x_curr + r * x_new)
        .collect::<Vec<_>>();
      // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
      // W_next = W_curr + r * W_new
      let (W_next, W_sm_proof) = acc_sm.scalar_mul(W_curr, *W_new, r, transcript);
      // E_comm_next = E_comm_curr + r * T
      let (E_next, E_sm_proof) = acc_sm.scalar_mul(E_curr, T_comm, r, transcript);

      let instance_next = RelaxedR1CSInstance {
        W: W_next,
        X: X_next,
        u: u_next,
        E: E_next,
      };
      (instance_next, W_sm_proof, E_sm_proof)
    };

    let W_next = zip_with!(
      (W_curr.into_par_iter(), W_new.par_iter()),
      |w_curr, w_new| w_curr + r * w_new
    )
    .collect::<Vec<_>>();
    let E_next = zip_with!(
      (E_curr.into_par_iter(), T.par_iter()),
      |e_curr, e_new| e_curr + r * e_new
    )
    .collect::<Vec<_>>();

    let acc_next = Self {
      instance: instance_next,
      W: W_next,
      E: E_next,
    };

    let fold_proof = FoldProof {
      T: T_comm,
      W_sm_proof,
      E_sm_proof,
    };

    (acc_next, acc_sm, fold_proof)
  }

  /// Fold the proof for the previous state transition, producing an accumulator for the current state,
  /// and a proof to be consumed by the verifier.
  pub fn merge_many(
    ck: &CommitmentKey<E>,
    shapes: &[R1CSShape<E>],
    mut accs_L: Vec<Self>,
    accs_R: Vec<Self>,
    mut acc_sm: ScalarMulAccumulator<E>,
    transcript: &mut E::TE,
  ) -> (Vec<Self>, ScalarMulAccumulator<E>, Vec<MergeProof<E>>) {
    // TODO: parallelize
    let (Ts, T_comms): (Vec<_>, Vec<_>) = zip_with!(
      (accs_L.iter_mut(), accs_R.iter(), shapes),
      |acc_L, acc_R, shape| {
        acc_L.compute_fold_proof(
          ck,
          shape,
          Some(acc_R.instance.u),
          &acc_R.instance.X,
          &acc_R.W,
        )
      }
    )
    .unzip();
    for T_comm in &T_comms {
      transcript.absorb(b"T", T_comm);
    }
    let r = transcript.squeeze(b"r").unwrap();

    let (accs_next, merge_proofs): (Vec<_>, Vec<_>) = zip_with!(
      (
        accs_L.into_iter(),
        accs_R.into_iter(),
        Ts.iter(),
        T_comms.into_iter()
      ),
      |acc_L, acc_R, T, T_comm| {
        let Self {
          instance: instance_L,
          W: W_L,
          E: E_L,
        } = acc_L;
        let Self {
          instance: instance_R,
          W: W_R,
          E: E_R,
        } = acc_R;

        let W_next = zip_with!((W_L.into_par_iter(), W_R.par_iter()), |w_L, w_R| w_L
          + r * w_R)
        .collect::<Vec<_>>();
        let E_next = zip_with!(
          (E_L.into_par_iter(), T.par_iter(), E_R.par_iter()),
          |e_L, t, e_R| {
            let e_tmp = *t + r * e_R;
            e_L + r * e_tmp
          }
        )
        .collect::<Vec<_>>();

        let (instance_next, W_sm_proof, E1_sm_proof, E2_sm_proof) = {
          // Unpack accumulator
          let RelaxedR1CSInstance {
            u: u_L,
            X: X_L,
            W: W_L,
            E: E_L,
          } = instance_L;

          // Unpack fresh proof
          let RelaxedR1CSInstance {
            u: u_R,
            X: X_R,
            W: W_R,
            E: E_R,
          } = instance_R;

          let u_next = u_L + r * u_R;
          let X_next = zip_eq(X_L.into_iter(), X_R.iter())
            .map(|(x_L, x_R)| x_L + r * x_R)
            .collect::<Vec<_>>();
          // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
          // W_next = W_L + r * W_R
          let (W_next, W_sm_proof) = acc_sm.scalar_mul(W_L, W_R, r, transcript);
          let (E1_next, E1_sm_proof) = acc_sm.scalar_mul(T_comm, E_R, r, transcript);
          // E_next = E_curr + r * E1_next = E_curr + r * T + r^2 * E_new
          let (E_next, E2_sm_proof) = acc_sm.scalar_mul(E_L, E1_next, r, transcript);

          let instance_next = RelaxedR1CSInstance {
            W: W_next,
            X: X_next,
            u: u_next,
            E: E_next,
          };
          (instance_next, W_sm_proof, E1_sm_proof, E2_sm_proof)
        };

        let acc_next = Self {
          instance: instance_next,
          W: W_next,
          E: E_next,
        };

        let merge_proof = MergeProof {
          T: T_comm,
          W_sm_proof,
          E1_sm_proof,
          E2_sm_proof,
        };
        (acc_next, merge_proof)
      }
    )
    .unzip();

    (accs_next, acc_sm, merge_proofs)
  }

  fn compute_fold_proof(
    &self,
    _ck: &CommitmentKey<E>,
    _shape: &R1CSShape<E>,
    _u_new: Option<E::Scalar>,
    _X_new: &[E::Scalar],
    _W_new: &[E::Scalar],
  ) -> (Vec<E::Scalar>, Commitment<E>) {
    // let T_comm = CE::<E>::commit(ck, &T);
    todo!()
  }
}

impl<E: Engine> RelaxedR1CSInstance<E> {
  pub fn default(shape: &R1CSShape<E>) -> Self {
    Self {
      u: E::Scalar::ZERO,
      X: vec![E::Scalar::ZERO; shape.num_io],
      W: Commitment::<E>::default(),
      E: Commitment::<E>::default(),
    }
  }
}
