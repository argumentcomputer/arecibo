use itertools::*;
use rayon::prelude::*;

use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::cycle_fold::HashedCommitment;
use crate::parafold::nifs_primary::{FoldProof, MergeProof, RelaxedR1CSInstance};
use crate::parafold::prover::CommitmentKey;
use crate::parafold::transcript::prover::Transcript;
use crate::r1cs::R1CSShape;
use crate::traits::Engine;
use crate::zip_with;

/// A full Relaxed-R1CS accumulator for a circuit
#[derive(Debug)]
pub struct RelaxedR1CS<E1: Engine> {
  instance: RelaxedR1CSInstance<E1>,
  W: Vec<E1::Scalar>,
  E: Vec<E1::Scalar>,
  // TODO: store cache for Folding T
}

impl<E1: Engine> RelaxedR1CS<E1> {
  // pub fn default(shape: &R1CSShape<E>) -> Self {
  //   Self {
  //     instance: RelaxedR1CSInstance::default(shape),
  //     W: vec![E::Scalar::ZERO; shape.num_vars],
  //     E: vec![E::Scalar::ZERO; shape.num_cons],
  //   }
  // }

  pub fn instance(&self) -> &RelaxedR1CSInstance<E1> {
    &self.instance
  }

  /// Fold the proof for the previous state transition, producing an accumulator for the current state,
  /// and a proof to be consumed by the verifier.
  ///
  /// # Warning
  /// We assume the R1CS IO `X_new` has already been absorbed in some form into the transcript in order to avoid
  /// unnecessary hashing. The caller is responsible for ensuring this assumption is valid.
  pub fn fold<E2>(
    &mut self,
    ck: &CommitmentKey<E1>,
    shape: &R1CSShape<E1>,
    X_new: Vec<E1::Scalar>,
    W_new: &[E1::Scalar],
    acc_sm: &mut ScalarMulAccumulator<E2>,
    transcript: &mut Transcript<E1>,
  ) -> FoldProof<E1, E2>
  where
    E2: Engine<Base = E1::Scalar>,
  {
    // TODO: Parallelize both of these operations
    let W_comm_new = { ck.commit(&W_new) };
    let (T, T_comm) = { self.compute_fold_proof(ck, shape, None, &X_new, &W_new) };

    transcript.absorb(&W_comm_new);
    transcript.absorb(&T_comm);
    let r = transcript.squeeze();

    let Self {
      instance: instance_curr,
      W: W_curr,
      E: E_curr,
    } = self;

    let (instance_next, W_sm_proof, E_sm_proof) = {
      // Unpack accumulator
      let RelaxedR1CSInstance {
        u: u_curr,
        X: X_curr,
        W: W_comm_curr,
        E: E_comm_curr,
      } = instance_curr;

      // For relaxed instances, u_new = 1
      let u_next = *u_curr + r;
      let X_next = zip_eq(X_curr, X_new)
        .map(|(x_curr, x_new)| *x_curr + r * x_new)
        .collect::<Vec<_>>();
      // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
      // W_comm_next = W_comm_curr + r * W_comm_new
      let (W_comm_next, W_sm_proof) = acc_sm.scalar_mul(&W_comm_curr, &W_comm_new, &r, transcript);
      // E_comm_next = E_comm_curr + r * T
      let (E_comm_next, E_sm_proof) = acc_sm.scalar_mul(&E_comm_curr, &T_comm, &r, transcript);

      let instance_next = RelaxedR1CSInstance {
        u: u_next,
        X: X_next,
        W: W_comm_next,
        E: E_comm_next,
      };
      (instance_next, W_sm_proof, E_sm_proof)
    };

    let W_next = zip_with!(
      (W_curr.into_par_iter(), W_new.par_iter()),
      |w_curr, w_new| *w_curr + r * w_new
    )
    .collect::<Vec<_>>();
    let E_next = zip_with!(
      (E_curr.into_par_iter(), T.par_iter()),
      |e_curr, e_new| *e_curr + r * e_new
    )
    .collect::<Vec<_>>();

    let fold_proof = FoldProof {
      W: W_comm_new,
      T: T_comm,
      W_sm_proof,
      E_sm_proof,
    };

    *self = Self {
      instance: instance_next,
      W: W_next,
      E: E_next,
    };

    fold_proof
  }

  /// Fold the proof for the previous state transition, producing an accumulator for the current state,
  /// and a proof to be consumed by the verifier.
  pub fn merge_many<E2>(
    ck: &CommitmentKey<E1>,
    shapes: &[R1CSShape<E1>],
    mut accs_L: Vec<Self>,
    accs_R: Vec<Self>,
    acc_sm: &mut ScalarMulAccumulator<E2>,
    transcript: &mut Transcript<E1>,
  ) -> (Vec<Self>, Vec<MergeProof<E1, E2>>)
  where
    E2: Engine<Base = E1::Scalar>,
  {
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
      transcript.absorb(T_comm);
    }
    let r = transcript.squeeze();

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
          let (W_next, W_sm_proof) = acc_sm.scalar_mul::<E1>(&W_L, &W_R, &r, transcript);
          let (E1_next, E1_sm_proof) = acc_sm.scalar_mul::<E1>(&T_comm, &E_R, &r, transcript);
          // E_next = E_curr + r * E1_next = E_curr + r * T + r^2 * E_new
          let (E_next, E2_sm_proof) = acc_sm.scalar_mul::<E1>(&E_L, &E1_next, &r, transcript);

          let instance_next = RelaxedR1CSInstance {
            u: u_next,
            X: X_next,
            W: W_next,
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

    (accs_next, merge_proofs)
  }

  fn compute_fold_proof(
    &self,
    _ck: &CommitmentKey<E1>,
    _shape: &R1CSShape<E1>,
    _u_new: Option<E1::Scalar>,
    _X_new: &[E1::Scalar],
    _W_new: &[E1::Scalar],
  ) -> (Vec<E1::Scalar>, HashedCommitment<E1>) {
    // let T_comm = CE::<E>::commit(ck, &T);
    todo!()
  }
}
