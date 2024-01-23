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

  /// Given the public IO `X_new` for a circuit with R1CS representation `shape`,
  /// along with a satisfying witness vector `W_new`, and assuming `self` is a valid accumulator for the same circuit,
  /// this function will fold the statement into `self` and return a [FoldProof] that will allow the verifier to perform
  /// the same transformation over the corresponding [RelaxedR1CSInstance] of the input `self`.  
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

    self
      .W
      .par_iter_mut()
      .zip_eq(W_new.par_iter())
      .for_each(|(w, w_new)| *w += r * w_new);

    self
      .E
      .par_iter_mut()
      .zip_eq(T.par_iter())
      .for_each(|(e, t)| *e += r * t);

    let fold_proof = self
      .instance
      .fold_aux(acc_sm, X_new, W_comm_new, T_comm, r, transcript);
    fold_proof
  }

  /// Given two lists of [RelaxedR1CS] accumulators,
  pub fn merge_many<E2>(
    ck: &CommitmentKey<E1>,
    shapes: &[R1CSShape<E1>],
    mut accs_L: Vec<Self>,
    accs_R: &[Self],
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

    zip_with!(
      (
        accs_L.into_iter(),
        accs_R.iter(),
        Ts.iter(),
        T_comms.into_iter()
      ),
      |acc_L, acc_R, T, T_comm| {
        let W = zip_with!(
          (acc_L.W.into_par_iter(), acc_R.W.par_iter()),
          |w_L, w_R| w_L + r * w_R
        )
        .collect();

        let E = zip_with!(
          (acc_L.E.into_par_iter(), T.par_iter(), acc_R.E.par_iter()),
          |e_L, t, e_R| e_L + r * (*t + r * e_R)
        )
        .collect();

        let (instance, merge_proof) = RelaxedR1CSInstance::merge_aux(
          acc_L.instance,
          &acc_R.instance,
          acc_sm,
          T_comm,
          r,
          transcript,
        );

        let acc = Self { instance, W, E };

        (acc, merge_proof)
      }
    )
    .unzip()
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

impl<E1: Engine> RelaxedR1CSInstance<E1> {
  pub fn fold_aux<E2>(
    &mut self,
    acc_sm: &mut ScalarMulAccumulator<E2>,
    X_new: Vec<E1::Scalar>,
    W_new: HashedCommitment<E1>,
    T: HashedCommitment<E1>,
    r: E1::Scalar,
    transcript: &mut Transcript<E1>,
  ) -> FoldProof<E1, E2>
  where
    E2: Engine<Base = E1::Scalar>,
  {
    // For non-relaxed instances, u_new = 1
    self.u += r;
    self
      .X
      .iter_mut()
      .zip_eq(X_new)
      .for_each(|(x, x_new)| *x += r * x_new);

    // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
    // W_comm_next = W_comm_curr + r * W_comm_new
    let (W, W_sm_proof) = acc_sm.scalar_mul(&self.W, &W_new, &r, transcript);
    self.W = W;

    // E_comm_next = E_comm_curr + r * T
    let (E, E_sm_proof) = acc_sm.scalar_mul(&self.E, &T, &r, transcript);
    self.E = E;

    FoldProof {
      W: W_new,
      T,
      W_sm_proof,
      E_sm_proof,
    }
  }

  pub fn merge_aux<E2>(
    acc_L: Self,
    acc_R: &Self,
    acc_sm: &mut ScalarMulAccumulator<E2>,
    T: HashedCommitment<E1>,
    r: E1::Scalar,
    transcript: &mut Transcript<E1>,
  ) -> (Self, MergeProof<E1, E2>)
  where
    E2: Engine<Base = E1::Scalar>,
  {
    let u = acc_L.u + r * &acc_R.u;
    let X = zip_eq(acc_L.X.into_iter(), acc_R.X.iter())
      .map(|(x_L, x_R)| x_L + r * x_R)
      .collect();

    // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
    // W_next = W_L + r * W_R
    let (W, W_sm_proof) = acc_sm.scalar_mul::<E1>(&acc_L.W, &acc_R.W, &r, transcript);

    let (E1_next, E1_sm_proof) = acc_sm.scalar_mul::<E1>(&T, &acc_R.E, &r, transcript);
    // E_next = E_L + r * E1_next = E_L + r * T + r^2 * E_R
    let (E, E2_sm_proof) = acc_sm.scalar_mul::<E1>(&acc_L.E, &E1_next, &r, transcript);
    let instance = Self { u, X, W, E };

    let merge_proof = MergeProof {
      T,
      W_sm_proof,
      E1_sm_proof,
      E2_sm_proof,
    };
    (instance, merge_proof)
  }
}
