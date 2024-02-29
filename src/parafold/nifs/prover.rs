use ff::Field;
use neptune::Poseidon;
use rayon::prelude::*;

use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs::{compute_fold_proof, R1CSPoseidonConstants, RelaxedR1CSInstance};
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::TranscriptElement;
use crate::r1cs::R1CSShape;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::CurveCycleEquipped;
use crate::{Commitment, CommitmentKey};

/// A full Relaxed-R1CS accumulator for a circuit
/// # TODO:
/// It would make sense to store the [R1CSShape] here since
/// - There is only one accumulator per shape
/// - We can probably use an Arc to avoid copying
#[derive(Debug)]
pub struct RelaxedR1CS<E: CurveCycleEquipped> {
  instance: RelaxedR1CSInstance<E>,
  W: Vec<E::Scalar>,
  E: Vec<E::Scalar>,
  // TODO: store cache for Folding T
}

impl<E: CurveCycleEquipped> RelaxedR1CS<E> {
  pub fn new(shape: &R1CSShape<E>) -> Self {
    assert_eq!(shape.num_io, 1);
    Self {
      instance: RelaxedR1CSInstance {
        pp: shape.digest(),
        u: E::Scalar::ZERO,
        X: E::Scalar::ZERO,
        W: Commitment::<E>::default(),
        E: Commitment::<E>::default(),
      },
      W: vec![E::Scalar::ZERO; shape.num_vars],
      E: vec![E::Scalar::ZERO; shape.num_cons],
    }
  }
  pub fn instance(&self) -> &RelaxedR1CSInstance<E> {
    &self.instance
  }

  /// Simulate the fold protocol for a circuit on the primary curve, creating a trivial proof,
  /// while updating the transcript with the standard pattern.
  pub fn simulate_fold(acc_sm: &mut ScalarMulAccumulator<E>, transcript: &mut Transcript<E>) {
    let W = Commitment::<E>::default();
    let T = Commitment::<E>::default();
    transcript.absorb(TranscriptElement::CommitmentPrimary(W));
    transcript.absorb(TranscriptElement::CommitmentPrimary(T));

    let r = transcript.squeeze();
    let _ = acc_sm.scalar_mul(W, W, r, transcript);
    let _ = acc_sm.scalar_mul(T, T, r, transcript);
  }

  /// Given the public IO `X_new` for a circuit with R1CS representation `shape`,
  /// along with a satisfying witness vector `W_new`, and assuming `self` is a valid accumulator for the same circuit,
  /// this function will fold the statement into `self` and return a [FoldProof] that will allow the verifier to perform
  /// the same transformation over the corresponding [RelaxedR1CSInstance] of the input `self`.
  ///
  /// # Warning
  /// We assume the R1CS IO `X_new` has already been absorbed in some form into the transcript in order to avoid
  /// unnecessary hashing. The caller is responsible for ensuring this assumption is valid.
  pub fn fold(
    &mut self,
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    X_new: E::Scalar,
    W_new: &[E::Scalar],
    acc_sm: &mut ScalarMulAccumulator<E>,
    transcript: &mut Transcript<E>,
  ) {
    // TODO: Parallelize both of these operations
    let W_comm_new = { E::CE::commit(ck, W_new) };
    let (T, T_comm) = {
      compute_fold_proof(
        ck,
        shape,
        self.instance.u,
        &[self.instance.X],
        &self.W,
        None,
        &[X_new],
        W_new,
      )
    };

    transcript.absorb(TranscriptElement::CommitmentPrimary(W_comm_new));
    transcript.absorb(TranscriptElement::CommitmentPrimary(T_comm));

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

    // For non-relaxed instances, u_new = 1
    self.instance.u += r;
    self.instance.X += r * X_new;

    // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
    // W_comm_next = W_comm_curr + r * W_comm_new
    self.instance.W = acc_sm.scalar_mul(self.instance.W, W_comm_new, r, transcript);

    // E_comm_next = E_comm_curr + r * T
    self.instance.E = acc_sm.scalar_mul(self.instance.E, T_comm, r, transcript);
  }

  // /// Given two lists of [RelaxedR1CS] accumulators,
  // pub fn merge_many(
  //   ck: &CommitmentKey<E>,
  //   shapes: &[R1CSShape<E>],
  //   mut accs_L: Vec<Self>,
  //   accs_R: &[Self],
  //   acc_sm: &mut ScalarMulAccumulator<E>,
  //   transcript: &mut Transcript<E>,
  // ) -> Vec<Self> {
  //   // TODO: parallelize
  //   let (Ts, T_comms): (Vec<_>, Vec<_>) = zip_with!(
  //     (accs_L.iter_mut(), accs_R.iter(), shapes),
  //     |acc_L, acc_R, shape| {
  //       compute_fold_proof(
  //         ck,
  //         shape,
  //         &acc_L.instance.u,
  //         &[acc_L.instance.X],
  //         &acc_L.W,
  //         Some(acc_R.instance.u),
  //         &[acc_R.instance.X],
  //         &acc_R.W,
  //       )
  //     }
  //   )
  //   .unzip();
  //
  //   for T_comm in &T_comms {
  //     transcript.absorb(T_comm.into());
  //   }
  //   let r = transcript.squeeze();
  //
  //   zip_with!(
  //     (
  //       accs_L.into_iter(),
  //       accs_R.iter(),
  //       Ts.iter(),
  //       T_comms.into_iter()
  //     ),
  //     |acc_L, acc_R, T, T_comm| {
  //       let W = zip_with!(
  //         (acc_L.W.into_par_iter(), acc_R.W.par_iter()),
  //         |w_L, w_R| w_L + r * w_R
  //       )
  //       .collect();
  //
  //       let E = zip_with!(
  //         (acc_L.E.into_par_iter(), T.par_iter(), acc_R.E.par_iter()),
  //         |e_L, t, e_R| e_L + r * (*t + r * e_R)
  //       )
  //       .collect();
  //
  //       let instance = {
  //         assert_eq!(acc_L.instance.pp, acc_R.instance.pp);
  //         let pp = acc_L.instance.pp;
  //
  //         let u = acc_L.instance.u + r * acc_R.instance.u;
  //         let X = acc_L.instance.X + r * acc_R.instance.X;
  //
  //         // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
  //         // W_next = W_L + r * W_R
  //         let W = acc_sm.scalar_mul(acc_L.instance.W, acc_R.instance.W, r, transcript);
  //
  //         let E_tmp = acc_sm.scalar_mul(T_comm, acc_R.instance.E, r, transcript);
  //         // E_next = E_L + r * E1_next = E_L + r * T + r^2 * E_R
  //         let E = acc_sm.scalar_mul(acc_L.instance.E, E_tmp, r, transcript);
  //
  //         RelaxedR1CSInstance { pp, u, X, W, E }
  //       };
  //       Self { instance, W, E }
  //     }
  //   )
  //   .collect()
  // }
}

impl<E: CurveCycleEquipped> RelaxedR1CSInstance<E> {
  pub fn default() -> Self {
    Self {
      pp: Default::default(),
      u: Default::default(),
      X: Default::default(),
      W: Default::default(),
      E: Default::default(),
    }
  }
  pub fn as_preimage(&self) -> impl IntoIterator<Item = TranscriptElement<E>> {
    let pp = TranscriptElement::Scalar(self.pp);
    let u = TranscriptElement::Scalar(self.u);
    let X = TranscriptElement::Scalar(self.X);
    let W = TranscriptElement::CommitmentPrimary(self.W.clone());
    let E = TranscriptElement::CommitmentPrimary(self.E.clone());
    [pp, u, X, W, E]
  }

  /// On the primary curve, the instances are stored as hashes in the recursive state.
  pub fn hash(&self) -> E::Scalar {
    let constants = R1CSPoseidonConstants::<E>::new();
    let elements = self
      .as_preimage()
      .into_iter()
      .map(|x| x.to_field())
      .flatten()
      .collect::<Vec<_>>();
    Poseidon::new_with_preimage(&elements, &constants).hash()
  }
}
