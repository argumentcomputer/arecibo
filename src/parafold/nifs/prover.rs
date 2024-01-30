use ff::Field;
use itertools::*;
use rayon::prelude::*;

use crate::constants::{BN_N_LIMBS, NUM_CHALLENGE_BITS};
use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::cycle_fold::HashedCommitment;
use crate::parafold::nifs::{FoldProof, MergeProof, RelaxedR1CSInstance};
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::TranscriptConstants;
use crate::r1cs::R1CSShape;
use crate::traits::commitment::{CommitmentEngineTrait, CommitmentTrait};
use crate::traits::Engine;
use crate::{zip_with, Commitment, CommitmentKey, CE};

/// A full Relaxed-R1CS accumulator for a circuit
/// # TODO:
/// It would make sense to store the [R1CSShape] here since
/// - There is only one accumulator per shape
/// -   
#[derive(Debug)]
pub struct RelaxedR1CS<E: Engine> {
  instance: RelaxedR1CSInstance<E>,
  W: Vec<E::Scalar>,
  E: Vec<E::Scalar>,
  // TODO: store cache for Folding T
}

impl<E: Engine> RelaxedR1CS<E> {
  pub fn new(shape: &R1CSShape<E>) -> Self {
    Self {
      instance: RelaxedR1CSInstance {
        u: E::Scalar::ZERO,
        X: vec![E::Scalar::ZERO; shape.num_io],
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

  pub fn simulate_fold_primary(
    acc_sm: &mut ScalarMulAccumulator<E>,
    transcript: &mut Transcript<E>,
  ) -> FoldProof<E> {
    let W = Commitment::<E>::default();
    let T = Commitment::<E>::default();
    transcript.absorb_commitment_primary(W);
    transcript.absorb_commitment_primary(T);
    let r = transcript.squeeze();
    let _ = acc_sm.scalar_mul(W, W, r, transcript);
    let _ = acc_sm.scalar_mul(T, T, r, transcript);
    FoldProof { W, T }
  }

  pub fn simulate_fold_secondary<E1: Engine<Scalar = E::Base, Base = E::Scalar>>(
    transcript: &mut Transcript<E1>,
  ) -> FoldProof<E> {
    let W = Commitment::<E>::default();
    let T = Commitment::<E>::default();
    transcript.absorb_commitment_secondary::<E>(W);
    transcript.absorb_commitment_secondary::<E>(T);
    let _r = transcript.squeeze();
    FoldProof { W, T }
  }

  /// Given the public IO `X_new` for a circuit with R1CS representation `shape`,
  /// along with a satisfying witness vector `W_new`, and assuming `self` is a valid accumulator for the same circuit,
  /// this function will fold the statement into `self` and return a [FoldProof] that will allow the verifier to perform
  /// the same transformation over the corresponding [RelaxedR1CSInstance] of the input `self`.  
  ///
  /// # Warning
  /// We assume the R1CS IO `X_new` has already been absorbed in some form into the transcript in order to avoid
  /// unnecessary hashing. The caller is responsible for ensuring this assumption is valid.
  pub fn fold_primary(
    &mut self,
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    X_new: Vec<E::Scalar>,
    W_new: &[E::Scalar],
    acc_sm: &mut ScalarMulAccumulator<E>,
    transcript: &mut Transcript<E>,
  ) -> FoldProof<E> {
    // TODO: Parallelize both of these operations
    let W_comm_new = { E::CE::commit(ck, W_new) };
    let (T, T_comm) = { self.compute_fold_proof(ck, shape, None, &X_new, W_new) };

    acc_sm.add_to_transcript(W_comm_new, transcript);
    acc_sm.add_to_transcript(T_comm, transcript);
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
    self
      .instance
      .X
      .iter_mut()
      .zip_eq(X_new)
      .for_each(|(x, x_new)| *x += r * x_new);

    // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
    // W_comm_next = W_comm_curr + r * W_comm_new
    self.instance.W = acc_sm.scalar_mul(self.instance.W, W_comm_new, r, transcript);

    // E_comm_next = E_comm_curr + r * T
    self.instance.E = acc_sm.scalar_mul(self.instance.E, T_comm, r, transcript);

    FoldProof {
      W: W_comm_new,
      T: T_comm,
    }
  }

  pub fn fold_secondary<E1: Engine<Scalar = E::Base, Base = E::Scalar>>(
    &mut self,
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    X_new: Vec<E::Scalar>,
    W_new: &[E::Scalar],
    transcript: &mut Transcript<E1>,
  ) -> FoldProof<E> {
    // TODO: Parallelize both of these operations
    let W_comm_new = { E::CE::commit(ck, W_new) };
    let (T, T_comm) = { self.compute_fold_proof(ck, shape, None, &X_new, W_new) };

    transcript.absorb(comm_to_base::<E>(&W_comm_new));
    transcript.absorb(comm_to_base::<E>(&T_comm));
    // TODO: Squeeze
    let r = transcript.squeeze_bits_secondary(NUM_CHALLENGE_BITS);

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
    self
      .instance
      .X
      .iter_mut()
      .zip_eq(X_new)
      .for_each(|(x, x_new)| *x += r * x_new);
    self.instance.W = self.instance.W + W_comm_new * r;
    self.instance.E = self.instance.E + T_comm * r;

    FoldProof {
      W: W_comm_new,
      T: T_comm,
    }
  }

  /// Given two lists of [RelaxedR1CS] accumulators,
  pub fn merge_many(
    ck: &CommitmentKey<E>,
    shapes: &[R1CSShape<E>],
    mut accs_L: Vec<Self>,
    accs_R: &[Self],
    acc_sm: &mut ScalarMulAccumulator<E>,
    transcript: &mut Transcript<E>,
  ) -> (Vec<Self>, Vec<MergeProof<E>>) {
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
      transcript.absorb_commitment_primary(*T_comm);
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

        let instance = {
          let u = acc_L.instance.u + r * acc_R.instance.u;
          let X = zip_eq(acc_L.instance.X.into_iter(), acc_R.instance.X.iter())
            .map(|(x_L, x_R)| x_L + r * x_R)
            .collect();

          // Compute scalar multiplications and resulting instances to be proved with the CycleFold circuit
          // W_next = W_L + r * W_R
          let W = acc_sm.scalar_mul(acc_L.instance.W, acc_R.instance.W, r, transcript);

          let E_tmp = acc_sm.scalar_mul(T_comm, acc_R.instance.E, r, transcript);
          // E_next = E_L + r * E1_next = E_L + r * T + r^2 * E_R
          let E = acc_sm.scalar_mul(acc_L.instance.E, E_tmp, r, transcript);

          RelaxedR1CSInstance { u, X, W, E }
        };

        let acc = Self { instance, W, E };

        let merge_proof = MergeProof { T: T_comm };

        (acc, merge_proof)
      }
    )
    .unzip()
  }

  /// Given two lists of [RelaxedR1CS] accumulators,
  pub fn merge_secondary<E1: Engine<Scalar = E::Base, Base = E::Scalar>>(
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    acc_L: Self,
    acc_R: &Self,
    transcript: &mut Transcript<E1>,
  ) -> (Self, MergeProof<E>) {
    let (T, T_comm) = acc_L.compute_fold_proof(
      ck,
      shape,
      Some(acc_R.instance.u),
      &acc_R.instance.X,
      &acc_R.W,
    );

    transcript.absorb(comm_to_base::<E>(&T_comm));
    let r = transcript.squeeze_bits_secondary(NUM_CHALLENGE_BITS);

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

    let instance = {
      let u = acc_L.instance.u + r * acc_R.instance.u;
      let X = zip_eq(acc_L.instance.X, &acc_R.instance.X)
        .map(|(x_L, x_R)| x_L + r * x_R)
        .collect();

      let W = acc_L.instance.W + acc_R.instance.W * r;
      let E_tmp = T_comm + acc_R.instance.E * r;
      let E = acc_L.instance.E + E_tmp * r;

      RelaxedR1CSInstance { u, X, W, E }
    };

    let acc = Self { instance, W, E };

    let merge_proof = MergeProof { T: T_comm };

    (acc, merge_proof)
  }

  fn compute_fold_proof(
    &self,
    ck: &CommitmentKey<E>,
    shape: &R1CSShape<E>,
    u_new: Option<E::Scalar>,
    X_new: &[E::Scalar],
    W_new: &[E::Scalar],
  ) -> (Vec<E::Scalar>, Commitment<E>) {
    let u_1 = self.instance.u;
    let u_2 = u_new.unwrap_or(E::Scalar::ONE);
    let (AZ_1, BZ_1, CZ_1) = tracing::trace_span!("AZ_1, BZ_1, CZ_1")
      .in_scope(|| shape.multiply_witness(&self.W, &u_1, &self.instance.X))
      .unwrap();

    let (AZ_2, BZ_2, CZ_2) = tracing::trace_span!("AZ_2, BZ_2, CZ_2")
      .in_scope(|| shape.multiply_witness(W_new, &u_2, X_new))
      .unwrap();

    let (AZ_1_circ_BZ_2, AZ_2_circ_BZ_1, u_1_cdot_CZ_2, u_2_cdot_CZ_1) =
      tracing::trace_span!("cross terms").in_scope(|| {
        let AZ_1_circ_BZ_2 = (0..AZ_1.len())
          .into_par_iter()
          .map(|i| AZ_1[i] * BZ_2[i])
          .collect::<Vec<E::Scalar>>();
        let AZ_2_circ_BZ_1 = (0..AZ_2.len())
          .into_par_iter()
          .map(|i| AZ_2[i] * BZ_1[i])
          .collect::<Vec<E::Scalar>>();
        let u_1_cdot_CZ_2 = (0..CZ_2.len())
          .into_par_iter()
          .map(|i| u_1 * CZ_2[i])
          .collect::<Vec<E::Scalar>>();
        // TODO: Avoid multiplication by u2 if it is 1
        let u_2_cdot_CZ_1 = (0..CZ_1.len())
          .into_par_iter()
          .map(|i| u_2 * CZ_1[i])
          .collect::<Vec<E::Scalar>>();
        (AZ_1_circ_BZ_2, AZ_2_circ_BZ_1, u_1_cdot_CZ_2, u_2_cdot_CZ_1)
      });

    let T = tracing::trace_span!("T").in_scope(|| {
      AZ_1_circ_BZ_2
        .par_iter()
        .zip_eq(&AZ_2_circ_BZ_1)
        .zip_eq(&u_1_cdot_CZ_2)
        .zip_eq(&u_2_cdot_CZ_1)
        .map(|(((a, b), c), d)| *a + *b - *c - *d)
        .collect::<Vec<E::Scalar>>()
    });

    let comm_T = CE::<E>::commit(ck, &T);
    (T, comm_T)
  }
}

impl<E: Engine> RelaxedR1CSInstance<E> {
  pub(crate) fn default(num_io: usize) -> Self {
    Self {
      u: E::Scalar::ZERO,
      X: vec![E::Scalar::ZERO; num_io],
      W: Commitment::<E>::default(),
      E: Commitment::<E>::default(),
    }
  }
}

impl<E2: Engine> RelaxedR1CSInstance<E2> {
  pub(crate) fn as_preimage(&self) -> impl IntoIterator<Item = E2::Base> + '_ {
    // TODO, decompose into real limbs
    let u_limbs = [E2::Base::ZERO; BN_N_LIMBS];
    let X_limbs = self.X.iter().flat_map(|_x| [E2::Base::ZERO; BN_N_LIMBS]);
    let W = comm_to_base::<E2>(&self.W);
    let E = comm_to_base::<E2>(&self.E);
    chain![u_limbs, X_limbs, W, E]
  }

  pub fn io_size(&self) -> usize {
    [
      BN_N_LIMBS,                // u
      self.X.len() * BN_N_LIMBS, // X
      2,                         // W
      2,                         // E
    ]
    .into_iter()
    .sum()
  }
}

impl<E1: Engine> RelaxedR1CSInstance<E1> {
  /// On the primary curve, the instances are stored as hashes in the recursive state.
  pub fn hash(&self, transcript_constants: &TranscriptConstants<E1>) -> E1::Scalar {
    let mut transcript = Transcript::<E1>::new(transcript_constants.clone());
    let Self { u, X, W, E } = self;
    let W = HashedCommitment::<E1>::new(*W, transcript_constants);
    let E = HashedCommitment::<E1>::new(*E, transcript_constants);
    transcript.absorb(chain![
      [*u],
      X.iter().cloned(),
      W.as_preimage(),
      E.as_preimage()
    ]);
    transcript.squeeze()
  }
}

/// Convert a commitment over the secondary curve to its coordinates to it can be added to a transcript defined
/// over the primary curve.
/// The `is_infinity` flag is not added since it is computed in the circuit and the coordinates are checked.
fn comm_to_base<E2: Engine>(comm: &Commitment<E2>) -> [E2::Base; 2] {
  let (x, y, _) = comm.to_coordinates();
  [x, y]
}
