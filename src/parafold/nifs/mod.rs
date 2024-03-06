use digest::consts::U12;
use ff::Field;
use neptune::poseidon::PoseidonConstants;
use rayon::prelude::*;

use crate::r1cs::R1CSShape;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::{CurveCycleEquipped, Engine};
use crate::{Commitment, CommitmentKey, CE};

pub mod circuit;
pub mod prover;

const PRIMARY_R1CS_INSTANCE_SIZE: usize = 12;
/// Exact-sized Poseidon constants for hashing a RelaxedR1CSInstance.
/// Assumes that Commitments are serialized as 4=BN_NUM_LIMBS limbs.
type R1CSPoseidonConstants<E> = PoseidonConstants<<E as Engine>::Scalar, U12>;

/// Instance of a Relaxed-R1CS accumulator for a circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelaxedR1CSInstance<E: CurveCycleEquipped> {
  pp: E::Scalar,
  u: E::Scalar,
  X: [E::Scalar; 2],
  W: Commitment<E>,
  E: Commitment<E>,
}

pub fn compute_fold_proof<E: Engine>(
  ck: &CommitmentKey<E>,
  shape: &R1CSShape<E>,
  u_curr: E::Scalar,
  X_curr: &[E::Scalar],
  W_curr: &[E::Scalar],
  u_new: Option<E::Scalar>,
  X_new: &[E::Scalar],
  W_new: &[E::Scalar],
) -> (Vec<E::Scalar>, Commitment<E>) {
  let u_1 = u_curr;
  let u_2 = u_new.unwrap_or(E::Scalar::ONE);
  let (AZ_1, BZ_1, CZ_1) = tracing::trace_span!("AZ_1, BZ_1, CZ_1")
    .in_scope(|| shape.multiply_witness(W_curr, &u_1, X_curr))
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
