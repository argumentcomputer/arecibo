use ff::Field;
use neptune::generic_array::typenum::{U11, Unsigned};
use neptune::poseidon::PoseidonConstants;
use rayon::prelude::*;

use crate::{CE, Commitment, CommitmentKey};
use crate::parafold::hash::{Hasher, HashWriter};
use crate::r1cs::R1CSShape;
use crate::traits::{CurveCycleEquipped, Engine};
use crate::traits::commitment::CommitmentEngineTrait;

pub mod circuit;
pub mod prover;

/// Exact-sized Poseidon constants for hashing a RelaxedR1CSInstance.
/// Assumes that Commitments are serialized as 4=BN_NUM_LIMBS limbs.
type PrimaryR1CSArity = U11;

pub type PrimaryR1CSConstants<E> = PoseidonConstants<<E as Engine>::Scalar, PrimaryR1CSArity>;

pub fn new_primary_r1cs_constants<E: Engine>() -> PrimaryR1CSConstants<E> {
  PrimaryR1CSConstants::<E>::new_constant_length(PrimaryR1CSArity::to_usize())
}

/// Instance of a Relaxed-R1CS accumulator for a circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelaxedR1CSInstance<E: CurveCycleEquipped> {
  pp: E::Scalar,
  u: E::Scalar,
  X: E::Scalar,
  W: Commitment<E>,
  E: Commitment<E>,
}

impl<E: CurveCycleEquipped> Default for RelaxedR1CSInstance<E> {
  fn default() -> Self {
    Self {
      pp: Default::default(),
      u: Default::default(),
      X: Default::default(),
      W: Default::default(),
      E: Default::default(),
    }
  }
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

impl<E: CurveCycleEquipped> HashWriter<E> for RelaxedR1CSInstance<E> {
  fn write<H: Hasher<E>>(&self, hasher: &mut H) {
    hasher.absorb_scalar(self.pp);
    hasher.absorb_scalar(self.u);
    hasher.absorb_scalar(self.X);
    hasher.absorb_commitment_primary(self.W);
    hasher.absorb_commitment_primary(self.E);
  }
}

#[cfg(test)]
mod tests {
  use bellpepper_core::ConstraintSystem;
  use bellpepper_core::test_cs::TestConstraintSystem;

  use crate::parafold::hash::{AllocatedHashWriter, check_write};
  use crate::parafold::nifs::circuit::AllocatedRelaxedR1CSInstance;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;

  type CS = TestConstraintSystem<Scalar>;

  #[test]
  fn test_write() {
    let mut cs = CS::new();

    let acc = RelaxedR1CSInstance::<E>::default();
    let allocated_acc =
      AllocatedRelaxedR1CSInstance::<E>::alloc(cs.namespace(|| "alloc acc"), acc.clone());
    check_write(cs.namespace(|| "check write"), &acc, &allocated_acc);

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_hash() {
    let mut cs = CS::new();

    let constants = new_primary_r1cs_constants::<E>();

    let acc = RelaxedR1CSInstance::<E>::default();
    let allocated_acc =
      AllocatedRelaxedR1CSInstance::<E>::alloc(cs.namespace(|| "alloc acc"), acc.clone());

    let acc_hash = acc.hash(&constants);
    let allocated_acc_hash = allocated_acc
      .hash(cs.namespace(|| "hash"), &constants)
      .unwrap();

    assert_eq!(acc_hash, allocated_acc_hash.get_value().unwrap());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
