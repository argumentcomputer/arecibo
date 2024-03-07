//! This module defines some useful utilities for RO absorbing, and the Folding data used in the
//! CycleFold folding scheme.

use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
  gadgets::{f_to_nat, nat_to_limbs, scalar_as_base},
  r1cs::{R1CSInstance, RelaxedR1CSInstance},
  traits::{commitment::CommitmentTrait, AbsorbInROTrait, Engine, ROTrait},
  Commitment,
};

use ff::Field;
use serde::{Deserialize, Serialize};

/// Absorb a commitment over engine `E1` into an RO over engine `E2` by absorbing the limbs
pub(super) fn absorb_primary_commitment<E1, E2>(
  comm: &impl CommitmentTrait<E1>,
  ro: &mut impl ROTrait<E2::Base, E2::Scalar>,
) where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  let (x, y, is_infinity) = comm.to_coordinates();

  let x_limbs = nat_to_limbs(&f_to_nat(&x), BN_LIMB_WIDTH, BN_N_LIMBS).unwrap();
  let y_limbs = nat_to_limbs(&f_to_nat(&y), BN_LIMB_WIDTH, BN_N_LIMBS).unwrap();

  for limb in x_limbs {
    ro.absorb(scalar_as_base::<E2>(limb));
  }
  for limb in y_limbs {
    ro.absorb(scalar_as_base::<E2>(limb));
  }
  if is_infinity {
    ro.absorb(<E1 as Engine>::Scalar::ONE);
  } else {
    ro.absorb(<E1 as Engine>::Scalar::ZERO);
  }
}

pub(super) fn absorb_primary_r1cs<E1, E2>(
  u: &R1CSInstance<E1>,
  ro: &mut impl ROTrait<E2::Base, E2::Scalar>,
) where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  absorb_primary_commitment::<E1, E2>(&u.comm_W, ro);
  for x in &u.X {
    ro.absorb(*x);
  }
}

pub(super) fn absorb_cyclefold_r1cs<E: Engine>(u: &R1CSInstance<E>, ro: &mut E::RO) {
  u.comm_W.absorb_in_ro(ro);
  u.X.iter().for_each(|x| {
    let limbs: Vec<E::Scalar> = nat_to_limbs(&f_to_nat(x), BN_LIMB_WIDTH, BN_N_LIMBS).unwrap();
    limbs
      .into_iter()
      .for_each(|limb| ro.absorb(scalar_as_base::<E>(limb)));
  });
}

pub(super) fn absorb_primary_relaxed_r1cs<E1, E2>(U: &RelaxedR1CSInstance<E1>, ro: &mut E2::RO)
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  absorb_primary_commitment::<E1, E2>(&U.comm_W, ro);
  absorb_primary_commitment::<E1, E2>(&U.comm_E, ro);
  ro.absorb(U.u);
  for e in &U.X {
    ro.absorb(*e);
  }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub(super) struct FoldingData<E: Engine> {
  pub U: RelaxedR1CSInstance<E>,
  pub u: R1CSInstance<E>,
  pub T: Commitment<E>,
}

impl<E: Engine> FoldingData<E> {
  pub fn new(U: RelaxedR1CSInstance<E>, u: R1CSInstance<E>, T: Commitment<E>) -> Self {
    Self { U, u, T }
  }
}
