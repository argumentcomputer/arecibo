//! This module defines the needed wrong-field NIFS prover

use std::marker::PhantomData;

use ff::Field;

use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_CHALLENGE_BITS, NUM_FE_FOR_RO},
  errors::NovaError,
  gadgets::{
    nonnative::{bignat::nat_to_limbs, util::f_to_nat},
    utils::scalar_as_base,
  },
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{commitment::CommitmentTrait, /*AbsorbInROTrait,*/ Engine, ROConstants, ROTrait},
  Commitment, CommitmentKey, CompressedCommitment,
};

/// TODO: Docs
pub fn absorb_commitment<E1, E2>(comm: &Commitment<E1>, ro: &mut E2::RO)
where
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

fn absorb_r1cs<E1, E2>(u: &R1CSInstance<E1>, ro: &mut E2::RO)
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  absorb_commitment::<E1, E2>(&u.comm_W, ro);
  for x in &u.X {
    ro.absorb(*x);
  }
}

/// A SNARK that holds the proof of a step of an incremental computation
pub struct NIFS<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  pub(crate) comm_T: CompressedCommitment<E1>,
  _p: PhantomData<E2>,
}

impl<E1, E2> NIFS<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  /// Takes a relaxed R1CS instance-witness pair (U1, W1) and an R1CS instance-witness pair (U2, W)
  /// and folds them into a new relaxed R1CS instance-witness pair (U, W) and a commitment to the
  /// cross term T. It also provides the challenge r used to fold the instances.
  pub fn prove(
    ck: &CommitmentKey<E1>,
    ro_consts: &ROConstants<E2>,
    pp_digest: &E1::Scalar,
    S: &R1CSShape<E1>,
    U1: &RelaxedR1CSInstance<E1>,
    W1: &RelaxedR1CSWitness<E1>,
    U2: &R1CSInstance<E1>,
    W2: &R1CSWitness<E1>,
  ) -> Result<
    (
      Self,
      (RelaxedR1CSInstance<E1>, RelaxedR1CSWitness<E1>),
      E1::Scalar,
    ),
    NovaError,
  > {
    let mut ro = E2::RO::new(ro_consts.clone(), NUM_FE_FOR_RO);

    ro.absorb(*pp_digest);

    absorb_r1cs::<E1, E2>(U2, &mut ro);

    let (T, comm_T) = S.commit_T(ck, U1, W1, U2, W2)?;

    absorb_commitment::<E1, E2>(&comm_T, &mut ro);

    let r = scalar_as_base::<E2>(ro.squeeze(NUM_CHALLENGE_BITS));

    let U = U1.fold(U2, &comm_T, &r);

    let W = W1.fold(W2, &T, &r)?;

    Ok((
      Self {
        comm_T: comm_T.compress(),
        _p: PhantomData,
      },
      (U, W),
      r,
    ))
  }
}

#[cfg(test)]
mod test {
  // use super::*;
}
