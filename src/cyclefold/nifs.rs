//! This module defines the needed wrong-field NIFS prover

use std::marker::PhantomData;

use crate::{
  constants::{NUM_CHALLENGE_BITS, NUM_FE_FOR_RO},
  errors::NovaError,
  gadgets::utils::scalar_as_base,
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{commitment::CommitmentTrait, AbsorbInROTrait, Engine, ROConstants, ROTrait},
  CommitmentKey, CompressedCommitment,
};

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
  pub fn prove<C>(
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

    // FIXME
    // Want to write: U2.absorb_in_ro(&mut ro);
    // But can't because U2 is a R1CSInstance<E1> and not a R1CSInstance<E2>

    let (T, comm_T) = S.commit_T(ck, U1, W1, U2, W2)?;

    // FIXME
    // Want to write: comm_T.absorb_in_ro(&mut ro);
    // But can't because comm_T is a CompressedCommitment<E1> and not a CompressedCommitment<E2>

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
