//! This module defines the `RecursiveSNARKTrait` to abstract over the different implementations of
//! RecursiveSNARK
//!
//! NOTE: This trait is probably going to be changed in the future, it's a first guess on what it
//! should look like.
//!

use crate::{errors::NovaError, traits::Engine};

/// TODO: docs
pub trait RecursiveSNARKTrait<E1, E2, C>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  /// TODO: docs
  type PublicParams;

  /// TODO: docs
  type Proof; // FIXME: This shouldn't have to be here, but size of `Self` not known at compile time

  /// TODO: docs
  fn new(
    pp: &Self::PublicParams,
    c_primary: &C,
    z0_primary: &[E1::Scalar],
  ) -> Result<Self::Proof, NovaError>;

  /// TODO: docs
  fn prove_step(
    proof: &mut Self::Proof,
    pp: &Self::PublicParams,
    c_primary: &C,
  ) -> Result<(), NovaError>;

  /// TODO: docs
  fn verify(
    proof: &Self::Proof,
    pp: &Self::PublicParams,
    z0_primary: &[E1::Scalar],
  ) -> Result<Vec<E1::Scalar>, NovaError>;
}
