//! This module defines a collection of traits that define the behavior of a `zkSNARK` for `RelaxedR1CS`
use crate::{
  errors::NovaError,
  r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::Group,
  CommitmentKey,
};

use abomonation::Abomonation;
use serde::{Deserialize, Serialize};

/// Public parameter creation takes a size hint. This size hint carries the particular requirements of
/// the final compressing SNARK the user expected to use with these public parameters, and the below
/// is a sensible default, which is to not require any more bases then the usual (maximum of the number of
/// variables and constraints of the involved R1CS circuit).
pub fn default_ck_hint<G: Group>() -> Box<dyn for<'a> Fn(&'a R1CSShape<G>) -> usize> {
  // The default is to not put an additional floor on the size of the commitment key
  Box::new(|_shape: &R1CSShape<G>| 0)
}

/// A trait that defines the behavior of a `zkSNARK`
pub trait RelaxedR1CSSNARKTrait<G: Group>:
  Send + Sync + Serialize + for<'de> Deserialize<'de>
{
  /// A type that represents the prover's key
  type ProverKey: Send + Sync + Serialize + for<'de> Deserialize<'de> + Abomonation;

  /// A type that represents the verifier's key
  type VerifierKey: Send
    + Sync
    + Serialize
    + for<'de> Deserialize<'de>
    + DigestHelperTrait<G>
    + Abomonation;

  /// This associated function (not a method) provides a hint that offers
  /// a minimum sizing cue for the commitment key used by this SNARK
  /// implementation. The commitment key passed in setup should then
  /// be at least as large as this hint.
  fn ck_floor() -> Box<dyn for<'a> Fn(&'a R1CSShape<G>) -> usize> {
    // The default is to not put an additional floor on the size of the commitment key
    default_ck_hint()
  }

  /// Produces the keys for the prover and the verifier
  fn setup(
    ck: &CommitmentKey<G>,
    S: &R1CSShape<G>,
  ) -> Result<(Self::ProverKey, Self::VerifierKey), NovaError>;

  /// Produces a new SNARK for a relaxed R1CS
  fn prove(
    ck: &CommitmentKey<G>,
    pk: &Self::ProverKey,
    S: &R1CSShape<G>,
    U: &RelaxedR1CSInstance<G>,
    W: &RelaxedR1CSWitness<G>,
  ) -> Result<Self, NovaError>;

  /// Verifies a SNARK for a relaxed R1CS
  fn verify(&self, vk: &Self::VerifierKey, U: &RelaxedR1CSInstance<G>) -> Result<(), NovaError>;
}

/// A helper trait that defines the behavior of a verifier key of `zkSNARK`
pub trait DigestHelperTrait<G: Group> {
  /// Returns the digest of the verifier's key
  fn digest(&self) -> G::Scalar;
}
