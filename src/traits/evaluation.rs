//! This module defines a collection of traits that define the behavior of a polynomial evaluation engine
//! A vector of size N is treated as a multilinear polynomial in \log{N} variables,
//! and a commitment provided by the commitment engine is treated as a multilinear polynomial commitment
use crate::{
  errors::NovaError,
  traits::{commitment::CommitmentEngineTrait, Group},
};
use abomonation::Abomonation;
use serde::{Deserialize, Serialize};

/// A trait that ties different pieces of the commitment evaluation together
pub trait EvaluationEngineTrait: Clone + Send + Sync {
  /// The group type used in the engine's homomorphic commitment scheme
  type G: Group;

  /// A type that holds the prover key
  type ProverKey: Clone + Send + Sync + Serialize + for<'de> Deserialize<'de> + Abomonation;

  /// A type that holds the verifier key
  type VerifierKey: Clone + Send + Sync + Serialize + for<'de> Deserialize<'de> + Abomonation;

  /// A type that holds the evaluation argument
  type EvaluationArgument: Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// A method to perform any additional setup needed to produce proofs of evaluations
  fn setup(
    ck: &<<Self::G as Group>::CE as CommitmentEngineTrait>::CommitmentKey,
  ) -> (Self::ProverKey, Self::VerifierKey);

  /// A method to prove the evaluation of a multilinear polynomial
  fn prove(
    ck: &<<Self::G as Group>::CE as CommitmentEngineTrait>::CommitmentKey,
    pk: &Self::ProverKey,
    transcript: &mut <Self::G as Group>::TE,
    comm: &<<Self::G as Group>::CE as CommitmentEngineTrait>::Commitment,
    poly: &[<Self::G as Group>::Scalar],
    point: &[<Self::G as Group>::Scalar],
    eval: &<Self::G as Group>::Scalar,
  ) -> Result<Self::EvaluationArgument, NovaError>;

  /// A method to verify the purported evaluation of a multilinear polynomials
  fn verify(
    vk: &Self::VerifierKey,
    transcript: &mut <Self::G as Group>::TE,
    comm: &<<Self::G as Group>::CE as CommitmentEngineTrait>::Commitment,
    point: &[<Self::G as Group>::Scalar],
    eval: &<Self::G as Group>::Scalar,
    arg: &Self::EvaluationArgument,
  ) -> Result<(), NovaError>;
}
