use generic_array::typenum::{U2, U24};
use neptune::poseidon::PoseidonConstants;

use crate::traits::Engine;

pub mod circuit;
pub mod prover;

/// Poseidon constants for hashing. First element is used for the Fiat-Shamir transcript,
/// second is used for hashing points on the primary curve.
pub type TranscriptConstants<E> = (
  PoseidonConstants<<E as Engine>::Scalar, U24>,
  PoseidonConstants<<E as Engine>::Base, U2>,
);
