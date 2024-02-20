use generic_array::typenum::U24;
use neptune::poseidon::PoseidonConstants;

use crate::traits::Engine;

pub mod circuit;
pub mod prover;

/// Poseidon constants for hashing used for the Fiat-Shamir transcript
pub type TranscriptConstants<E> = PoseidonConstants<<E as Engine>::Scalar, U24>;
