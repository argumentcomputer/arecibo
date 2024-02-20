use generic_array::typenum::U24;
use neptune::poseidon::PoseidonConstants;

pub mod circuit;
pub mod prover;

/// Poseidon constants for hashing used for the Fiat-Shamir transcript
pub type TranscriptConstants<F> = PoseidonConstants<F, U24>;
