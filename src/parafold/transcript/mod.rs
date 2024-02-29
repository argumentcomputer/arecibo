use ff::{PrimeField, PrimeFieldBits};
use generic_array::typenum::U24;
use neptune::poseidon::PoseidonConstants;

use crate::parafold::cycle_fold::hash_commitment;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::CurveCycleEquipped;
use crate::Commitment;

pub mod circuit;
pub mod prover;

/// Poseidon constants for hashing used for the Fiat-Shamir transcript
pub type TranscriptConstants<F> = PoseidonConstants<F, U24>;

#[derive(Clone, Debug)]
pub enum TranscriptElement<E: CurveCycleEquipped> {
  Scalar(E::Scalar),
  Base(E::Base),
  CommitmentPrimary(Commitment<E>),
  CommitmentSecondary(Commitment<E::Secondary>),
}

impl<E: CurveCycleEquipped> TranscriptElement<E> {
  pub fn to_field(&self) -> impl IntoIterator<Item = E::Scalar> {
    // TODO: figure out if we can avoid Vec
    match self {
      TranscriptElement::Scalar(scalar) => vec![*scalar],
      TranscriptElement::Base(base) => base
        .to_le_bits()
        .chunks(128)
        .map(|bits| {
          bits
            .iter()
            .enumerate()
            .fold(0_u128, |mut byte, (index, bit)| {
              if *bit {
                let mask = 1_u128 << index;
                byte &= mask;
              }
              byte
            })
        })
        .map(|limb| E::Scalar::from_u128(limb))
        .collect::<Vec<_>>(),
      TranscriptElement::CommitmentPrimary(c) => {
        let hash = hash_commitment::<E>(*c);
        Self::Base(hash).to_field()
      }
      TranscriptElement::CommitmentSecondary(c) => {
        let (x, y, _) = c.to_coordinates();
        [x, y].to_vec()
      }
    }
  }

  pub fn size(&self) -> usize {
    match self {
      TranscriptElement::Scalar(_) => 1,
      TranscriptElement::Base(_) => 2,
      TranscriptElement::CommitmentPrimary(_) => 2,
      TranscriptElement::CommitmentSecondary(_) => 2,
    }
  }
}
