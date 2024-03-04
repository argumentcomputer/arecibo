use generic_array::typenum::U24;
use neptune::poseidon::PoseidonConstants;

use crate::parafold::cycle_fold::gadgets::emulated::BaseParams;
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
  /// Serialized as self
  Scalar(E::Scalar),
  /// Serialized as `[Scalar(limb_0), Scalar(limb_1), ...]`,
  /// where the limbs are given by the [BaseParams] definition.
  Base(E::Base),
  /// Serialized as `Base(hash)`, where `hash = Poseidon<E::Base, U2>(self.x, self.y)`
  CommitmentPrimary(Commitment<E>),
  /// Serialized as `[Scalar(self.x), Scalar(self.y)]`
  CommitmentSecondary(Commitment<E::Secondary>),
}

impl<E: CurveCycleEquipped> TranscriptElement<E> {
  pub fn to_field(&self) -> impl IntoIterator<Item = E::Scalar> {
    // TODO: figure out if we can avoid Vec
    match self {
      Self::Scalar(scalar) => vec![*scalar],
      Self::Base(base) => BaseParams::<E>::base_to_limb(*base),
      Self::CommitmentPrimary(c) => {
        let hash = hash_commitment::<E>(c);
        Self::Base(hash).to_field()
      }
      Self::CommitmentSecondary(c) => {
        let (x, y, _) = c.to_coordinates();
        [x, y].to_vec()
      }
    }
  }
}
