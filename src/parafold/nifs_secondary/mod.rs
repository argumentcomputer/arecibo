use crate::parafold::hash::{HashWriter, Hasher};
use crate::traits::CurveCycleEquipped;
use crate::Commitment;

pub mod circuit;
pub mod prover;

/// The IO of the secondary circuit is always composed of 4 base field elements
/// `[hash_A, hash_B, scalar, hash_C]`
pub const NUM_IO_SECONDARY: usize = 4;

/// Instance of a Relaxed-R1CS accumulator for a circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelaxedSecondaryR1CSInstance<E: CurveCycleEquipped> {
  pub u: E::Base,
  pub X: Vec<E::Base>,
  pub W: Commitment<E::Secondary>,
  pub E: Commitment<E::Secondary>,
}

impl<E: CurveCycleEquipped> Default for RelaxedSecondaryR1CSInstance<E> {
  fn default() -> Self {
    Self {
      u: Default::default(),
      X: vec![Default::default(); NUM_IO_SECONDARY],
      W: Default::default(),
      E: Default::default(),
    }
  }
}

impl<E: CurveCycleEquipped> HashWriter<E> for RelaxedSecondaryR1CSInstance<E> {
  fn write<H: Hasher<E>>(&self, hasher: &mut H) {
    hasher.absorb_base(self.u);
    for x in &self.X {
      hasher.absorb_base(*x);
    }
    hasher.absorb_commitment_secondary(self.W);
    hasher.absorb_commitment_secondary(self.E);
  }
}
