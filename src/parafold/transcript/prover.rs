use ff::{Field, PrimeFieldBits};
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::{Sponge, SpongeTrait};

use crate::parafold::cycle_fold::HashedCommitment;
use crate::parafold::transcript::TranscriptConstants;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::Engine;
use crate::Commitment;

#[derive(Clone, Debug)]
pub struct Transcript<E: Engine> {
  constants: TranscriptConstants<E>,
  state: Vec<E::Scalar>,
}

impl<E: Engine> Transcript<E> {
  pub fn new(constants: TranscriptConstants<E>) -> Self {
    Self {
      constants,
      state: vec![],
    }
  }

  pub fn new_init(init: E::Scalar, constants: TranscriptConstants<E>) -> Self {
    Self {
      constants,
      state: vec![init],
    }
  }

  pub fn absorb<I>(&mut self, elements: I)
  where
    I: IntoIterator<Item = E::Scalar>,
  {
    self.state.extend(elements);
  }

  pub fn absorb_commitment_primary(&mut self, c: Commitment<E>) {
    let c_hash = HashedCommitment::<E>::new(c, &self.constants);
    self.absorb(c_hash.as_preimage());
  }

  pub fn absorb_commitment_secondary<E2: Engine<Base = E::Scalar>>(&mut self, c: Commitment<E2>) {
    let (x, y, _) = c.to_coordinates();
    self.absorb([x, y]);
  }

  pub fn squeeze(&mut self) -> E::Scalar {
    let mut sponge = Sponge::new_with_constants(&self.constants.0, Simplex);
    let num_absorbs = self.state.len() as u32;
    let acc = &mut ();
    let parameter = IOPattern(vec![SpongeOp::Absorb(num_absorbs), SpongeOp::Squeeze(1u32)]);
    sponge.start(parameter, None, acc);
    SpongeAPI::absorb(&mut sponge, num_absorbs, &self.state, acc);
    let hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
    sponge.finish(acc).unwrap();
    let output = hash[0];
    self.state = hash;
    output
  }

  pub fn squeeze_bits_secondary(&mut self, num_bits: usize) -> E::Base {
    let hash = self.squeeze();

    // Only return `num_bits`
    let bits = hash.to_le_bits();
    let mut res = E::Base::ZERO;
    let mut coeff = E::Base::ONE;
    for bit in bits.into_iter().take(num_bits) {
      if bit {
        res += coeff;
      }
      coeff += coeff;
    }
    res
  }

  pub fn seal(&self) -> E::Scalar {
    assert_eq!(self.state.len(), 1);
    self.state[0]
  }

  pub fn merge(mut self_L: Self, self_R: &Self) -> Self {
    assert_eq!(self_L.state.len(), 1);
    assert_eq!(self_R.state.len(), 1);
    self_L.state.extend(self_R.state.iter().cloned());
    self_L
  }
}
