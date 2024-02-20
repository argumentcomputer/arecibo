use ff::{Field, PrimeField, PrimeFieldBits};
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::{Sponge, SpongeTrait};

use crate::parafold::cycle_fold::HashedCommitment;
use crate::parafold::transcript::TranscriptConstants;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::Engine;
use crate::Commitment;

#[derive(Clone, Debug)]
pub struct Transcript<F: PrimeField> {
  constants: TranscriptConstants<F>,
  state: Vec<F>,
}

impl<F: PrimeField> Transcript<F> {
  pub fn new(constants: TranscriptConstants<F>) -> Self {
    Self {
      constants,
      state: vec![],
    }
  }

  pub fn new_init(init: F, constants: TranscriptConstants<F>) -> Self {
    Self {
      constants,
      state: vec![init],
    }
  }

  pub fn absorb<I>(&mut self, elements: I)
  where
    I: IntoIterator<Item = F>,
  {
    self.state.extend(elements);
  }

  pub fn absorb_commitment_primary<E1: Engine<Scalar = F>>(&mut self, c: Commitment<E1>) {
    let c_hash = HashedCommitment::<E1>::new(c);
    self.absorb(c_hash.as_preimage());
  }

  pub fn absorb_commitment_secondary<E2: Engine<Base = F>>(&mut self, c: Commitment<E2>) {
    let (x, y, _) = c.to_coordinates();
    self.absorb([x, y]);
  }

  pub fn squeeze(&mut self) -> F {
    let mut sponge = Sponge::new_with_constants(&self.constants, Simplex);
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

  pub fn squeeze_bits_secondary<Base: Field>(&mut self, num_bits: usize) -> Base
  where
    F: PrimeFieldBits,
  {
    let hash = self.squeeze();

    // Only return `num_bits`
    let bits = hash.to_le_bits();
    let mut res = Base::ZERO;
    let mut coeff = Base::ONE;
    for bit in bits.into_iter().take(num_bits) {
      if bit {
        res += coeff;
      }
      coeff += coeff;
    }
    res
  }

  pub fn seal(&self) -> F {
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
