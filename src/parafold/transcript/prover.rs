use ff::PrimeFieldBits;

use crate::parafold::hash::{HashElement, Hasher};
use crate::parafold::transcript::TranscriptConstants;
use crate::traits::CurveCycleEquipped;

#[derive(Clone, Debug)]
pub struct Transcript<E: CurveCycleEquipped> {
  constants: TranscriptConstants<E>,

  // Buffer of messages for the current round
  round_state: Vec<E::Scalar>,

  // Stores the entire set of prover messages, which can be deserialized by the circuit verifier.
  // Doesn't include the message from the current round, as these are stored in `round_state`
  // and copies into `buffer` after calling `squeeze`.
  buffer: Vec<HashElement<E>>,
}

impl<E: CurveCycleEquipped> Transcript<E> {
  pub fn new(constants: TranscriptConstants<E>, init: impl IntoIterator<Item = E::Scalar>) -> Self {
    Self {
      constants,
      round_state: init.into_iter().collect(),
      buffer: vec![],
    }
  }

  pub fn absorb(&mut self, element: HashElement<E>) {
    self.round_state.absorb(element.clone());
    self.buffer.push(element);
  }

  pub fn squeeze(&mut self) -> E::Scalar {
    assert!(
      !self.round_state.is_empty(),
      "cannot squeeze from empty round state"
    );
    let hash = <Vec<E::Scalar> as Hasher<E>>::hash(&self.round_state, &self.constants);

    // save the current output
    self.round_state.clear();
    self.round_state.push(hash);

    hash
  }

  pub fn squeeze_bits(&mut self, num_bits: usize) -> Vec<bool> {
    let hash = self.squeeze();
    hash.to_le_bits().into_iter().take(num_bits).collect()
  }

  pub fn seal(mut self) -> (E::Scalar, Vec<HashElement<E>>) {
    let hash = if self.round_state.len() > 1 {
      self.squeeze()
    } else {
      self.round_state[0]
    };

    (hash, self.buffer)
  }
}
