use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};
use neptune::circuit2::Elt;
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::circuit::SpongeCircuit;
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::SpongeTrait;

use crate::parafold::transcript::TranscriptConstants;

pub struct AllocatedTranscript<F: PrimeField> {
  constants: TranscriptConstants<F>,
  state: Vec<Elt<F>>,
}

impl<F: PrimeField> AllocatedTranscript<F> {
  pub fn new(constants: TranscriptConstants<F>) -> Self {
    Self {
      constants,
      state: vec![],
    }
  }

  pub fn new_init<CS>(
    mut cs: CS,
    init: F,
    constants: TranscriptConstants<F>,
  ) -> (Self, AllocatedNum<F>)
  where
    CS: ConstraintSystem<F>,
  {
    let init = AllocatedNum::alloc_infallible(&mut cs, || init);
    let init_elt = Elt::Allocated(init.clone());
    (
      Self {
        constants,
        state: vec![init_elt],
      },
      init,
    )
  }

  pub fn absorb(&mut self, elements: impl IntoIterator<Item = AllocatedNum<F>>) {
    self.state.extend(elements.into_iter().map(Elt::Allocated));
  }

  pub(crate) fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    assert_eq!(self.state.len(), 1);
    let state = self.state[0].ensure_allocated(&mut cs, false)?;
    state.inputize(&mut cs)
  }

  pub fn squeeze<CS>(&mut self, mut cs: CS) -> Result<AllocatedNum<F>, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    let num_absorbs = self.state.len() as u32;

    let pattern = IOPattern(vec![SpongeOp::Absorb(num_absorbs), SpongeOp::Squeeze(1u32)]);

    let acc = &mut cs.namespace(|| "squeeze");

    let mut sponge = SpongeCircuit::new_with_constants(&self.constants, Simplex);
    sponge.start(pattern, None, acc);
    SpongeAPI::absorb(&mut sponge, num_absorbs, &self.state, acc);

    self.state = SpongeAPI::squeeze(&mut sponge, 1, acc);
    sponge.finish(acc).unwrap();

    let hash = self.state[0].ensure_allocated(acc, false)?;

    Ok(hash)
  }

  pub fn squeeze_bits<CS>(
    &mut self,
    mut cs: CS,
    num_bits: usize,
  ) -> Result<Vec<AllocatedBit>, SynthesisError>
  where
    CS: ConstraintSystem<F>,
    F: PrimeFieldBits,
  {
    let hash = self.squeeze(&mut cs)?;

    let bits = hash
      .to_bits_le_strict(cs.namespace(|| "hash to bits"))?
      .into_iter()
      .take(num_bits)
      .map(|boolean| match boolean {
        Boolean::Is(x) => x,
        _ => unreachable!("Wrong type of input. We should have never reached there"),
      })
      .collect::<Vec<_>>();

    Ok(bits)
  }

  /// Combine two transcripts
  pub fn merge(mut self_L: Self, self_R: Self) -> Self {
    assert_eq!(self_L.state.len(), 1);
    assert_eq!(self_R.state.len(), 1);
    self_L.state.extend(self_R.state);
    self_L
  }
}
