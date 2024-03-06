use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::AllocatedNum;
use itertools::chain;
use neptune::circuit2::Elt;
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::circuit::SpongeCircuit;
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::SpongeTrait;

use crate::parafold::cycle_fold::AllocatedPrimaryCommitment;
use crate::parafold::cycle_fold::gadgets::secondary_commitment::AllocatedSecondaryCommitment;
use crate::parafold::transcript::{TranscriptConstants, TranscriptElement};
use crate::traits::CurveCycleEquipped;

pub struct AllocatedTranscript<E: CurveCycleEquipped> {
  constants: TranscriptConstants<E::Scalar>,

  // Output challenge of the previous round
  prev: Option<AllocatedNum<E::Scalar>>,
  // Elements to be hashed in this round
  state: Vec<Elt<E::Scalar>>,

  // Entire contents of the prover messages
  buffer: std::vec::IntoIter<TranscriptElement<E>>,
}

impl<E: CurveCycleEquipped> AllocatedTranscript<E> {
  /// Initialize the transcript created by a prover.
  pub fn new(
    constants: TranscriptConstants<E::Scalar>,
    init: impl IntoIterator<Item = AllocatedNum<E::Scalar>>,
    buffer: Vec<TranscriptElement<E>>,
  ) -> Self {
    Self {
      constants,
      prev: None,
      state: Vec::from_iter(init.into_iter().map(Elt::Allocated)),
      buffer: buffer.into_iter(),
    }
  }

  /// Reads a single field element from the transcript
  #[allow(unused)]
  pub fn read_scalar<CS>(&mut self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let element = self
      .buffer
      .next()
      .ok_or(SynthesisError::AssignmentMissing)?;

    let val = match element {
      TranscriptElement::Scalar(val) => {
        AllocatedNum::alloc_infallible(cs.namespace(|| "alloc"), || val)
      }
      _ => return Err(SynthesisError::Unsatisfiable),
    };
    self.state.push(val.clone().into());
    Ok(val)
  }

  pub fn read_commitment_primary<CS>(
    &mut self,
    mut cs: CS,
  ) -> Result<AllocatedPrimaryCommitment<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let element = self
      .buffer
      .next()
      .ok_or(SynthesisError::AssignmentMissing)?;

    let allocated_hashed_commitment = match element {
      TranscriptElement::CommitmentPrimary(commitment) => {
        AllocatedPrimaryCommitment::alloc(cs.namespace(|| "alloc commitment primary"), &commitment)
      }
      _ => return Err(SynthesisError::AssignmentMissing),
    };

    self.state.extend(allocated_hashed_commitment.as_preimage());

    Ok(allocated_hashed_commitment)
  }

  pub fn read_commitment_secondary<CS>(
    &mut self,
    mut cs: CS,
  ) -> Result<AllocatedSecondaryCommitment<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let element = self
      .buffer
      .next()
      .ok_or(SynthesisError::AssignmentMissing)?;

    let allocated_commitment = match element {
      TranscriptElement::CommitmentSecondary(commitment) => AllocatedSecondaryCommitment::alloc(
        cs.namespace(|| "alloc commitment secondary"),
        commitment,
      ),
      _ => return Err(SynthesisError::AssignmentMissing),
    };

    self.state.extend(allocated_commitment.as_preimage());

    Ok(allocated_commitment)
  }

  pub fn squeeze<CS>(&mut self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let elements = chain!(
      self.prev.iter().cloned().map(Elt::Allocated),
      self.state.drain(..)
    )
    .collect::<Vec<_>>();

    let num_absorbs = elements.len() as u32;

    let hash = {
      let pattern = IOPattern(vec![SpongeOp::Absorb(num_absorbs), SpongeOp::Squeeze(1u32)]);

      let acc = &mut cs.namespace(|| "squeeze");

      let mut sponge = SpongeCircuit::new_with_constants(&self.constants, Simplex);
      sponge.start(pattern, None, acc);
      SpongeAPI::absorb(&mut sponge, num_absorbs, &elements, acc);

      let state_out = SpongeAPI::squeeze(&mut sponge, 1, acc);

      state_out[0].ensure_allocated(acc, true)?
    };
    self.prev = Some(hash.clone());

    Ok(hash)
  }

  pub fn squeeze_bits<CS>(
    &mut self,
    mut cs: CS,
    num_bits: usize,
  ) -> Result<Vec<Boolean>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let hash = self.squeeze(&mut cs)?;

    let bits = hash
      .to_bits_le_strict(cs.namespace(|| "hash to bits"))?
      .into_iter()
      .take(num_bits)
      .collect::<Vec<_>>();

    Ok(bits)
  }

  pub fn seal<CS>(mut self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    if !self.buffer.next().is_none() {
      return Err(SynthesisError::AssignmentMissing);
    }

    // Absorb the remaining elements into the sponge
    if !self.state.is_empty() {
      let _ = self.squeeze(&mut cs)?;
    }
    Ok(self.prev.unwrap())
  }

  pub(in crate::parafold::transcript) fn state(&self) -> Vec<Elt<E::Scalar>> {
    self.state.clone()
  }
}
