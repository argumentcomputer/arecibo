use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::AllocatedNum;
use neptune::circuit2::Elt;

use crate::parafold::gadgets::primary_commitment::AllocatedPrimaryCommitment;
use crate::parafold::gadgets::secondary_commitment::AllocatedSecondaryCommitment;
use crate::parafold::hash::{AllocatedHasher, AllocatedHashWriter, HashElement};
use crate::parafold::transcript::TranscriptConstants;
use crate::traits::CurveCycleEquipped;

pub struct AllocatedTranscript<E: CurveCycleEquipped> {
  constants: TranscriptConstants<E>,

  // Elements to be hashed in this round
  state: Vec<Elt<E::Scalar>>,

  // Entire contents of the prover messages.
  // If `None`, then it will always
  buffer: Option<std::vec::IntoIter<HashElement<E>>>,
}

impl<E: CurveCycleEquipped> AllocatedTranscript<E> {
  /// Initialize the transcript created by a prover.
  pub fn new(
    constants: TranscriptConstants<E>,
    init: impl IntoIterator<Item = AllocatedNum<E::Scalar>>,
    buffer: Option<Vec<HashElement<E>>>,
  ) -> Self {
    let state = init.into_iter().map(Elt::Allocated).collect();
    Self {
      constants,
      state,
      buffer: buffer.map(|b| b.into_iter()),
    }
  }

  /// Reads a single field element from the transcript
  #[allow(unused)]
  pub fn read_scalar<CS>(&mut self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let HashElement::Scalar(element) = (match &mut self.buffer {
      Some(buffer) => buffer.next().ok_or(SynthesisError::AssignmentMissing)?,
      None => HashElement::Scalar(Default::default()),
    }) else {
      unreachable!()
    };

    let allocated = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc"), || element);
    allocated.write(&mut self.state);

    Ok(allocated)
  }

  pub fn read_commitment_primary<CS>(
    &mut self,
    mut cs: CS,
  ) -> Result<AllocatedPrimaryCommitment<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let HashElement::CommitmentPrimary(element) = (match &mut self.buffer {
      Some(buffer) => buffer.next().ok_or(SynthesisError::AssignmentMissing)?,
      None => HashElement::CommitmentPrimary(Default::default()),
    }) else {
      unreachable!()
    };

    let allocated =
      AllocatedPrimaryCommitment::alloc(cs.namespace(|| "alloc commitment primary"), element);
    allocated.write(&mut self.state);

    Ok(allocated)
  }

  pub fn read_commitment_secondary<CS>(
    &mut self,
    mut cs: CS,
  ) -> Result<AllocatedSecondaryCommitment<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let HashElement::CommitmentSecondary(element) = (match &mut self.buffer {
      Some(buffer) => buffer.next().ok_or(SynthesisError::AssignmentMissing)?,
      None => HashElement::CommitmentSecondary(Default::default()),
    }) else {
      unreachable!()
    };

    let allocated =
      AllocatedSecondaryCommitment::alloc(cs.namespace(|| "alloc commitment secondary"), element);
    allocated.write(&mut self.state);

    Ok(allocated)
  }

  pub fn squeeze<CS>(&mut self, cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let hash =
      <Vec<Elt<E::Scalar>> as AllocatedHasher<E::Scalar>>::hash(&self.state, cs, &self.constants)?;
    self.state.clear();
    self.state.push(Elt::Allocated(hash.clone()));

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
    if let Some(buffer) = &mut self.buffer {
      if buffer.next().is_some() {
        return Err(SynthesisError::AssignmentMissing);
      }
    }

    // Absorb the remaining elements into the sponge
    if self.state.len() == 1 {
      return self
        .state
        .first()
        .expect("state can never be empty")
        .ensure_allocated(&mut cs.namespace(|| "alloc challenge"), true);
    }
    self.squeeze(cs.namespace(|| "squeeze"))
  }
}
