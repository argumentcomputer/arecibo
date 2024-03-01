use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError, Variable};

use crate::parafold::cycle_fold::gadgets::emulated::AllocatedBase;
use crate::parafold::cycle_fold::nifs::circuit::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::cycle_fold::{AllocatedPrimaryCommitment, NUM_IO_SECONDARY};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::CurveCycleEquipped;

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulAccumulator<E: CurveCycleEquipped> {
  deferred: Vec<AllocatedScalarMulInstance<E>>,
  acc: AllocatedSecondaryRelaxedR1CSInstance<E>,
}

impl<E: CurveCycleEquipped> AllocatedScalarMulAccumulator<E> {
  pub fn new(acc: AllocatedSecondaryRelaxedR1CSInstance<E>) -> Self {
    Self {
      deferred: vec![],
      acc,
    }
  }

  /// Compute the result `C <- A + x * B` by folding a proof over the secondary curve.
  pub fn scalar_mul<CS>(
    &mut self,
    mut cs: CS,
    A: AllocatedPrimaryCommitment<E>,
    B: AllocatedPrimaryCommitment<E>,
    x_bits: Vec<Boolean>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<AllocatedPrimaryCommitment<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let C = transcript.read_commitment_primary(cs.namespace(|| "transcript C"))?;

    self.deferred.push(AllocatedScalarMulInstance {
      A,
      B,
      x_bits,
      C: C.clone(),
    });

    Ok(C)
  }

  pub fn finalize<CS>(
    mut self,
    mut cs: CS,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<AllocatedSecondaryRelaxedR1CSInstance<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    for instance in self.deferred.drain(..) {
      let X = instance.to_io(CS::one());

      // TODO: In order to avoid computing unnecessary proofs, we can check
      // - x = 0 => C = A
      self
        .acc
        .fold(cs.namespace(|| "fold cf instance"), X, transcript)?;
    }

    Ok(self.acc)
  }

  pub fn is_finalized(&self) -> bool {
    self.deferred.is_empty()
  }
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulInstance<E: CurveCycleEquipped> {
  A: AllocatedPrimaryCommitment<E>,
  B: AllocatedPrimaryCommitment<E>,
  x_bits: Vec<Boolean>,
  C: AllocatedPrimaryCommitment<E>,
}

impl<E: CurveCycleEquipped> AllocatedScalarMulInstance<E> {
  fn to_io(self, one: Variable) -> [AllocatedBase<E>; NUM_IO_SECONDARY] {
    let Self { A, B, x_bits, C } = self;

    // Convert the elements in the instance to a bignum modulo E1::Base.
    // Since |E1::Scalar| < |E1::Base|, we can create the limbs without an initial bound-check
    // We should check here that the limbs are of the right size, but not-necessarily bound check them.
    let x = AllocatedBase::from_bits_le(one, &x_bits);
    [A.hash, B.hash, x, C.hash]
  }
}
