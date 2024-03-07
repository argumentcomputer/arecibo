use bellpepper_core::{ConstraintSystem, SynthesisError, Variable};
use bellpepper_core::boolean::Boolean;
use ff::PrimeField;

use crate::parafold::cycle_fold::AllocatedPrimaryCommitment;
use crate::parafold::cycle_fold::gadgets::emulated::AllocatedBase;
use crate::parafold::cycle_fold::nifs::circuit::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::cycle_fold::nifs::NUM_IO_SECONDARY;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::CurveCycleEquipped;

#[derive(Debug)]
pub struct AllocatedScalarMulAccumulator<E: CurveCycleEquipped> {
  deferred: Vec<AllocatedScalarMulInstance<E>>,
}

impl<E: CurveCycleEquipped> Drop for AllocatedScalarMulAccumulator<E> {
  fn drop(&mut self) {
    assert!(self.deferred.is_empty(), "unproved scalar multiplications")
  }
}

impl<E: CurveCycleEquipped> AllocatedScalarMulAccumulator<E> {
  pub fn new() -> Self {
    Self { deferred: vec![] }
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
    // Ensure the number of bits in the scalar matches fits.
    assert!(x_bits.len() <= E::Scalar::NUM_BITS as usize);

    let C = transcript.read_commitment_primary(cs.namespace(|| "transcript C"))?;

    self.deferred.push(AllocatedScalarMulInstance {
      A,
      B,
      x_bits,
      C: C.clone(),
    });

    Ok(C)
  }

  /// Consume a set of accumulated scalar multiplications, proving each instance by folding a proof
  /// into the internal secondary curve accumulator.
  pub fn finalize<CS>(
    mut self,
    mut cs: CS,
    acc_cf: &mut AllocatedSecondaryRelaxedR1CSInstance<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    for (i, instance) in self.deferred.drain(..).enumerate() {
      let X = instance.to_io(CS::one());

      // TODO: In order to avoid computing unnecessary proofs, we can check
      // - x = 0 => C = A
      acc_cf.fold(
        cs.namespace(|| format!("fold cf instance {i}")),
        X,
        transcript,
      )?;
    }
    Ok(())
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
