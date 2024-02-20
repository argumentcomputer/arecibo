use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use itertools::{chain, zip_eq};

use crate::parafold::cycle_fold::AllocatedHashedCommitment;
use crate::parafold::nifs::circuit_secondary::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::nifs::FoldProof;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::{CurveCycleEquipped, Engine};

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulAccumulator<E: Engine> {
  deferred: Vec<AllocatedScalarMulInstance<E>>,
}

impl<E: Engine> AllocatedScalarMulAccumulator<E> {
  pub fn new() -> Self {
    Self { deferred: vec![] }
  }

  /// Compute the result `C <- A + x * B` by folding a proof over the secondary curve.
  pub fn scalar_mul<CS>(
    &mut self,
    mut cs: CS,
    A: AllocatedHashedCommitment<E>,
    B: AllocatedHashedCommitment<E>,
    x: AllocatedNum<E::Scalar>,
    transcript: &mut AllocatedTranscript<E::Scalar>,
  ) -> Result<AllocatedHashedCommitment<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let A_value = A.value;
    let B_value = B.value;
    let x_value = x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    let C_value = A_value + B_value * x_value;
    let C = AllocatedHashedCommitment::alloc_transcript(
      cs.namespace(|| "alloc output"),
      C_value,
      transcript,
    );

    self.deferred.push(AllocatedScalarMulInstance {
      A,
      B,
      x,
      C: C.clone(),
    });

    Ok(C)
  }

  /// Merges another existing [AllocatedScalarMulAccumulator] into `self`
  pub fn merge(mut self_L: Self, mut self_R: Self) -> Self {
    self_L.deferred.append(&mut self_R.deferred);
    self_L
  }
}

impl<E: CurveCycleEquipped> AllocatedScalarMulAccumulator<E> {
  pub fn finalize<CS>(
    self,
    mut cs: CS,
    mut acc_cf: AllocatedSecondaryRelaxedR1CSInstance<E>,
    proofs: impl IntoIterator<Item = FoldProof<E::Secondary>>,
    transcript: &mut AllocatedTranscript<E::Scalar>,
  ) -> Result<AllocatedSecondaryRelaxedR1CSInstance<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    for (instance, proof) in zip_eq(self.deferred, proofs) {
      let AllocatedScalarMulInstance { A, B, x, C } = instance;
      let _X_tmp: Vec<_> = chain![A.as_preimage(), B.as_preimage(), [x], C.as_preimage()].collect();

      // TODO: In order to avoid computing unnecessary proofs, we can check
      // - x = 0 => C = A

      // Convert the elements in the instance to a bignum modulo E1::Base.
      // Since |E1::Scalar| < |E1::Base|, we can create the limbs without an initial bound-check
      // We should check here that the limbs are of the right size, but not-necessarily bound check them.
      // X = [A.as_bignum(), B.as_bignum(), x.as_bignum(), C.as_bignum()]
      let X = vec![];
      acc_cf.fold(cs.namespace(|| "fold cf instance"), X, proof, transcript)?;
    }

    Ok(acc_cf)
  }
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulInstance<E: Engine> {
  A: AllocatedHashedCommitment<E>,
  B: AllocatedHashedCommitment<E>,
  x: AllocatedNum<E::Scalar>,
  C: AllocatedHashedCommitment<E>,
}

impl<E: Engine> AllocatedScalarMulInstance<E> {
  pub fn as_preimage(&self) -> impl IntoIterator<Item = AllocatedNum<E::Scalar>> + '_ {
    chain![
      self.A.as_preimage(),
      self.B.as_preimage(),
      [self.x.clone()],
      self.C.as_preimage()
    ]
  }
}
