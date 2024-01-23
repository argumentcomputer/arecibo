use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::cycle_fold::{
  AllocatedHashedCommitment, AllocatedScalarMulAccumulator, AllocatedScalarMulFoldProof,
  AllocatedScalarMulMergeProof,
};
use crate::parafold::nifs_secondary::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::Engine;

impl<E1, E2> AllocatedScalarMulAccumulator<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  /// Compute the result `C <- A + x * B` by folding a proof over the secondary curve.
  pub fn scalar_mul<CS>(
    &mut self,
    /*mut*/ cs: CS,
    A: AllocatedHashedCommitment<E1>,
    B: AllocatedHashedCommitment<E1>,
    _x: AllocatedNum<E1::Scalar>,
    proof: AllocatedScalarMulFoldProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<AllocatedHashedCommitment<E1>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let AllocatedScalarMulFoldProof { output, proof } = proof;
    transcript.absorb(&output);

    let X_new = vec![
      A.hash,
      B.hash,
      // TODO: alloc x as big nat
      // BigNat::(cs.namespace(|| "alloc x"), Some(x))?,
      output.hash.clone(),
    ];

    self.acc.fold(cs, X_new, proof, transcript)?;

    Ok(output)
  }

  /// Merges another existing [AllocatedScalarMulAccumulator] into `self`
  pub fn merge<CS>(
    cs: CS,
    self_L: Self,
    self_R: Self,
    proof: AllocatedScalarMulMergeProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let Self { acc: acc_L } = self_L;
    let Self { acc: acc_R } = self_R;
    let AllocatedScalarMulMergeProof { proof } = proof;
    let acc_next =
      AllocatedSecondaryRelaxedR1CSInstance::merge(cs, acc_L, acc_R, proof, transcript)?;
    Ok(Self { acc: acc_next })
  }
}
