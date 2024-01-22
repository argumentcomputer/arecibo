use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS};
use crate::gadgets::nonnative::bignat::BigNat;
use crate::parafold::cycle_fold::AllocatedScalarMulAccumulator;
use crate::parafold::cycle_fold::{
  AllocatedHashedCommitment, AllocatedScalarMulFoldProof, AllocatedScalarMulMergeProof,
  HashedCommitment, ScalarMulAccumulatorInstance, ScalarMulFoldProof, ScalarMulMergeProof,
};
use crate::parafold::nifs_secondary::{
  AllocatedSecondaryFoldProof, AllocatedSecondaryMergeProof, AllocatedSecondaryRelaxedR1CSInstance,
};
use crate::traits::Engine;

impl<E1, E2> AllocatedScalarMulAccumulator<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FA>(cs: CS, acc: FA) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FA: FnOnce() -> ScalarMulAccumulatorInstance<E2>,
  {
    let ScalarMulAccumulatorInstance { acc } = acc();
    Self {
      acc: AllocatedSecondaryRelaxedR1CSInstance::alloc_infallible(cs, || acc),
    }
  }

  pub fn to_native(&self) -> Result<ScalarMulAccumulatorInstance<E2>, SynthesisError> {
    let acc = self.acc.to_native()?;
    Ok(ScalarMulAccumulatorInstance { acc })
  }
}

impl<E1: Engine> AllocatedHashedCommitment<E1> {
  pub fn alloc_infallible<CS, FH>(mut cs: CS, hashed_commitment: FH) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FH: FnOnce() -> HashedCommitment<E1>,
  {
    let value = hashed_commitment();
    // TODO: Check if we need `max_word`
    // TODO: handle error
    let hash = BigNat::alloc_from_limbs(
      cs.namespace(|| "alloc hash"),
      || Ok(value.hash_limbs.to_vec()),
      None,
      BN_LIMB_WIDTH,
      BN_N_LIMBS,
    )
    .unwrap();
    Self { value, hash }
  }

  pub fn to_native(&self) -> Result<HashedCommitment<E1>, SynthesisError> {
    Ok(self.value.clone())
  }
}

impl<E1, E2> AllocatedScalarMulFoldProof<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FF>(mut cs: CS, proof: FF) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FF: FnOnce() -> ScalarMulFoldProof<E1, E2>,
  {
    let ScalarMulFoldProof { output, proof } = proof();
    let output =
      AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc output"), || output);
    let proof =
      AllocatedSecondaryFoldProof::alloc_infallible(cs.namespace(|| "alloc proof"), || proof);
    Self { output, proof }
  }
}

impl<E1, E2> AllocatedScalarMulMergeProof<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FP>(mut cs: CS, proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> ScalarMulMergeProof<E1, E2>,
  {
    let ScalarMulMergeProof { proof, .. } = proof();
    let proof =
      AllocatedSecondaryMergeProof::alloc_infallible(cs.namespace(|| "alloc proof"), || proof);
    Self { proof }
  }
}
