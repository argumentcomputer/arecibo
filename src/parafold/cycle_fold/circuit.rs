use std::marker::PhantomData;

use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::cycle_fold::prover::{
  GroupElement, ScalarMulAccumulatorInstance, ScalarMulFoldProof, ScalarMulMergeProof,
};
use crate::parafold::transcript::circuit::{AllocatedTranscript, TranscriptRepresentable};
use crate::traits::Engine;

/// Circuit representation of a [GroupElement<E>]
///
/// # Details
/// Let F_r be the scalar field over which the circuit is defined, and F_q be the base field of the group G over which
/// the proof is defined, whose scalar field is F_r. We will assume that r < q, which is the case when we instantiate
/// the proof over the BN254/Grumpkin curve cycle.
///
/// A [GroupElement] corresponds to a group element C \in G, and would usually be represented by
/// its coordinates (x,y) \in F_q, possibly with a boolean flag indicating whether it is equal to the identity element.
///
/// Representing F_q scalars within a circuit over F_r is expensive since we need to encode these
/// with range-checked limbs, and any operation performed over these non-native scalar require many constraints
/// to properly constrain the modular reduction by q.
///
/// An important observation we can make is that the minimal operation we need to support over [GroupElement]s is
/// "multiply-add", and that the internal of the group element are ignored by the recursive verifier.
///
/// We chose to represent the [GroupElement] C as the F_q element
///  h_C = H(C) = H((x,y)),
/// where H is a hash function with efficient arithmetization over F_q.
///
/// The circuit on the secondary curve has IO (h_C, h_A, h_B, x) \in (F_q, F_q, F_q, F_r),
/// with private inputs A, B \in G, and checks
/// - C <- A + x * B
/// - h_A == H(A), h_B == H(B), h_C == H(C)
///
/// When folding a proof for the above IO on the primary curve, each IO elements leads to a non-native "multiply-add",
/// so this additional hashing that occurs in the secondary circuit ensure we only need to perform this expensive
/// operation 4 times. Moreover, the fact that r<q ensures that the scalar x \in F_r can be trivially embedded into F_q.
///
/// # TODO:
/// - Move the above details (or a portion of it) to the module documentation
#[derive(Debug, Clone)]
pub struct AllocatedGroupElement<E: Engine> {
  // hash = if let Some(point) = value { H_secondary(point) } else { 0 }
  // hash: AllocatedBigNum<E>
  // value: Option<E::GE>
  _marker: PhantomData<E>,
}

impl<E: Engine> TranscriptRepresentable<E::Scalar> for AllocatedGroupElement<E> {
  fn to_field_vec(&self) -> Vec<AllocatedNum<E::Scalar>> {
    todo!()
  }
}

/// Circuit representation of a RelaxedR1CS accumulator of the non-native scalar multiplication circuit.
///
/// # Future work
/// While the secondary circuit will be quite small, generating a proof for it may lead to bottlenecks in
/// the full prover pipeline, since each operation needs to be proved sequentially. The small size of the circuit
/// also prevents efficient use of parallelism.
///
/// One way to side-step this issue is to defer all proving until the end of the interaction, while still ensuring
/// that the non-interactive instantiation of the protocol is safe.
///
/// Whenever `scalar_mul(A, B, x, transcript)` is called, the function will only compute the result `C <- A + x * B`
/// and add `C` to the `transcript`. This defines an instance `X = [A, B, C, x]` of the secondary circuit,
/// which can be appended to a list of deferred instances stored inside the mutable accumulator.
/// At the end of the protocol, the accumulator is "finalized" before being returned as output. This involves the prover
/// synthesizing and proving each instance of the circuit, until the list of deferred instances is empty.
///
/// The `merge` operation can simply compute the actual merged folding accumulators, while concatenating the two lists
/// of deferred instances.  
#[derive(Debug, Clone)]
pub struct AllocatedScalarMulAccumulator<E: Engine> {
  // acc: AllocatedSecondaryRelaxedR1CSAccumulate (mouth-full)
  _marker: PhantomData<E>,
  //
}

impl<E: Engine> AllocatedScalarMulAccumulator<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _acc: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> ScalarMulAccumulatorInstance<E>,
  {
    todo!()
  }

  /// Compute the result `C <- A + x * B` by folding a proof over the secondary curve.
  pub fn scalar_mul<CS>(
    &mut self,
    mut cs: CS,
    _A: AllocatedGroupElement<E>,
    _B: AllocatedGroupElement<E>,
    _x: AllocatedNum<E::Scalar>,
    proof: AllocatedScalarMulFoldProof<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<AllocatedGroupElement<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let AllocatedScalarMulFoldProof { output, .. } = proof;
    transcript.absorb(cs.namespace(|| "absorb output C"), &output)?;

    // unpack (C, W, T) = proof
    // add C to transcript (A, B, x are assumed to be already derived from elements added to transcript)
    // define instance X = [A,B,C,x] and folding proof pi = (W,T)
    // fold (X,pi) into self.acc, passing the transcript to which pi will be added
    // return C

    todo!()
  }

  /// Merges another existing [AllocatedScalarMulAccumulator] into `self`
  pub fn merge<CS>(
    self,
    /*mut*/ _cs: CS,
    _other: Self,
    _proof: AllocatedScalarMulMergeProof<E>,
    _transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // Merge the two SecondaryRelaxedR1CSInstances using the proof pi = T
    todo!()
  }
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulFoldProof<E: Engine> {
  output: AllocatedGroupElement<E>,
  // W: AllocatedPoint<E>
  // T: AllocatedPoint<E>
  _marker: PhantomData<E>,
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulMergeProof<E: Engine> {
  _marker: PhantomData<E>,
  // T: AllocatedPoint<E>
}

impl<E: Engine> AllocatedGroupElement<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _group_element: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> GroupElement<E>,
  {
    todo!()
  }

  pub fn get_value(&self) -> Option<E::GE> {
    todo!()
  }
}

impl<E: Engine> AllocatedScalarMulFoldProof<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> ScalarMulFoldProof<E>,
  {
    todo!()
  }
}

impl<E: Engine> AllocatedScalarMulMergeProof<E> {
  pub fn alloc_infallible<CS, F>(/*mut*/ _cs: CS, _proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> ScalarMulMergeProof<E>,
  {
    todo!()
  }
}
