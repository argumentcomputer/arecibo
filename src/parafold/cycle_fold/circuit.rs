use std::fmt::Debug;
use std::marker::PhantomData;

use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::gadgets::nonnative::bignat::BigNat;
use crate::parafold::nifs_secondary::circuit::{
  AllocatedSecondaryFoldProof, AllocatedSecondaryMergeProof, AllocatedSecondaryRelaxedR1CSInstance,
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
pub struct AllocatedHashedCommitment<E1: Engine> {
  // hash = if let Some(point) = value { H_secondary(point) } else { 0 }
  value: Option<(E1::Base, E1::Base)>,
  hash: BigNat<E1::Scalar>,
}

impl<E1: Engine> TranscriptRepresentable<E1::Scalar> for AllocatedHashedCommitment<E1> {
  fn to_field_vec(&self) -> Vec<AllocatedNum<E1::Scalar>> {
    //
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
pub struct AllocatedScalarMulAccumulator<E1: Engine, E2: Engine> {
  acc: AllocatedSecondaryRelaxedR1CSInstance<E2>,
  _marker: PhantomData<E1>,
}

impl<E1: Engine, E2: Engine<Base = E1::Scalar>> AllocatedScalarMulAccumulator<E1, E2> {
  /// Compute the result `C <- A + x * B` by folding a proof over the secondary curve.
  pub fn scalar_mul<CS>(
    self,
    /*mut*/ cs: CS,
    A: AllocatedHashedCommitment<E1>,
    B: AllocatedHashedCommitment<E1>,
    _x: AllocatedNum<E1::Scalar>,
    proof: AllocatedScalarMulFoldProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(Self, AllocatedHashedCommitment<E1>), SynthesisError>
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

    let acc_next = self.acc.fold(cs, X_new, proof, transcript)?;

    Ok((
      Self {
        acc: acc_next,
        _marker: PhantomData::default(),
      },
      output,
    ))
  }

  /// Merges another existing [AllocatedScalarMulAccumulator] into `self`
  pub fn merge<CS>(
    self,
    cs: CS,
    other: Self,
    proof: AllocatedScalarMulMergeProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let Self { acc: acc_L, .. } = self;
    let Self { acc: acc_R, .. } = other;
    let proof = proof.proof;
    let acc_next = acc_L.merge(cs, acc_R, proof, transcript)?;
    Ok(Self {
      acc: acc_next,
      _marker: PhantomData::default(),
    })
  }
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulFoldProof<E1: Engine, E2: Engine> {
  output: AllocatedHashedCommitment<E1>,
  proof: AllocatedSecondaryFoldProof<E2>,
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulMergeProof<E1: Engine, E2: Engine> {
  proof: AllocatedSecondaryMergeProof<E2>,
  _marker: PhantomData<E1>,
}
