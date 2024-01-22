use std::marker::PhantomData;

use bellpepper_core::num::AllocatedNum;
use ff::Field;

use crate::constants::BN_N_LIMBS;
use crate::gadgets::nonnative::bignat::BigNat;
use crate::parafold::nifs_secondary::prover::SecondaryRelaxedR1CSInstance;
use crate::parafold::nifs_secondary::{
  AllocatedSecondaryFoldProof, AllocatedSecondaryMergeProof, AllocatedSecondaryRelaxedR1CSInstance,
};
use crate::parafold::nifs_secondary::{SecondaryFoldProof, SecondaryMergeProof};
use crate::parafold::transcript::prover::TranscriptRepresentable;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::Engine;
use crate::Commitment;

pub mod circuit;
mod circuit_alloc;
pub mod prover;

/// A native group element for the [Engine] is given by `point = (x, y)` where the coordinates are over the base field.
/// Inside a circuit, it is represented only as the hash `h = H(x, y)`, where `H` is a hash function with
/// efficient arithmetization over the base field. The identity element is represented by the zero `hash`.   
#[derive(Debug, Clone, Default, PartialEq)]
pub struct HashedCommitment<E1: Engine> {
  point: Commitment<E1>,
  // Poseidon hash of (x,y) = point. We set hash = 0 when `point` = infinity
  hash: E1::Base,
  // E1 representation of `BN_N_LIMBS` limbs with BN_LIMB_WIDTH bits.
  hash_limbs: Vec<E1::Scalar>,
}

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
  value: HashedCommitment<E1>,
  hash: BigNat<E1::Scalar>,
}

impl<E1: Engine> crate::parafold::transcript::circuit::TranscriptRepresentable<E1::Scalar>
  for AllocatedHashedCommitment<E1>
{
  fn to_field_vec(&self) -> Vec<AllocatedNum<E1::Scalar>> {
    //
    todo!()
  }
}

impl<E1: Engine> HashedCommitment<E1> {
  pub fn new(C: Commitment<E1>) -> Self {
    let (_x, _y, infinity) = C.to_coordinates();
    if infinity {
      Self {
        point: C,
        hash: E1::Base::ZERO,
        hash_limbs: vec![E1::Scalar::ZERO; BN_N_LIMBS],
      }
    } else {
      // TODO
      // Compute hash = H(x,y)
      // decompose hash into BN_N_LIMBS with BN_LIMB_WIDTH bits each
      Self {
        point: C,
        hash: E1::Base::ZERO,
        hash_limbs: vec![E1::Scalar::ZERO; BN_N_LIMBS],
      }
    }
  }
}

impl<E1: Engine> TranscriptRepresentable<E1::Scalar> for HashedCommitment<E1> {
  fn to_field_vec(&self) -> Vec<E1::Scalar> {
    self.hash_limbs.clone()
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
  pub acc: AllocatedSecondaryRelaxedR1CSInstance<E1, E2>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ScalarMulAccumulatorInstance<E2: Engine> {
  acc: SecondaryRelaxedR1CSInstance<E2>,
}

/// A proof for a non-native group operation C = A + x * B, where x is a native scalar
/// and A, B, C, are non-native group elements
#[derive(Debug, Clone, Default)]
pub struct ScalarMulFoldProof<E1: Engine, E2: Engine> {
  output: HashedCommitment<E1>,
  proof: SecondaryFoldProof<E2>,
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulFoldProof<E1: Engine, E2: Engine> {
  pub output: AllocatedHashedCommitment<E1>,
  pub proof: AllocatedSecondaryFoldProof<E1, E2>,
}

#[derive(Debug, Clone)]
pub struct ScalarMulMergeProof<E1: Engine, E2: Engine> {
  proof: SecondaryMergeProof<E2>,
  _marker: PhantomData<E1>,
}

#[derive(Debug, Clone)]
pub struct AllocatedScalarMulMergeProof<E1: Engine, E2: Engine> {
  proof: AllocatedSecondaryMergeProof<E1, E2>,
}
