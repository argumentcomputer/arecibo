use bellpepper_core::num::AllocatedNum;
use bellpepper_core::ConstraintSystem;
use ff::{Field, PrimeFieldBits};
use neptune::Poseidon;

use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS};
use crate::parafold::transcript::TranscriptConstants;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::Engine;
use crate::Commitment;

pub mod circuit;
pub mod prover;

/// Compressed representation of a [Commitment] for a proof over the [Engine]'s scalar field.
///
/// # Details
/// Let F_r be the scalar field over which the circuit is defined, and F_q be the base field of the group G over which
/// the proof is defined, whose scalar field is F_r. We will assume that r < q, which is the case when we instantiate
/// the proof over the BN254/Grumpkin curve cycle.
///
/// A [HashedCommitment] corresponds to a group element C \in G, and would usually be represented by
/// its coordinates (x,y) \in F_q, possibly with a boolean flag indicating whether it is equal to the identity element.
///
/// Representing F_q scalars within a circuit over F_r is expensive since we need to encode these
/// with range-checked limbs, and any operation performed over these non-native scalar require many constraints
/// to properly constrain the modular reduction by q.
///
/// An important observation we can make is that the minimal operation we need to support over [HashedCommitment]s is
/// "multiply-add", and that the internal of the group element are ignored by the recursive verifier.
///
/// We chose to represent the [HashedCommitment] C as the F_q element
///  h_C = H(C) = H((x,y)),
/// where H is a hash function with efficient arithmetization over F_q.
/// If C is the identity, then we define h_C = 0.
///
/// The circuit on the secondary curve has IO (h_C, h_A, h_B, x) \in (F_q, F_q, F_q, F_r),
/// with private inputs A, B \in G, and checks
/// - C <- A + x * B
/// - h_A == H(A), h_B == H(B), h_C == H(C)
///
/// When folding a proof for the above IO on the primary curve, each IO elements leads to a non-native "multiply-add",
/// so this additional hashing that occurs in the secondary circuit ensure we only need to perform this expensive
/// operation 4 times. Moreover, the fact that r<q ensures that the scalar x \in F_r can be trivially embedded into F_q.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HashedCommitment<E1: Engine> {
  point: Commitment<E1>,
  // Poseidon hash of (x,y) = point. We set hash = 0 when `point` = infinity
  hash: E1::Base,
  // E1 representation of `BN_N_LIMBS` limbs with BN_LIMB_WIDTH bits.
  hash_limbs: [E1::Scalar; BN_N_LIMBS],
}

impl<E1: Engine> HashedCommitment<E1> {
  /// Convert a [Commitment] to it's compressed representation.
  ///
  /// # TODO:
  /// - The Poseidon constants for `H(x,y)` over F_q are defined by `constants.1`.
  pub fn new(point: Commitment<E1>, constants: &TranscriptConstants<E1>) -> Self {
    let (x, y, infinity) = point.to_coordinates();
    if infinity {
      Self {
        point,
        hash: E1::Base::ZERO,
        hash_limbs: [E1::Scalar::ZERO; BN_N_LIMBS],
      }
    } else {
      let hash = Poseidon::new_with_preimage(&[x, y], &constants.1).hash();
      let hash_limbs = hash
        .to_le_bits()
        .chunks_exact(BN_LIMB_WIDTH)
        .map(|limb_bits| {
          // TODO: Find more efficient trick
          let mut limb = E1::Scalar::ZERO;
          for bit in limb_bits.iter().rev() {
            // double limb
            limb += limb;
            if *bit {
              limb += E1::Scalar::ONE;
            }
          }
          limb
        })
        .collect::<Vec<E1::Scalar>>();

      Self {
        point,
        hash,
        hash_limbs: hash_limbs.try_into().unwrap(),
      }
    }
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = E1::Scalar> {
    self.hash_limbs
  }
}

/// Allocated [HashedCommitment]
///
/// # Details
/// Inside the primary circuit, a [Commitment] C is represented by the limbs of the hash `h_C = H(C.x, C.y)`.
/// The limbs of `h_C` are not range-checked and we assume this check occurs during the conversion to a big integer.
///
/// # TODO
/// - Investigate whether a `is_infinity` flag is needed. It could be used to avoid synthesizing secondary circuits
///   when the scalar multiplication is trivial.
#[derive(Debug, Clone)]
pub struct AllocatedHashedCommitment<E1: Engine> {
  value: Commitment<E1>,
  // hash = if let Some(point) = value { H_secondary(point) } else { 0 }
  hash_limbs: [AllocatedNum<E1::Scalar>; BN_N_LIMBS],
}

impl<E1: Engine> AllocatedHashedCommitment<E1> {
  pub fn alloc<CS>(mut cs: CS, c: Commitment<E1>, constants: &TranscriptConstants<E1>) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let hashed = HashedCommitment::<E1>::new(c, constants);
    let hash_limbs = hashed
      .hash_limbs
      .map(|limb| AllocatedNum::alloc_infallible(cs.namespace(|| "alloc limb"), || limb));

    Self {
      value: c,
      hash_limbs,
    }
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = AllocatedNum<E1::Scalar>> {
    self.hash_limbs.clone()
  }
}
