use ff::Field;
use neptune::generic_array::typenum::U2;
use neptune::hash_type::HashType;
use neptune::poseidon::PoseidonConstants;
use neptune::{Poseidon, Strength};

use crate::traits::commitment::CommitmentTrait;
use crate::traits::CurveCycleEquipped;
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
pub fn hash_commitment<E: CurveCycleEquipped>(commitment: &Commitment<E>) -> E::Base {
  // TODO: Find a way to cache this
  let constants = PoseidonConstants::<E::Base, U2>::new_with_strength_and_type(
    Strength::Standard,
    HashType::ConstantLength(2),
  );

  let (x, y, infinity) = commitment.to_coordinates();
  if infinity {
    E::Base::ZERO
  } else {
    Poseidon::new_with_preimage(&[x, y], &constants).hash()
  }
}
