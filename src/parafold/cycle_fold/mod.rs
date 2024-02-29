use bellpepper_core::ConstraintSystem;
use digest::consts::U2;
use ff::Field;
use neptune::circuit2::Elt;
use neptune::poseidon::PoseidonConstants;
use neptune::Poseidon;

use crate::parafold::cycle_fold::gadgets::emulated::AllocatedBase;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::CurveCycleEquipped;
use crate::Commitment;

const NUM_IO_SECONDARY: usize = 4;

pub mod circuit;
pub mod gadgets;
pub mod nifs;
pub mod prover;

pub fn hash_commitment<E: CurveCycleEquipped>(commitment: Commitment<E>) -> E::Base {
  // TODO: Find a way to cache this
  let constants = PoseidonConstants::<E::Base, U2>::new();

  let (x, y, infinity) = commitment.to_coordinates();
  if infinity {
    E::Base::ZERO
  } else {
    Poseidon::new_with_preimage(&[x, y], &constants).hash()
  }
}

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
pub struct AllocatedPrimaryCommitment<E: CurveCycleEquipped> {
  // hash = if let Some(point) = value { H_secondary(point) } else { 0 }
  // TODO: Should this be a BigNat?
  pub(crate) hash: AllocatedBase<E>,
}

impl<E: CurveCycleEquipped> AllocatedPrimaryCommitment<E> {
  pub fn alloc<CS: ConstraintSystem<E::Scalar>>(mut cs: CS, commitment: Commitment<E>) -> Self {
    let hash = AllocatedBase::alloc(
      cs.namespace(|| "alloc hash"),
      hash_commitment::<E>(commitment),
    );
    Self { hash }
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> {
    self.hash.as_preimage()
  }
}
