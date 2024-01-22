use crate::gadgets::nonnative::bignat::BigNat;
use crate::parafold::ecc::AllocatedPoint;
use crate::traits::Engine;
use crate::Commitment;

pub mod circuit;
pub mod circuit_alloc;
pub mod prover;

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryRelaxedR1CSInstance<E1: Engine, E2: Engine> {
  pub u: BigNat<E1::Scalar>,
  pub X: Vec<BigNat<E1::Scalar>>,
  pub W: AllocatedPoint<E1::Scalar, E2::GE>,
  pub E: AllocatedPoint<E1::Scalar, E2::GE>,
  // q: BigNat<E1::Scalar>, // = E2::Base::MODULUS
}

/// A proof for folding a statement X of a circuit C into a Relaxed-R1CS circuit for the same circuit C
#[derive(Debug, Clone, Default)]
pub struct SecondaryFoldProof<E2: Engine> {
  W: Commitment<E2>,
  T: Commitment<E2>,
}

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryFoldProof<E1: Engine, E2: Engine> {
  W: AllocatedPoint<E1::Scalar, E2::GE>,
  T: AllocatedPoint<E1::Scalar, E2::GE>,
}

/// A proof for merging two valid Relaxed-R1CS accumulators for the same circuit C
#[derive(Debug, Clone)]
pub struct SecondaryMergeProof<E2: Engine> {
  T: Commitment<E2>,
}

#[derive(Debug, Clone)]
pub struct AllocatedSecondaryMergeProof<E1: Engine, E2: Engine> {
  pub T: AllocatedPoint<E1::Scalar, E2::GE>,
}
