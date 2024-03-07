use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::num::AllocatedNum;

use crate::{Commitment, CommitmentKey};
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::gadgets::utils::scalar_as_base;
use crate::parafold::cycle_fold::gadgets::ecc::AllocatedPoint;
use crate::parafold::cycle_fold::hash_commitment;
use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CS;
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::TranscriptElement;
use crate::r1cs::R1CSShape;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::CurveCycleEquipped;

/// A [ScalarMulAccumulator] represents a coprocessor for efficiently computing non-native ECC scalar multiplications
/// inside a circuit.
///
/// # Details
/// During an interactive proof, all scalar multiplications operations are deferred and collected
/// into this data structure. Since the results of the operation are provided non-deterministically, it must be
/// added to the Fiat-Shamir transcript as it represents a value "provided by the prover".
///
/// All operations are proved in a batch at the end of the circuit in order to minimize latency for the prover.
#[derive(Debug, PartialEq, Eq)]
pub struct ScalarMulAccumulator<E: CurveCycleEquipped> {
  deferred: Vec<ScalarMulInstance<E>>,
}

impl<E: CurveCycleEquipped> Drop for ScalarMulAccumulator<E> {
  fn drop(&mut self) {
    if !self.deferred.is_empty() {
      panic!("unproved scalar mul instances")
    }
  }
}

impl<E: CurveCycleEquipped> ScalarMulAccumulator<E> {
  pub fn new() -> Self {
    Self { deferred: vec![] }
  }

  /// Given two commitments `A`, `B` and a scalar `x`, compute `C <- A + x * B`
  ///
  /// # Details
  /// Since the result `C` is computed by the prover, it is added to the transcript.
  /// The tuple `[A, B, x, C]` is added to the `deferred` list which will be proved in a batch later on.
  pub fn scalar_mul(
    &mut self,
    A: Commitment<E>,
    B: Commitment<E>,
    x: E::Scalar,
    transcript: &mut Transcript<E>,
  ) -> Commitment<E> {
    let C: Commitment<E> = A + B * x;

    transcript.absorb(TranscriptElement::CommitmentPrimary(C.clone()));

    self.deferred.push(ScalarMulInstance { A, B, x, C });

    C
  }

  /// Consume all deferred scalar multiplication instances and create a folding proof for each result.
  /// The proofs are folded into a mutable RelaxedR1CS for the corresponding circuit over the secondary curve.
  pub fn finalize(
    mut self,
    ck: &CommitmentKey<E::Secondary>,
    shape: &R1CSShape<E::Secondary>,
    acc_cf: &mut RelaxedSecondaryR1CS<E>,
    transcript: &mut Transcript<E>,
  ) -> Result<(), SynthesisError> {
    for instance in self.deferred.drain(..) {
      let mut cs = SatisfyingAssignment::<E::Secondary>::new();

      let X_expected = [
        hash_commitment::<E>(&instance.A),
        hash_commitment::<E>(&instance.B),
        scalar_as_base::<E>(instance.x.clone()),
        hash_commitment::<E>(&instance.C),
      ];
      instance.synthesize(&mut cs)?;
      let (X, W) = cs.to_assignments();

      assert_eq!(&X_expected, &X[1..]);

      acc_cf.fold(ck, shape, &X[1..], &W, transcript);
    }
    Ok(())
  }

  pub fn simulate_finalize(mut self, transcript: &mut Transcript<E>) {
    self
      .deferred
      .drain(..)
      .for_each(|_| RelaxedSecondaryR1CS::simulate_fold(transcript));
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarMulInstance<E: CurveCycleEquipped> {
  A: Commitment<E>,
  B: Commitment<E>,
  x: E::Scalar,
  C: Commitment<E>,
}

impl<E: CurveCycleEquipped> ScalarMulInstance<E> {
  pub fn dummy() -> Self {
    Self {
      A: Default::default(),
      B: Default::default(),
      x: Default::default(),
      C: Default::default(),
    }
  }

  #[allow(unused)]
  pub fn synthesize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Base>,
  {
    let a = AllocatedPoint::<E::GE>::alloc_hashed_input(
      cs.namespace(|| "alloc a"),
      self.A.to_coordinates(),
    )?;
    let b = AllocatedPoint::<E::GE>::alloc_hashed_input(
      cs.namespace(|| "alloc b"),
      self.B.to_coordinates(),
    )?;

    let x = AllocatedNum::alloc_input(cs.namespace(|| "alloc x"), || {
      Ok(scalar_as_base::<E>(self.x))
    })?;

    let x_bits = x.to_bits_le(cs.namespace(|| "x_bits"))?;

    let xb = b.scalar_mul(cs.namespace(|| "x*b"), &x_bits)?;
    let c = a.add(cs.namespace(|| "a + xb"), &xb)?;

    c.inputize_hashed(cs.namespace(|| "inputize c"))
  }
}
