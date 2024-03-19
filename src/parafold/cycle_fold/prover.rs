use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::num::AllocatedNum;

use crate::{Commitment, CommitmentKey};
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::gadgets::utils::scalar_as_base;
use crate::parafold::cycle_fold::hash_commitment;
use crate::parafold::gadgets::ecc::AllocatedPoint;
use crate::parafold::hash::HashElement;
use crate::parafold::nifs_secondary::prover::RelaxedSecondaryR1CS;
use crate::parafold::transcript::prover::Transcript;
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
    assert!(self.deferred.is_empty(), "unproved scalar mul instances");
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

    transcript.absorb(HashElement::CommitmentPrimary(C));

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
        scalar_as_base::<E>(instance.x),
        hash_commitment::<E>(&instance.C),
      ];
      instance.synthesize(&mut cs)?;
      let (X, W) = cs.to_assignments();

      assert_eq!(&X_expected, &X[1..]);

      acc_cf.fold(ck, shape, &X[1..], &W, transcript);
    }
    Ok(())
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarMulInstance<E: CurveCycleEquipped> {
  A: Commitment<E>,
  B: Commitment<E>,
  x: E::Scalar,
  C: Commitment<E>,
}

impl<E: CurveCycleEquipped> Default for ScalarMulInstance<E> {
  fn default() -> Self {
    Self {
      A: Default::default(),
      B: Default::default(),
      x: Default::default(),
      C: Default::default(),
    }
  }
}

impl<E: CurveCycleEquipped> ScalarMulInstance<E> {
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
#[cfg(test)]
mod tests {
  use bellpepper_core::boolean::Boolean;
  use bellpepper_core::ConstraintSystem;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use expect_test::expect;

  use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
  use crate::parafold::gadgets::primary_commitment::AllocatedPrimaryCommitment;
  use crate::parafold::nifs_secondary::circuit::AllocatedSecondaryRelaxedR1CSInstance;
  use crate::parafold::nifs_secondary::RelaxedSecondaryR1CSInstance;
  use crate::parafold::transcript::circuit::AllocatedTranscript;
  use crate::parafold::transcript::new_transcript_constants;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;
  type Base = <E as Engine>::Base;

  type CS1 = TestConstraintSystem<Scalar>;
  type CS2 = TestConstraintSystem<Base>;

  #[test]
  fn test_scalar_mul_secondary() {
    let mut cs = CS2::new();
    let instance = ScalarMulInstance::<E>::default();

    instance.synthesize(cs.namespace(|| "scalar mul")).unwrap();

    expect!["3405"].assert_eq(&cs.num_constraints().to_string());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }

  #[test]
  fn test_scalar_primary() {
    let mut cs = CS1::new();

    let constants = new_transcript_constants::<E>();
    let mut transcript = AllocatedTranscript::<E>::new(constants, [], None);
    let identity =
      AllocatedPrimaryCommitment::<E>::alloc(cs.namespace(|| "alloc"), Commitment::<E>::default());
    let scalar: Vec<Boolean> = vec![];
    let mut acc_sm = AllocatedScalarMulAccumulator::<E>::new();
    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::<E>::alloc_unchecked(
      cs.namespace(|| "alloc acc_cf"),
      &RelaxedSecondaryR1CSInstance::<E>::default(),
    );
    let constraints_alloc = cs.num_constraints();

    let _ = acc_sm
      .scalar_mul(
        cs.namespace(|| "acc sm"),
        identity.clone(),
        identity.clone(),
        scalar,
        &mut transcript,
      )
      .unwrap();

    let _ = acc_sm
      .finalize(cs.namespace(|| "finalize"), acc_cf, &mut transcript)
      .unwrap();

    let constraints = cs.num_constraints() - constraints_alloc;
    expect!["6584"].assert_eq(&constraints.to_string());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
