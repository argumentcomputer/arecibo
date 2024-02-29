use bellpepper_core::ConstraintSystem;

use crate::bellpepper::solver::SatisfyingAssignment;
use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CS;
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::TranscriptElement;
use crate::r1cs::R1CSShape;
use crate::traits::CurveCycleEquipped;
use crate::{Commitment, CommitmentKey};

/// A [ScalarMulAccumulator] represents a coprocessor for efficiently computing non-native ECC scalar multiplications
/// inside a circuit.
///
/// # Details
/// During an interactive proof, all scalar multiplications operations are deferred and collected
/// into this data structure. Since the results of the operation are provided non-deterministically, it must be
/// added to the Fiat-Shamir transcript as it represents a value "provided by the prover".
///
/// All operations are proved in a batch at the end of the circuit in order to minimize latency for the prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarMulAccumulator<E: CurveCycleEquipped> {
  deferred: Vec<ScalarMulInstance<E>>,
  acc: RelaxedSecondaryR1CS<E>,
}

impl<E: CurveCycleEquipped> ScalarMulAccumulator<E> {
  pub fn new(acc: RelaxedSecondaryR1CS<E>) -> Self {
    Self {
      deferred: vec![],
      acc,
    }
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

  // pub fn merge(
  //   ck: &CommitmentKey<E::Secondary>,
  //   shape: &R1CSShape<E::Secondary>,
  //   mut self_L: Self,
  //   self_R: &Self,
  //   transcript: &mut Transcript<E>,
  // ) -> Self {
  //   let mut deferred = self_L.deferred;
  //   deferred.extend(self_R.deferred.clone());
  //   let acc = RelaxedSecondaryR1CS::merge(ck, shape, self_L.acc, &self_R.acc, transcript);
  //   Self { deferred, acc }
  // }
  //

  /// Consume all deferred scalar multiplication instances and create a folding proof for each result.
  /// The proofs are folded into a mutable RelaxedR1CS for the corresponding circuit over the secondary curve.
  pub fn finalize(
    mut self,
    ck: &CommitmentKey<E::Secondary>,
    shape: &R1CSShape<E::Secondary>,
    transcript: &mut Transcript<E>,
  ) -> RelaxedSecondaryR1CS<E> {
    self.deferred.drain(..).for_each(|_instance| {
      let cs = SatisfyingAssignment::<E::Secondary>::new();
      // TODO: synthesize the circuit that proves `instance`
      let (X, W) = cs.to_assignments();
      self.acc.fold(ck, shape, X, &W, transcript)
    });
    self.acc
  }

  pub fn simulate_finalize(mut self, transcript: &mut Transcript<E>) -> RelaxedSecondaryR1CS<E> {
    self
      .deferred
      .drain(..)
      .for_each(|_| RelaxedSecondaryR1CS::simulate_fold(transcript));
    self.acc
  }

  pub fn is_finalized(&self) -> bool {
    self.deferred.is_empty()
  }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ScalarMulInstance<E: CurveCycleEquipped> {
  A: Commitment<E>,
  B: Commitment<E>,
  x: E::Scalar,
  C: Commitment<E>,
}
