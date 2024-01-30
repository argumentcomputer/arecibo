use bellpepper_core::ConstraintSystem;

use crate::bellpepper::solver::SatisfyingAssignment;
use crate::parafold::cycle_fold::HashedCommitment;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::FoldProof;
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::TranscriptConstants;
use crate::r1cs::R1CSShape;
use crate::traits::Engine;
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
pub struct ScalarMulAccumulator<E1: Engine> {
  constants: TranscriptConstants<E1>,
  deferred: Vec<ScalarMulInstance<E1>>,
}

impl<E1: Engine> ScalarMulAccumulator<E1> {
  pub fn new(constants: TranscriptConstants<E1>) -> Self {
    Self {
      constants,
      deferred: vec![],
    }
  }

  /// Given two commitments `A`, `B` and a scalar `x`, compute `C <- A + x * B`
  ///
  /// # Details
  /// Since the result `C` is computed by the prover, it is added to the transcript.
  /// The tuple `[A, B, x, C]` is added to the `deferred` list which will be proved in a batch later on.
  pub fn scalar_mul(
    &mut self,
    A: Commitment<E1>,
    B: Commitment<E1>,
    x: E1::Scalar,
    transcript: &mut Transcript<E1>,
  ) -> Commitment<E1> {
    let C_value = A + B * x;

    let C = self.add_to_transcript(C_value, transcript);

    self.deferred.push(ScalarMulInstance {
      A: HashedCommitment::new(A, &self.constants),
      B: HashedCommitment::new(B, &self.constants),
      x,
      C,
    });
    C_value
  }

  /// Convert a [Commitment] to a [HashedCommitment] and add it to the transcript.
  pub fn add_to_transcript(
    &self,
    C: Commitment<E1>,
    transcript: &mut Transcript<E1>,
  ) -> HashedCommitment<E1> {
    let C = HashedCommitment::new(C, &self.constants);
    transcript.absorb(C.hash_limbs);
    C
  }

  /// Consume all deferred scalar multiplication instances and create a folding proof for each result.
  /// The proofs are folded into a mutable RelaxedR1CS for the corresponding circuit over the secondary curve.
  pub fn finalize<E2>(
    self,
    ck: &CommitmentKey<E2>,
    shape: &R1CSShape<E2>,
    acc_cf: &mut RelaxedR1CS<E2>,
    transcript: &mut Transcript<E1>,
  ) -> Vec<FoldProof<E2>>
  where
    E2: Engine<Scalar = E1::Base, Base = E1::Scalar>,
  {
    self
      .deferred
      .into_iter()
      .map(|_instance| {
        let cs = SatisfyingAssignment::<E2>::new();
        // TODO: synthesize the circuit that proves `instance`
        let (X, W) = cs.to_assignments();
        acc_cf.fold_secondary(ck, shape, X, &W, transcript)
      })
      .collect()
  }

  pub fn simulate_finalize<E2>(self, transcript: &mut Transcript<E1>) -> Vec<FoldProof<E2>>
  where
    E2: Engine<Scalar = E1::Base, Base = E1::Scalar>,
  {
    self
      .deferred
      .into_iter()
      .map(|_| RelaxedR1CS::<E2>::simulate_fold_secondary(transcript))
      .collect()
  }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ScalarMulInstance<E1: Engine> {
  A: HashedCommitment<E1>,
  B: HashedCommitment<E1>,
  x: E1::Scalar,
  C: HashedCommitment<E1>,
}
