use bellpepper_core::ConstraintSystem;

use crate::bellpepper::solver::SatisfyingAssignment;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::FoldProof;
use crate::parafold::transcript::prover::Transcript;
use crate::r1cs::R1CSShape;
use crate::traits::{CurveCycleEquipped, Dual, Engine};
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
pub struct ScalarMulAccumulator<E: Engine> {
  deferred: Vec<ScalarMulInstance<E>>,
}

impl<E: Engine> ScalarMulAccumulator<E> {
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
    transcript: &mut Transcript<E::Scalar>,
  ) -> Commitment<E> {
    let C: Commitment<E> = A + B * x;

    transcript.absorb_commitment_primary::<E>(C.clone());

    self.deferred.push(ScalarMulInstance { A, B, x, C });

    C
  }
}

impl<E: CurveCycleEquipped> ScalarMulAccumulator<E> {
  /// Consume all deferred scalar multiplication instances and create a folding proof for each result.
  /// The proofs are folded into a mutable RelaxedR1CS for the corresponding circuit over the secondary curve.
  pub fn finalize(
    self,
    ck: &CommitmentKey<E::Secondary>,
    shape: &R1CSShape<E::Secondary>,
    acc_cf: &mut RelaxedR1CS<E::Secondary>,
    transcript: &mut Transcript<E::Scalar>,
  ) -> Vec<FoldProof<E::Secondary>> {
    self
      .deferred
      .into_iter()
      .map(|_instance| {
        let cs = SatisfyingAssignment::<Dual<E>>::new();
        // TODO: synthesize the circuit that proves `instance`
        let (X, W) = cs.to_assignments();
        acc_cf.fold_secondary::<E>(ck, shape, X, &W, transcript)
      })
      .collect()
  }

  pub fn simulate_finalize(
    self,
    transcript: &mut Transcript<E::Scalar>,
  ) -> Vec<FoldProof<E::Secondary>> {
    self
      .deferred
      .into_iter()
      .map(|_| RelaxedR1CS::simulate_fold_secondary::<E>(transcript))
      .collect()
  }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ScalarMulInstance<E: Engine> {
  A: Commitment<E>,
  B: Commitment<E>,
  x: E::Scalar,
  C: Commitment<E>,
}
