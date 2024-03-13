use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use ff::Field;
use itertools::{enumerate, zip_eq};

use crate::gadgets::utils::{alloc_num_equals, alloc_zero, conditionally_select};
use crate::parafold::{
  NIVCMergeProof, NIVCPoseidonConstants, NIVCStepProof, VerifierStateConstants,
};
use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::hash::{AllocatedHasher, AllocatedHashWriter, Hasher, HashWriter};
use crate::parafold::io::AllocatedNIVCIO;
use crate::parafold::nifs::circuit::AllocatedRelaxedR1CSInstance;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::nifs_secondary::circuit::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::nifs_secondary::prover::RelaxedSecondaryR1CS;
use crate::parafold::nifs_secondary::RelaxedSecondaryR1CSInstance;
use crate::parafold::NIVCIO;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::supernova::StepCircuit;
use crate::traits::CurveCycleEquipped;

/// Succinct representation of the recursive NIVC state that is known
#[derive(Clone, Debug, PartialEq)]
pub struct VerifierState<E: CurveCycleEquipped> {
  pub(crate) transcript_state: E::Scalar,
  io: NIVCIO<E>,
  accs_hash: Vec<E::Scalar>,
  acc_cf: RelaxedSecondaryR1CSInstance<E>,
}

impl<E: CurveCycleEquipped> VerifierState<E> {
  pub fn new(
    io: NIVCIO<E>,
    accs: &[RelaxedR1CS<E>],
    acc_cf: &RelaxedSecondaryR1CS<E>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Self {
    Self {
      transcript_state: E::Scalar::ZERO,
      io,
      accs_hash: accs
        .iter()
        .map(|acc| acc.instance().hash(&constants.primary_r1cs))
        .collect(),
      acc_cf: acc_cf.instance().clone(),
    }
  }

  pub fn synthesize_step<CS, SF>(
    self,
    mut cs: CS,
    step_proof: NIVCStepProof<E>,
    step_circuit: &SF,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Option<Self>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    SF: StepCircuit<E::Scalar>,
  {
    let mut state =
      AllocatedVerifierState::init(cs.namespace(|| "alloc state"), self, step_proof, constants)?;

    state.io.update(cs.namespace(|| "step"), step_circuit)?;

    state.inputize(cs.namespace(|| "inputize state"), &constants.verifier_state)?;

    Ok(state.get_value())
  }

  ///Circuit
  #[allow(unused)]
  pub fn synthesize_merge<CS>(
    mut cs: CS,
    input_L: Self,
    input_R: Self,
    merge_proof: NIVCMergeProof<E>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Option<Self>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // Merge states
    let state = AllocatedVerifierState::merge(
      cs.namespace(|| "merge"),
      input_L,
      input_R,
      merge_proof,
      constants,
    )?;

    state.inputize(cs.namespace(|| "inputize state"), &constants.verifier_state)?;

    Ok(state.get_value())
  }

  pub fn dummy(arity: usize, num_circuit: usize) -> Self {
    Self {
      transcript_state: Default::default(),
      io: NIVCIO::dummy(arity),
      accs_hash: vec![Default::default(); num_circuit],
      acc_cf: Default::default(),
    }
  }
}

/// A representation of a NIVC state, where `io` represents the computations inputs and outputs,
/// and the `accs` are the accumulators for each step function that was used to produce this result.
#[derive(Clone, Debug)]
pub struct AllocatedVerifierState<E: CurveCycleEquipped> {
  transcript_state: AllocatedNum<E::Scalar>,
  pub io: AllocatedNIVCIO<E>,
  accs_hash: Vec<AllocatedNum<E::Scalar>>,
  acc_cf: AllocatedSecondaryRelaxedR1CSInstance<E>,
}

impl<E: CurveCycleEquipped> AllocatedVerifierState<E> {
  pub fn alloc_unverified<CS>(mut cs: CS, state: VerifierState<E>) -> (Self, Boolean)
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let transcript_state =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc transcript_state"), || {
        state.transcript_state
      });

    let io = AllocatedNIVCIO::alloc(cs.namespace(|| "alloc io"), state.io);
    let accs_hash = enumerate(state.accs_hash)
      .map(|(i, acc_hash)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc acc_hash {i}")), || acc_hash)
      })
      .collect::<Vec<_>>();
    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::alloc_unchecked(
      cs.namespace(|| "alloc acc_cf"),
      state.acc_cf,
    );

    // Define the base case as transcript_prev == 0
    let is_base_case = {
      let zero = alloc_zero(cs.namespace(|| "alloc zero"));
      let is_base_case = alloc_num_equals(
        cs.namespace(|| "transcript_state == 0"),
        &transcript_state,
        &zero,
      )
      .unwrap();
      Boolean::from(is_base_case)
    };

    // Enforce that the current IO is trivial, i.e. io.in == io.out
    io.enforce_trivial(
      cs.namespace(|| "is_base_case => (io.in == io.out)"),
      &is_base_case,
    );

    (
      Self {
        transcript_state,
        io,
        accs_hash,
        acc_cf,
      },
      is_base_case,
    )
  }

  /// Loads a previously proved state from a proof of its correctness.
  pub fn init<CS>(
    mut cs: CS,
    instance: VerifierState<E>,
    step_proof: NIVCStepProof<E>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let (state, is_base_case) = Self::alloc_unverified(cs.namespace(|| "alloc"), instance);
    let state_hash = state.hash(cs.namespace(|| "state hash"), &constants.verifier_state)?;

    let mut transcript = AllocatedTranscript::new(
      constants.transcript.clone(),
      [state_hash.clone()],
      step_proof.transcript_buffer,
    );

    // Initialize scalar mul accumulator for folding
    let mut acc_sm = AllocatedScalarMulAccumulator::new();

    // Load pre-image of accumulator to be updated
    let mut acc = AllocatedRelaxedR1CSInstance::alloc(cs.namespace(|| "alloc acc"), step_proof.acc);

    // Create selector for acc_hash_curr and ensure it is contained in accs_hash
    let accs_hash_selector = {
      // Compute its hash
      let acc_hash_curr = acc.hash(cs.namespace(|| "acc_hash_curr"), &constants.primary_r1cs)?;

      let bits = state
        .accs_hash
        .iter()
        .enumerate()
        .map(|(i, acc_hash)| {
          let mut cs = cs.namespace(|| format!("accs_hash_selector[{i}]"));
          // Allocate a bit which is true if i == index_prev
          let bit = step_proof.index.map_or(false, |index_prev| index_prev == i);
          let bit = AllocatedBit::alloc(cs.namespace(|| "alloc selector"), Some(bit)).unwrap();

          // Ensure acc_hash[index] = acc_hash_curr
          cs.enforce(
            || "bit * (acc_hash - acc_hash_curr) = 0",
            |lc| lc + bit.get_variable(),
            |lc| lc + acc_hash.get_variable() - acc_hash_curr.get_variable(),
            |lc| lc,
          );

          Boolean::Is(bit)
        })
        .collect::<Vec<_>>();

      let bits_sum = bits.iter().fold(LinearCombination::zero(), |lc, bit| {
        lc + &bit.lc(CS::one(), E::Scalar::ONE)
      });

      // Ensure only 1 selection bit is true, except in the base case where all bits are 0
      cs.enforce(
        || "is_base.not = ∑_i bits[i]",
        |lc| lc,
        |lc| lc,
        |_| is_base_case.not().lc(CS::one(), E::Scalar::ONE) - &bits_sum,
      );

      bits
    };

    // Set the R1CS IO as the transcript init followed by the state
    let X_new = state_hash;
    acc.fold(
      cs.namespace(|| "fold"),
      &X_new,
      &mut acc_sm,
      &mut transcript,
    )?;
    let acc_hash_next = acc.hash(
      cs.namespace(|| "hash acc_hash_next"),
      &constants.primary_r1cs,
    )?;

    // Update hashes of accumulators in state
    let accs_hash = zip_eq(&state.accs_hash, &accs_hash_selector)
      .enumerate()
      .map(|(i, (acc_hash, bit))| {
        conditionally_select(
          cs.namespace(|| format!("acc_hash_next {i}")),
          &acc_hash_next,
          acc_hash,
          bit,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    // Prove all scalar multiplication by updating the secondary curve accumulator
    // If this is the first iteration, then reset `acc_cf` to its default state since no scalar multiplications
    // were actually computed
    let acc_cf = acc_sm
      .finalize(
        cs.namespace(|| "finalize acc_sm"),
        state.acc_cf,
        &mut transcript,
      )?
      .select_default(cs.namespace(|| "enforce trivial acc_cf"), &is_base_case)?;

    let transcript_state = transcript.seal(cs.namespace(|| "checkpoint"))?;

    Ok(Self {
      transcript_state,
      io: state.io,
      accs_hash,
      acc_cf,
    })
  }

  pub fn inputize<CS>(
    &self,
    mut cs: CS,
    verifier_state_constants: &VerifierStateConstants<E>,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let state_hash = self.hash(cs.namespace(|| "state hash"), verifier_state_constants)?;
    state_hash.inputize(cs.namespace(|| "inputize state_hash"))?;
    state_hash.inputize(cs.namespace(|| "HACK inputize state_hash"))
  }

  pub fn merge<CS>(
    mut cs: CS,
    input_L: VerifierState<E>,
    input_R: VerifierState<E>,
    proof: NIVCMergeProof<E>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // Verify L
    let self_L = AllocatedVerifierState::init(
      cs.namespace(|| "alloc state_L"),
      input_L,
      proof.step_proof_L,
      constants,
    )?;
    let accs_L = self_L.load_accs(cs.namespace(|| "load accs_L"), proof.accs_L, constants)?;

    // Verify R
    let self_R = AllocatedVerifierState::init(
      cs.namespace(|| "alloc state_R"),
      input_R,
      proof.step_proof_R,
      constants,
    )?;
    let accs_R = self_R.load_accs(cs.namespace(|| "load accs_R"), proof.accs_R, constants)?;

    let mut transcript = AllocatedTranscript::new(
      constants.transcript.clone(),
      [self_L.transcript_state, self_R.transcript_state],
      proof.transcript_buffer,
    );

    let io = AllocatedNIVCIO::merge(cs.namespace(|| "io merge"), self_L.io, self_R.io);

    let mut acc_sm = AllocatedScalarMulAccumulator::new();

    // Merge the two lists of accumulators and return their hashes
    let accs = AllocatedRelaxedR1CSInstance::merge_many(
      cs.namespace(|| "accs"),
      accs_L,
      accs_R,
      &mut acc_sm,
      &mut transcript,
    )?;

    let accs_hash = accs
      .iter()
      .map(|acc| acc.hash(cs.namespace(|| "hash acc"), &constants.primary_r1cs))
      .collect::<Result<Vec<_>, _>>()?;

    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::merge(
      cs.namespace(|| "acc_cf merge"),
      self_L.acc_cf,
      self_R.acc_cf,
      &mut transcript,
    )?;

    // Prove all scalar multiplications by folding the result into the secondary curve accumulator
    let acc_cf = acc_sm.finalize(cs.namespace(|| "acc_sm finalize"), acc_cf, &mut transcript)?;

    let transcript_state = transcript.seal(cs.namespace(|| "checkpoint"))?;

    Ok(Self {
      transcript_state,
      io,
      accs_hash,
      acc_cf,
    })
  }

  fn load_accs<CS>(
    &self,
    mut cs: CS,
    accs: Vec<RelaxedR1CSInstance<E>>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Vec<AllocatedRelaxedR1CSInstance<E>>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    zip_eq(accs, &self.accs_hash)
      .map(|(acc_native, acc_hash)| {
        let acc = AllocatedRelaxedR1CSInstance::alloc(cs.namespace(|| "alloc acc"), acc_native);
        let acc_hash_real = acc.hash(cs.namespace(|| "hash acc"), &constants.primary_r1cs)?;

        // Ensure the loaded accumulator's hash matches the one from the state
        cs.enforce(
          || "acc_hash_real == acc_hash",
          |lc| lc,
          |lc| lc,
          |lc| lc + acc_hash_real.get_variable() - acc_hash.get_variable(),
        );
        Ok::<_, SynthesisError>(acc)
      })
      .collect::<Result<Vec<_>, _>>()
  }

  fn get_value(&self) -> Option<VerifierState<E>> {
    let transcript_state = self.transcript_state.get_value()?;
    let io = self.io.get_value()?;
    let accs_hash = self
      .accs_hash
      .iter()
      .map(|acc_hash| acc_hash.get_value())
      .collect::<Option<Vec<_>>>()?;
    let acc_cf = self.acc_cf.get_value()?;
    Some(VerifierState {
      transcript_state,
      io,
      accs_hash,
      acc_cf,
    })
  }
}

impl<E: CurveCycleEquipped> HashWriter<E> for VerifierState<E> {
  fn write<H: Hasher<E>>(&self, hasher: &mut H) {
    hasher.absorb_scalar(self.transcript_state);
    self.io.write(hasher);
    for acc_hash in &self.accs_hash {
      hasher.absorb_scalar(*acc_hash);
    }
    self.acc_cf.write(hasher);
  }
}

impl<E: CurveCycleEquipped> AllocatedHashWriter<E::Scalar> for AllocatedVerifierState<E> {
  fn write<H: AllocatedHasher<E::Scalar>>(&self, hasher: &mut H) {
    self.transcript_state.write(hasher);
    self.io.write(hasher);
    self.accs_hash.write(hasher);
    self.acc_cf.write(hasher);
  }
}

#[cfg(test)]
mod tests {
  use bellpepper_core::ConstraintSystem;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use expect_test::expect;

  use crate::parafold::test::TrivialNonUniform;
  use crate::provider::Bn256EngineKZG as E;
  use crate::supernova::NonUniformCircuit;
  use crate::traits::Engine;

  use super::*;

  type Scalar = <E as Engine>::Scalar;

  type CS = TestConstraintSystem<Scalar>;

  #[test]
  fn test_update() {
    let mut cs = CS::new();
    let constants = NIVCPoseidonConstants::<E>::new();

    let arity = 1;
    let num_circuits = 1;
    let nc = TrivialNonUniform::<E>::new(num_circuits);

    let state = VerifierState::<E>::dummy(arity, num_circuits);
    let dummy_proof = NIVCStepProof::<E>::dummy();
    let _ = state.synthesize_step(
      cs.namespace(|| "step"),
      dummy_proof,
      &nc.primary_circuit(0),
      &constants,
    );

    expect![["18682"]].assert_eq(&cs.num_constraints().to_string());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
  #[test]
  fn test_merge() {
    let mut cs = CS::new();
    let constants = NIVCPoseidonConstants::<E>::new();

    let arity = 1;
    let num_circuits = 1;

    let state_L = VerifierState::<E>::dummy(arity, num_circuits);
    let state_R = VerifierState::<E>::dummy(arity, num_circuits);
    let merge_proof = NIVCMergeProof::<E>::dummy(num_circuits);
    let _ = VerifierState::synthesize_merge(
      cs.namespace(|| "merge"),
      state_L,
      state_R,
      merge_proof,
      &constants,
    );

    expect![["67617"]].assert_eq(&cs.num_constraints().to_string());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
