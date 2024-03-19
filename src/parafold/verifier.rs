use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use ff::Field;
use itertools::{enumerate, zip_eq};

use crate::gadgets::utils::{alloc_num_equals, alloc_zero, conditionally_select};
use crate::parafold::{MergeProof, NIVCPoseidonConstants, StepProof, VerifierStateConstants};
use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::hash::{AllocatedHasher, AllocatedHashWriter, Hasher, HashWriter};
use crate::parafold::io::AllocatedStepCircuitIO;
use crate::parafold::nifs::circuit::AllocatedRelaxedR1CSInstance;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::nifs_secondary::circuit::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::nifs_secondary::prover::RelaxedSecondaryR1CS;
use crate::parafold::nifs_secondary::RelaxedSecondaryR1CSInstance;
use crate::parafold::StepCircuitIO;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::supernova::StepCircuit;
use crate::traits::CurveCycleEquipped;

/// Succinct representation of the recursive NIVC state that is known
#[derive(Clone, Debug, PartialEq)]
pub struct VerifierState<E: CurveCycleEquipped> {
  pub(crate) transcript_state: E::Scalar,
  io: StepCircuitIO<E>,
  accs_hash: Vec<E::Scalar>,
  acc_cf: RelaxedSecondaryR1CSInstance<E>,
}

impl<E: CurveCycleEquipped> VerifierState<E> {
  pub fn new(
    io: StepCircuitIO<E>,
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
    &self,
    mut cs: CS,
    step_proof: StepProof<E>,
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
    input_L: &Self,
    input_R: &Self,
    merge_proof: MergeProof<E>,
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

  pub fn dummy(arity: usize, num_circuit: usize, _constants: &NIVCPoseidonConstants<E>) -> Self {
    let dummy_hash = E::Scalar::ZERO;
    // let dummy_hash = RelaxedR1CSInstance::<E>::init(E::Scalar::ZERO).hash(&constants.primary_r1cs);
    Self {
      transcript_state: Default::default(),
      io: StepCircuitIO::dummy(arity),
      accs_hash: vec![dummy_hash; num_circuit],
      acc_cf: Default::default(),
    }
  }
}

/// A representation of a NIVC state, where `io` represents the computations inputs and outputs,
/// and the `accs` are the accumulators for each step function that was used to produce this result.
#[derive(Clone, Debug)]
pub struct AllocatedVerifierState<E: CurveCycleEquipped> {
  transcript_state: AllocatedNum<E::Scalar>,
  pub io: AllocatedStepCircuitIO<E>,
  accs_hash: Vec<AllocatedNum<E::Scalar>>,
  acc_cf: AllocatedSecondaryRelaxedR1CSInstance<E>,
}

impl<E: CurveCycleEquipped> AllocatedVerifierState<E> {
  pub fn alloc_unverified<CS>(mut cs: CS, state: &VerifierState<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // Previous state of the transcript
    let transcript_state =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc transcript_state"), || {
        state.transcript_state
      });

    // Step Circuit IO
    let io = AllocatedStepCircuitIO::alloc(cs.namespace(|| "alloc io"), &state.io);

    // Allocate hashes of R1CS accumulators. If the accumulator has not been initialized yet,
    // we define it as 0.
    let accs_hash = enumerate(&state.accs_hash)
      .map(|(i, acc_hash)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc acc_hash {i}")), || *acc_hash)
      })
      .collect();

    // Allocate the CycleFold accumulator, without checking
    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::alloc_unchecked(
      cs.namespace(|| "alloc acc_cf"),
      &state.acc_cf,
    );

    Self {
      transcript_state,
      io,
      accs_hash,
      acc_cf,
    }
  }

  /// Loads a previously proved state from a proof of its correctness.
  pub fn init<CS>(
    mut cs: CS,
    input_state: &VerifierState<E>,
    step_proof: StepProof<E>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let state = Self::alloc_unverified(cs.namespace(|| "alloc"), input_state);
    let state_hash = state.hash(cs.namespace(|| "state hash"), &constants.verifier_state)?;

    // Define the base case as transcript_prev == 0
    let is_base_case: Boolean = {
      let zero = alloc_zero(cs.namespace(|| "alloc zero"));
      Boolean::from(alloc_num_equals(
        cs.namespace(|| "transcript_state == 0"),
        &state.transcript_state,
        &zero,
      )?)
    };

    // Step Circuit IO
    // Enforce that the current IO is trivial, i.e. io.in == io.out
    state.io.enforce_trivial(
      cs.namespace(|| "is_base_case => (io.in == io.out)"),
      &is_base_case,
    );

    let mut transcript = AllocatedTranscript::new(
      constants.transcript.clone(),
      [state_hash.clone()],
      step_proof.transcript_buffer,
    );

    // Get the hash of the accumulator being updated
    let acc_hash_curr = transcript.read_scalar(cs.namespace(|| "acc_hash_curr"))?;

    // Create selector for acc_hash_curr and ensure it is contained in accs_hash
    let accs_hash_selector = {
      let bits = state
        .accs_hash
        .iter()
        .enumerate()
        .map(|(i, acc_hash)| {
          let mut cs = cs.namespace(|| format!("accs_hash_selector[{i}]"));
          // Allocate a bit which is true if i == index_prev
          // If index_prev = None, always allocate false
          let bit = step_proof.index.map_or(false, |index_prev| index_prev == i);
          let bit = AllocatedBit::alloc(cs.namespace(|| "alloc selector"), Some(bit)).unwrap();

          // Ensure acc_hash[index] = acc_hash_curr
          cs.enforce(
            || "bit * (acc_hash - acc_hash_curr) = 0",
            |lc| lc + bit.get_variable(),
            |lc| lc + acc_hash.get_variable() - acc_hash_curr.get_variable(),
            |lc| lc,
          );

          Boolean::from(bit)
        })
        .collect::<Vec<_>>();

      // Ensure only 1 selection bit is true, except in the base case where all bits are 0
      let bits_sum = bits.iter().fold(LinearCombination::zero(), |lc, bit| {
        lc + &bit.lc(CS::one(), E::Scalar::ONE)
      });
      cs.enforce(
        || "is_base.not = ∑_i bits[i]",
        |lc| lc,
        |lc| lc,
        |_| is_base_case.not().lc(CS::one(), E::Scalar::ONE) - &bits_sum,
      );

      bits
    };

    // "dereference" the hash of the accumulator
    let mut acc = AllocatedRelaxedR1CSInstance::alloc_from_hash(
      cs.namespace(|| "alloc acc"),
      &acc_hash_curr,
      &step_proof.acc,
      &constants.primary_r1cs,
    )?;

    // Initialize scalar mul accumulator for folding
    let mut acc_sm = AllocatedScalarMulAccumulator::new();

    // Set the R1CS IO as the transcript init followed by the state
    let X_new = state_hash;
    acc.fold(
      cs.namespace(|| "fold"),
      &X_new,
      &mut acc_sm,
      &mut transcript,
      &is_base_case,
    )?;
    let acc_hash_next = acc.hash(
      cs.namespace(|| "hash acc_hash_next"),
      &constants.primary_r1cs,
    )?;

    // Update hashes of accumulators in state
    let accs_hash = zip_eq(state.accs_hash, &accs_hash_selector)
      .enumerate()
      .map(|(i, (acc_hash, bit))| {
        let cs = cs.namespace(|| format!("acc_next_hash[{i}]"));
        conditionally_select(cs, &acc_hash_next, &acc_hash, bit)
      })
      .collect::<Result<Vec<_>, _>>()?;

    // Prove all scalar multiplication by updating the secondary curve accumulator
    // If this is the first iteration, then reset `acc_cf` to its default state since no scalar multiplications
    // were actually computed
    let acc_cf = acc_sm.finalize(
      cs.namespace(|| "finalize acc_sm"),
      state.acc_cf,
      &mut transcript,
    )?;
    let acc_cf = acc_cf.select_default(cs.namespace(|| "enforce trivial acc_cf"), &is_base_case)?;

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
    input_L: &VerifierState<E>,
    input_R: &VerifierState<E>,
    proof: MergeProof<E>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // Verify L
    let self_L = Self::init(
      cs.namespace(|| "alloc state_L"),
      input_L,
      proof.step_proof_L,
      constants,
    )?;
    let accs_L = self_L.load_accs(cs.namespace(|| "load accs_L"), &proof.accs_L, constants)?;

    // Verify R
    let self_R = Self::init(
      cs.namespace(|| "alloc state_R"),
      input_R,
      proof.step_proof_R,
      constants,
    )?;
    let accs_R = self_R.load_accs(cs.namespace(|| "load accs_R"), &proof.accs_R, constants)?;

    let mut transcript = AllocatedTranscript::new(
      constants.transcript.clone(),
      [self_L.transcript_state, self_R.transcript_state],
      proof.transcript_buffer,
    );

    let io = AllocatedStepCircuitIO::merge(cs.namespace(|| "io merge"), self_L.io, self_R.io);

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

  fn load_accs<'a, CS>(
    &self,
    mut cs: CS,
    accs: impl IntoIterator<Item = &'a RelaxedR1CSInstance<E>>,
    constants: &NIVCPoseidonConstants<E>,
  ) -> Result<Vec<AllocatedRelaxedR1CSInstance<E>>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    E: 'a,
  {
    zip_eq(accs, &self.accs_hash)
      .enumerate()
      .map(|(i, (acc_native, acc_hash))| {
        let cs = cs.namespace(|| format!("load acc {i}"));
        AllocatedRelaxedR1CSInstance::alloc_from_hash(
          cs,
          acc_hash,
          acc_native,
          &constants.primary_r1cs,
        )
      })
      .collect()
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

    let state = VerifierState::<E>::dummy(arity, num_circuits, &constants);
    let dummy_proof = StepProof::<E>::dummy();
    let _ = state.synthesize_step(
      cs.namespace(|| "step"),
      dummy_proof,
      &nc.primary_circuit(0),
      &constants,
    );

    expect!["18698"].assert_eq(&cs.num_constraints().to_string());

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

    let state_L = VerifierState::<E>::dummy(arity, num_circuits, &constants);
    let state_R = VerifierState::<E>::dummy(arity, num_circuits, &constants);
    let merge_proof = MergeProof::<E>::dummy(num_circuits);
    let _ = VerifierState::synthesize_merge(
      cs.namespace(|| "merge"),
      &state_L,
      &state_R,
      merge_proof,
      &constants,
    );

    expect!["67675"].assert_eq(&cs.num_constraints().to_string());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
