use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use itertools::zip_eq;

use crate::gadgets::utils::{alloc_num_equals, alloc_zero};
use crate::parafold::cycle_fold::circuit::{
  AllocatedScalarMulAccumulator, AllocatedScalarMulMergeProof,
};
use crate::parafold::nifs_primary::circuit::{
  AllocatedFoldProof, AllocatedMergeProof, AllocatedRelaxedR1CSInstance,
};
use crate::parafold::nivc::prover::NIVCIO;
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::circuit_supernova::EnforcingStepCircuit;
use crate::traits::{Engine, ROConstantsCircuit};

/// The input and output of a NIVC computation over one or more steps.
///
/// # Note
/// - An IO result is trivial if {pc, z}_in == {pc, z}_out
#[derive(Debug, Clone)]
pub struct AllocatedNIVCIO<F: PrimeField> {
  pc_in: AllocatedNum<F>,
  z_in: Vec<AllocatedNum<F>>,
  pc_out: AllocatedNum<F>,
  z_out: Vec<AllocatedNum<F>>,
}

/// A representation of a NIVC state, where `io` represents the computations inputs and outputs,
/// and the `accs` are the accumulators for each step function that was used to produce this result.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCState<E1: Engine, E2: Engine> {
  pub io: AllocatedNIVCIO<E1::Scalar>,
  pub accs: Vec<AllocatedRelaxedR1CSInstance<E1>>,
  pub acc_sm: AllocatedScalarMulAccumulator<E1, E2>,
}

/// A proved NIVC step for a particular step function. Can be folded into an existing [`AllocatedNIVCState'].
#[derive(Debug, Clone)]
pub struct AllocatedNIVCStateProof<E1: Engine, E2: Engine> {
  /// Output of the previous step
  pub state: AllocatedNIVCState<E1, E2>,
  /// Inputs of the previous step
  pub hash_input: [AllocatedNum<E1::Scalar>; 2],
  /// Index of the circuits that produced `state`
  pub index: usize,
  /// Proof for folding the previous circuit into `state.accs[index_prev]`
  pub fold_proof: AllocatedFoldProof<E1, E2>,
}

/// A proved NIVC step for a particular step function. Can be folded into an existing [`AllocatedNIVCState'].
#[derive(Debug, Clone)]
pub struct AllocatedNIVCMergeProof<E1: Engine, E2: Engine> {
  /// Proof for merging the scalar multiplication accumulators from two different states.
  sm_merge_proof: AllocatedScalarMulMergeProof<E1, E2>,
  /// Proofs for merging each accumulator in [AllocatedNIVCState.accs] from two different states
  nivc_merge_proofs: Vec<AllocatedMergeProof<E1, E2>>,
}

impl<E1: Engine, E2: Engine<Base = E1::Scalar>> AllocatedNIVCState<E1, E2> {
  /// Compute the hash of the parts of the state
  fn hash<CS>(
    &self,
    mut cs: CS,
    _hasher: &NIVCHasher<E1>,
  ) -> Result<AllocatedNum<E1::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // FIXME: Real hash
    Ok(AllocatedNum::alloc_infallible(
      cs.namespace(|| "alloc hash"),
      || E1::Scalar::ONE,
    ))
  }

  /// Loads a previously proved state from a proof of its correctness.
  ///
  /// # Details
  ///
  ///
  fn from_proof<CS>(
    mut cs: CS,
    hasher: &NIVCHasher<E1>,
    proof: AllocatedNIVCStateProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(Self, AllocatedNum<E1::Scalar>), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // `state_prev` is the output of the previous iteration, that was produced by the circuit
    // at index `index_prev`, where the inputs were `h_L, h_R`.
    // `fold_proof` proves this computation, but also includes auxiliary proof data to update the accumulators
    // in `state_prev`.
    let AllocatedNIVCStateProof {
      state: state_prev,
      hash_input: [h_L, h_R],
      index: index_prev,
      fold_proof,
    } = proof;

    // Handle base case, which is active when `h_L == h_R == 0`.
    {
      let zero = alloc_zero(cs.namespace(|| "alloc zero"));

      let is_init = {
        let h_L_is_zero = alloc_num_equals(cs.namespace(|| "h_L == 0"), &h_L, &zero)?;
        let h_R_is_zero = alloc_num_equals(cs.namespace(|| "h_R == 0"), &h_R, &zero)?;
        AllocatedBit::and(
          cs.namespace(|| "is_init = (h_L == 0) & (h_R == 0)"),
          &h_L_is_zero,
          &h_R_is_zero,
        )?
      };

      // We only need to enforce that the NIVC IO is trivial.
      // We do not need to check that `accs` and `acc_sm` are trivial, the only requirement is that they are
      // valid RelaxedR1CS accumulators. In practice, we do actually supply trivial accumulators.
      state_prev
        .io
        .enforce_trivial(cs.namespace(|| "is_init => (io.in == io.out)"), &is_init);
    }

    // The actual public output of the circuit is the hash of `state_prev`,
    // so we recompute it to derive the full R1CS IO `X_prev`
    let h_prev = state_prev.hash(cs.namespace(|| "hash_prev"), hasher)?;

    // Manually add the R1CS IO to the transcript to bind the inputs
    let X_prev = vec![h_L.clone(), h_R.clone(), h_prev.clone()];
    for x_prev in &X_prev {
      transcript.absorb(x_prev);
    }

    let AllocatedNIVCState {
      io: io_prev,
      accs: accs_prev,
      acc_sm: acc_sm_prev,
    } = state_prev;

    // FIXME: Use selector
    // let index = io_new.program_counter();
    // let selector = AllocatedSelector::new(index, accs_curr.len());
    // let acc_curr = selector.get(accs)
    let acc_prev = accs_prev[index_prev].clone();

    let (acc_curr, acc_sm_curr) = acc_prev.fold(
      cs.namespace(|| "fold"),
      X_prev,
      acc_sm_prev,
      fold_proof,
      transcript,
    )?;

    // let accs_next = selector.update(acc_curr);
    let mut accs_curr = accs_prev.clone();
    accs_curr[index_prev] = acc_curr;

    let nivc_curr = Self {
      io: io_prev,
      accs: accs_curr,
      acc_sm: acc_sm_curr,
    };

    Ok((nivc_curr, h_prev))
  }

  pub fn new_step<CS, SF>(
    mut cs: CS,
    hasher: &NIVCHasher<E1>,
    proof: AllocatedNIVCStateProof<E1, E2>,
    step_circuit: SF,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
    SF: EnforcingStepCircuit<E1::Scalar>,
  {
    // Fold proof for previous state
    let (nivc_curr, hash_prev) =
      Self::from_proof(cs.namespace(|| "verify self"), hasher, proof, transcript)?;

    let AllocatedNIVCState {
      io: io_prev,
      accs,
      acc_sm,
    } = nivc_curr;

    let AllocatedNIVCIO {
      pc_in: pc_init,
      z_in: z_init,
      pc_out: pc_prev,
      z_out: z_prev,
    } = io_prev;

    // Run the step circuit
    let (pc_next, z_next) = {
      let cs_step = &mut cs.namespace(|| "synthesize");

      let (pc_next, z_next) = step_circuit.synthesize(cs_step, Some(&pc_prev), &z_prev)?;
      let pc_next = pc_next.ok_or(SynthesisError::AssignmentMissing)?;
      (pc_next, z_next)
    };

    // Set the new IO state
    let io_next = AllocatedNIVCIO {
      pc_in: pc_init,
      z_in: z_init,
      pc_out: pc_next,
      z_out: z_next,
    };

    // Define output state
    let nivc_next = AllocatedNIVCState {
      io: io_next,
      accs,
      acc_sm,
    };

    // For succinctness, we only output the hash of the next state
    let hash_next = nivc_next.hash(cs.namespace(|| "hash nivc_next"), hasher)?;

    // To ensure both step and merge circuits have the same IO, we inputize the previous output twice
    hash_prev.inputize(cs.namespace(|| "inputize hash_prev"))?;
    hash_prev.inputize(cs.namespace(|| "inputize hash_prev"))?;
    hash_next.inputize(cs.namespace(|| "inputize hash_next"))?;

    Ok(nivc_next)
  }

  /// Circuit
  pub fn new_merge<CS>(
    mut cs: CS,
    hasher: &NIVCHasher<E1>,
    proof_L: AllocatedNIVCStateProof<E1, E2>,
    proof_R: AllocatedNIVCStateProof<E1, E2>,
    merge_proof: AllocatedNIVCMergeProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    //
    let (nivc_L, hash_L_prev) = Self::from_proof(
      cs.namespace(|| "verify proof_L"),
      hasher,
      proof_L,
      transcript,
    )?;
    let (nivc_R, hash_R_prev) = Self::from_proof(
      cs.namespace(|| "verify proof_R"),
      hasher,
      proof_R,
      transcript,
    )?;

    let AllocatedNIVCState {
      io: io_L,
      accs: accs_L,
      acc_sm: acc_sm_L,
    } = nivc_L;
    let AllocatedNIVCState {
      io: io_R,
      accs: accs_R,
      acc_sm: acc_sm_R,
    } = nivc_R;

    let AllocatedNIVCMergeProof {
      sm_merge_proof,
      nivc_merge_proofs,
    } = merge_proof;

    let acc_sm_merge = acc_sm_L.merge(
      cs.namespace(|| "merge acc_sm_L acc_sm_R"),
      acc_sm_R,
      sm_merge_proof,
      transcript,
    )?;

    // merge the accumulators from both states.
    let (accs_next, acc_sm_next) = AllocatedRelaxedR1CSInstance::merge_many(
      cs.namespace(|| "merge many"),
      accs_L,
      accs_R,
      acc_sm_merge,
      nivc_merge_proofs,
      transcript,
    )?;

    let io_next = io_L.merge(cs.namespace(|| "merge io"), io_R)?;

    let nivc_next = Self {
      io: io_next,
      accs: accs_next,
      acc_sm: acc_sm_next,
    };
    let hash_next = nivc_next.hash(cs.namespace(|| "hash nivc_next"), hasher)?;

    // Set public IO to be the hashes of the two input states, and the hash of the next state
    hash_L_prev.inputize(cs.namespace(|| "inputize hash_L_prev"))?;
    hash_R_prev.inputize(cs.namespace(|| "inputize hash_R_prev"))?;
    hash_next.inputize(cs.namespace(|| "inputize hash_next"))?;

    Ok(nivc_next)
  }
}

impl<F: PrimeField> AllocatedNIVCIO<F> {
  pub fn alloc_infallible<CS, N>(mut cs: CS, state: N) -> Self
  where
    CS: ConstraintSystem<F>,
    N: FnOnce() -> NIVCIO<F>,
  {
    let NIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    } = state();

    let pc_in =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_in"), || F::from(pc_in as u64));
    let z_in = z_in
      .into_iter()
      .enumerate()
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || z)
      })
      .collect();
    let pc_out =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_out"), || F::from(pc_out as u64));
    let z_out = z_out
      .into_iter()
      .enumerate()
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_out[{i}]")), || z)
      })
      .collect();

    Self {
      pc_in,
      z_in,
      pc_out,
      z_out,
    }
  }

  pub fn merge<CS>(self, mut cs: CS, other: Self) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<F>,
  {
    // self.pc_out = other.pc_in
    cs.enforce(
      || "self.pc_out = other.pc_in",
      |lc| lc,
      |lc| lc,
      |lc| lc + self.pc_out.get_variable() - other.pc_in.get_variable(),
    );

    // self.z_out = other.z_in
    zip_eq(&self.z_out, &other.z_in)
      .enumerate()
      .for_each(|(i, (z_L_i, z_R_i))| {
        cs.enforce(
          || format!("self.z_out[{i}] = other.z_in[{i}]"),
          |lc| lc,
          |lc| lc,
          |lc| lc + z_L_i.get_variable() - z_R_i.get_variable(),
        );
      });

    Ok(Self {
      pc_in: self.pc_in,
      z_in: self.z_in,
      pc_out: other.pc_out,
      z_out: other.z_out,
    })
  }

  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &AllocatedBit)
  where
    CS: ConstraintSystem<F>,
  {
    // (is_trivial) * (pc_in - pc_out) = 0
    cs.enforce(
      || "(is_trivial) * (pc_in - pc_out) = 0",
      |lc| lc + is_trivial.get_variable(),
      |lc| lc + self.pc_in.get_variable() - self.pc_out.get_variable(),
      |lc| lc,
    );

    // (is_trivial) * (z_in - z_out) = 0
    zip_eq(&self.z_in, &self.z_out)
      .enumerate()
      .for_each(|(i, (z_in_i, z_out_i))| {
        cs.enforce(
          || format!("(is_trivial) * (z_in[{i}] - z_out[{i}]) = 0"),
          |lc| lc + is_trivial.get_variable(),
          |lc| lc + z_in_i.get_variable() - z_out_i.get_variable(),
          |lc| lc,
        );
      });
  }
}

pub struct NIVCHasher<E: Engine> {
  ro_consts: ROConstantsCircuit<E>,
  pp: AllocatedNum<E::Scalar>,
  arity: usize,
}

impl<E: Engine> NIVCHasher<E> {
  pub fn new(ro_consts: ROConstantsCircuit<E>, pp: AllocatedNum<E::Scalar>, arity: usize) -> Self {
    Self {
      ro_consts,
      pp,
      arity,
    }
  }
}
