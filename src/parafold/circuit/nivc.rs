use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use itertools::zip_eq;

use crate::gadgets::utils::{alloc_num_equals, alloc_zero};
use crate::parafold::circuit::nifs::{
  AllocatedFoldProof, AllocatedMergeProof, AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance,
};
use crate::parafold::circuit::scalar_mul::{
  AllocatedCommitment, AllocatedScalarMulAccumulator, AllocatedScalarMulMergeProof,
};
use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::nivc::{NIVCStateInstance, NIVCStateProof, NIVCIO};
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
pub struct AllocatedNIVCState<E: Engine> {
  io: AllocatedNIVCIO<E::Scalar>,
  accs: Vec<AllocatedRelaxedR1CSInstance<E>>,
  acc_sm: AllocatedScalarMulAccumulator<E>,
  /// hash = H(accs, acc_sm, io)
  hash: AllocatedNum<E::Scalar>,
}

/// A proved NIVC step for a particular step function. Can be folded into an existing [`AllocatedNIVCState'].
#[derive(Debug, Clone)]
pub struct AllocatedNIVCStateProof<E: Engine> {
  /// Output of the previous step
  state: AllocatedNIVCState<E>,
  /// Inputs of the previous step
  hash_input: [AllocatedNum<E::Scalar>; 2],
  /// Proof of circuit that produced `state`
  W: AllocatedCommitment<E>,
  /// Index of the circuits that produced `state`
  index: usize,
  /// Proof for folding the previous circuit into `state.accs[index_prev]`
  fold_proof: AllocatedFoldProof<E>,
}

/// A proved NIVC step for a particular step function. Can be folded into an existing [`AllocatedNIVCState'].
#[derive(Debug, Clone)]
pub struct AllocatedNIVCMergeProof<E: Engine> {
  /// Proof for merging the scalar multiplication accumulators from two different states.
  sm_merge_proof: AllocatedScalarMulMergeProof<E>,
  /// Proofs for merging each accumulator in [AllocatedNIVCState.accs] from two different states
  nivc_merge_proofs: Vec<AllocatedMergeProof<E>>,
}

impl<E: Engine> AllocatedNIVCState<E> {
  fn new<CS>(
    mut cs: CS,
    hasher: &NIVCHasher<E>,
    io: AllocatedNIVCIO<E::Scalar>,
    accs: Vec<AllocatedRelaxedR1CSInstance<E>>,
    acc_sm: AllocatedScalarMulAccumulator<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let hash = Self::hash(cs.namespace(|| "hash"), hasher, &io, &accs, &acc_sm)?;
    Ok(Self {
      io,
      accs,
      acc_sm,
      hash,
    })
  }

  /// Compute the hash of the parts of the state
  fn hash<CS>(
    mut cs: CS,
    _hasher: &NIVCHasher<E>,
    _io: &AllocatedNIVCIO<E::Scalar>,
    _accs: &[AllocatedRelaxedR1CSInstance<E>],
    _acc_sm: &AllocatedScalarMulAccumulator<E>,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // FIXME: Real hash
    Ok(AllocatedNum::alloc_infallible(
      cs.namespace(|| "alloc hash"),
      || E::Scalar::ONE,
    ))
  }

  /// Loads a previously proved state from a proof of its correctness
  fn from_proof<CS>(
    mut cs: CS,
    hasher: &NIVCHasher<E>,
    proof: AllocatedNIVCStateProof<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let AllocatedNIVCStateProof {
      state,
      hash_input: hash_input_prev,
      W,
      index: index_prev,
      fold_proof,
    } = proof;

    let zero = alloc_zero(cs.namespace(|| "alloc zero"));

    let [h_init, h_prev] = hash_input_prev;

    let AllocatedNIVCState {
      io: io_curr,
      accs: accs_prev,
      acc_sm: acc_sm_prev,
      hash: h_curr,
    } = state;

    let X = vec![h_init.clone(), h_prev.clone(), h_curr];

    let is_init = {
      let h_init_is_zero = alloc_num_equals(cs.namespace(|| "h_init == 0"), &h_init, &zero)?;
      let h_prev_is_zero = alloc_num_equals(cs.namespace(|| "h_prev == 0"), &h_prev, &zero)?;
      AllocatedBit::and(
        cs.namespace(|| "is_init = (h_init == 0) & (h_prev == 0)"),
        &h_init_is_zero,
        &h_prev_is_zero,
      )?
    };

    io_curr.enforce_trivial(
      cs.namespace(|| "is_init => (io_curr.in == io_curr.out)"),
      &is_init,
    );

    // FIXME: replace with actual logic
    // If base-case, then there isn't any proof for the previous iteration,
    // so we enforce
    let r1cs_new = AllocatedR1CSInstance::new(X, W);

    // FIXME: Use selector
    // let index = io_new.program_counter();
    // let selector = AllocatedSelector::new(index, accs_curr.len());
    // let acc_curr = selector.get(accs)
    let acc_prev = accs_prev[index_prev].clone();

    let (acc_curr, acc_sm_curr) = acc_prev.fold(
      cs.namespace(|| "fold"),
      r1cs_new,
      acc_sm_prev,
      fold_proof,
      transcript,
    )?;

    // let accs_next = selector.update(acc_curr);
    let mut accs_curr = accs_prev.clone();
    accs_curr[index_prev] = acc_curr;

    Ok(Self::new(
      cs.namespace(|| "state curr"),
      hasher,
      io_curr,
      accs_curr,
      acc_sm_curr,
    )?)
  }

  pub fn new_step<CS, SF>(
    mut cs: CS,
    hasher: &NIVCHasher<E>,
    proof: AllocatedNIVCStateProof<E>,
    step_circuit: SF,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    SF: EnforcingStepCircuit<E::Scalar>,
  {
    // Fold proof for previous state
    let nivc_curr = Self::from_proof(cs.namespace(|| "verify self"), hasher, proof, transcript)?;

    let AllocatedNIVCState {
      io: io_curr,
      accs: accs_curr,
      acc_sm: acc_sm_curr,
      hash: hash_curr,
    } = nivc_curr;

    let AllocatedNIVCIO {
      pc_in: pc_init,
      z_in: z_init,
      pc_out: pc_curr,
      z_out: z_curr,
    } = io_curr;

    let (pc_next, z_next) = {
      let cs_step = &mut cs.namespace(|| "synthesize");

      // Run the step circuit
      let (pc_next, z_next) = step_circuit.synthesize(cs_step, Some(&pc_curr), &z_curr)?;
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
    let nivc_next = AllocatedNIVCState::new(
      cs.namespace(|| "state next"),
      hasher,
      io_next,
      accs_curr,
      acc_sm_curr,
    )?;

    // To ensure both step and merge circuits have the same IO, we inputize the previous output twice
    hash_curr.inputize(cs.namespace(|| "inputize hash_curr"))?;
    hash_curr.inputize(cs.namespace(|| "inputize hash_curr"))?;
    nivc_next
      .hash
      .inputize(cs.namespace(|| "inputize hash_next"))?;

    Ok(nivc_next)
  }

  /// Circuit
  pub fn new_merge<CS>(
    mut cs: CS,
    hasher: &NIVCHasher<E>,
    proof_L: AllocatedNIVCStateProof<E>,
    proof_R: AllocatedNIVCStateProof<E>,
    merge_proof: AllocatedNIVCMergeProof<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let nivc_L = Self::from_proof(
      cs.namespace(|| "verify proof_L"),
      hasher,
      proof_L,
      transcript,
    )?;
    let nivc_R = Self::from_proof(
      cs.namespace(|| "verify proof_R"),
      hasher,
      proof_R,
      transcript,
    )?;

    let AllocatedNIVCState {
      io: io_L,
      accs: accs_L,
      acc_sm: acc_sm_L,
      hash: hash_L,
    } = nivc_L;
    let AllocatedNIVCState {
      io: io_R,
      accs: accs_R,
      acc_sm: acc_sm_R,
      hash: hash_R,
    } = nivc_R;

    let AllocatedNIVCMergeProof {
      sm_merge_proof,
      nivc_merge_proofs,
    } = merge_proof;

    let acc_sm = acc_sm_L.merge(
      cs.namespace(|| "merge acc_sm_L acc_sm_R"),
      acc_sm_R,
      sm_merge_proof,
      transcript,
    )?;

    // merge the accumulators from both states.
    let (accs_next, acc_sm) = AllocatedRelaxedR1CSInstance::merge_many(
      cs.namespace(|| "merge many"),
      accs_L,
      accs_R,
      acc_sm,
      nivc_merge_proofs,
      transcript,
    )?;

    let io_next = io_L.merge(cs.namespace(|| "merge io"), io_R)?;

    let nivc_next = Self::new(
      cs.namespace(|| "state merge"),
      hasher,
      io_next,
      accs_next,
      acc_sm,
    )?;

    // Set public IO to be the hashes of the two input states, and the hash of the next state
    hash_L.inputize(cs.namespace(|| "inputize hash_L"))?;
    hash_R.inputize(cs.namespace(|| "inputize hash_R"))?;
    nivc_next
      .hash
      .inputize(cs.namespace(|| "inputize hash_next"))?;

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

impl<E: Engine> AllocatedNIVCState<E> {
  pub fn alloc<CS, F>(mut cs: CS, hasher: &NIVCHasher<E>, state: F) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> NIVCStateInstance<E>,
  {
    let NIVCStateInstance { io, accs, acc_sm } = state();

    let io = AllocatedNIVCIO::alloc_infallible(cs.namespace(|| "alloc io"), || io);
    let accs = accs
      .into_iter()
      .enumerate()
      .map(|(i, acc)| {
        AllocatedRelaxedR1CSInstance::alloc_infallible(
          cs.namespace(|| format!("alloc acc[{i}]")),
          || acc,
        )
      })
      .collect();
    let acc_sm =
      AllocatedScalarMulAccumulator::alloc_infallible(cs.namespace(|| "alloc W"), || acc_sm);

    // TODO: unwrap
    Self::new(
      cs.namespace(|| "instance with hash"),
      hasher,
      io,
      accs,
      acc_sm,
    )
  }
}

impl<E: Engine> AllocatedNIVCStateProof<E> {
  pub fn alloc<CS, F>(mut cs: CS, hasher: &NIVCHasher<E>, proof: F) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> NIVCStateProof<E>,
  {
    let NIVCStateProof {
      state,
      hash_input,
      W,
      index,
      nifs_fold_proof,
    } = proof();

    let state = AllocatedNIVCState::alloc(cs.namespace(|| "alloc state"), hasher, || state)?;
    let hash_input =
      hash_input.map(|h| AllocatedNum::alloc_infallible(cs.namespace(|| "alloc hash input"), || h));
    let W = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let fold_proof =
      AllocatedFoldProof::alloc_infallible(cs.namespace(|| "alloc fold_proof"), || nifs_fold_proof);

    Ok(Self {
      state,
      hash_input,
      W,
      index,
      fold_proof,
    })
  }
}

pub struct NIVCHasher<E: Engine> {
  ro_consts: ROConstantsCircuit<E>,
  pp: AllocatedNum<E::Scalar>,
  arity: usize,
}
