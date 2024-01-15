use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use itertools::{chain, zip_eq};
use pairing::Engine;

use crate::gadgets::utils::{alloc_num_equals, alloc_zero};
use crate::parafold::circuit::nifs::{
  AllocatedProof, AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance,
};
use crate::parafold::circuit::scalar_mul::{
  AllocatedCommitment, AllocatedScalarMulAccumulator, AllocatedScalarMulFoldProof,
  AllocatedScalarMulInstance, AllocatedScalarMulMergeProof,
};
use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::nivc::NIVCIO;
use crate::traits::circuit_supernova::EnforcingStepCircuit;
use crate::zip_with;

/// The input and output of a NIVC computation over one or more steps.
///
/// # Note
/// - An IO result is trivial if {pc, z}_in == {pc, z}_out
#[derive(Debug, Clone)]
pub(crate) struct AllocatedNIVCIO<F: PrimeField> {
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
  hash_input_prev: [AllocatedNum<E::Scalar>; 2],
  /// Proof of circuit that produced `state`
  W: AllocatedCommitment<E>,
  /// Index of the circuits that produced `state`
  index_prev: usize,
  /// Proof for folding the previous circuit into `state.accs[index_prev]`
  fold_proof: AllocatedProof<E>,
}

/// A proved NIVC step for a particular step function. Can be folded into an existing [`AllocatedNIVCState'].
#[derive(Debug, Clone)]
pub struct AllocatedNIVCMergeProof<E: Engine> {
  /// Proofs for merging each accumulator in [AllocatedNIVCState.accs] from two different states
  nivc_merge_proofs: Vec<AllocatedProof<E>>,
  /// Proof for merging the scalar multiplication accumulators from two different states.
  sm_merge_proof: AllocatedScalarMulMergeProof<E>,
}

impl<E: Engine> AllocatedNIVCState<E> {
  fn new<CS>(
    mut cs: CS,
    io: AllocatedNIVCIO<E::Scalar>,
    accs: Vec<AllocatedRelaxedR1CSInstance<E>>,
    acc_sm: AllocatedScalarMulAccumulator<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let hash = Self::hash(cs.namespace(|| "hash"), &io, &accs, &acc_sm)?;
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

  /// Make this state part of the circuit's IO by inputizing the hash.
  fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    self.hash.inputize(cs.namespace(|| "inputize hash"))
  }

  /// Loads a previously proved state from a proof of its correctness
  fn from_proof<CS>(
    mut cs: CS,
    proof: AllocatedNIVCStateProof<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Self, [AllocatedScalarMulInstance<E>; 2]), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let AllocatedNIVCStateProof {
      state,
      hash_input_prev,
      W,
      index_prev,
      fold_proof,
    } = proof;

    let zero = alloc_zero(cs.namespace(|| "alloc zero"));

    let [h_init, h_prev] = hash_input_prev;

    let AllocatedNIVCState {
      io: io_curr,
      accs: accs_prev,
      acc_sm: acc_sm_curr,
      hash: h_curr,
    } = state;

    let X = vec![&h_init, &h_prev, &h_curr];

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

    let (acc_curr, scalar_mul_instances) = acc_prev.fold(
      cs.namespace(|| "fold"),
      r1cs_new,
      fold_proof,
      is_init.into(),
      transcript,
    )?;

    // let accs_next = selector.update(acc_curr);
    let accs_curr = accs_prev.clone();
    accs_curr[index_prev] = acc_curr;

    Ok((
      Self::new(
        cs.namespace(|| "state curr"),
        io_curr,
        accs_curr,
        acc_sm_curr,
      )?,
      scalar_mul_instances,
    ))
  }

  pub fn new_step<CS, SF>(
    mut cs: CS,
    proof: AllocatedNIVCStateProof<E>,
    step_circuit: SF,
    sm_fold_proofs: Vec<AllocatedScalarMulFoldProof<E>>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    SF: EnforcingStepCircuit<E::Scalar>,
  {
    // Fold proof for previous state
    let (nivc_curr, scalar_mul_instances) =
      Self::from_proof(cs.namespace(|| "verify self"), proof, transcript)?;

    // To ensure both step and merge circuits have the same IO, we inputize the previous output twice
    nivc_curr.inputize(cs.namespace(|| "inputize nivc_curr 0"))?;
    nivc_curr.inputize(cs.namespace(|| "inputize nivc_curr 1"))?;

    let AllocatedNIVCState {
      io: io_curr,
      accs: accs_curr,
      acc_sm: acc_sm_curr,
      ..
    } = nivc_curr;

    let AllocatedNIVCIO {
      pc_in: pc_init,
      z_in: z_init,
      pc_out: pc_curr,
      z_out: z_curr,
    } = io_curr;

    let mut cs_step = cs.namespace(|| "synthesize");

    // Run the step circuit
    let (Some(pc_next), z_next) = step_circuit.synthesize(&mut cs_step, Some(&pc_curr), &z_curr)?;

    // Set the new IO state
    let io_next = AllocatedNIVCIO {
      pc_in: pc_init,
      z_in: z_init,
      pc_out: pc_next,
      z_out: z_next,
    };

    // Prove all scalar multiplications
    let acc_sm_next = acc_sm_curr.fold(
      cs.namespace(|| "fold scalar mul proofs"),
      scalar_mul_instances,
      sm_fold_proofs,
    )?;

    // Define output state
    let nivc_next = AllocatedNIVCState::new(
      cs.namespace(|| "state next"),
      io_next,
      accs_curr,
      acc_sm_next,
    )?;

    // Set public output to be `nivc_next`
    nivc_next.inputize(cs.namespace(|| "inputize hash_curr"))?;

    Ok(nivc_next)
  }

  /// Circuit
  pub fn new_merge<CS>(
    mut cs: CS,
    proof_L: AllocatedNIVCStateProof<E>,
    proof_R: AllocatedNIVCStateProof<E>,
    // one proof for each accumulator
    merge_proof: AllocatedNIVCMergeProof<E>,
    sm_fold_proofs: Vec<AllocatedScalarMulFoldProof<E>>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let (nivc_L, scalar_mul_instances_L) =
      Self::from_proof(cs.namespace(|| "verify proof_L"), proof_L, transcript)?;
    nivc_L.inputize(cs.namespace(|| "inputize nivc_L"))?;
    let (nivc_R, scalar_mul_instances_R) =
      Self::from_proof(cs.namespace(|| "verify proof_R"), proof_R, transcript)?;
    nivc_R.inputize(cs.namespace(|| "inputize nivc_R"))?;

    let AllocatedNIVCState {
      io: io_L,
      accs: accs_L,
      acc_sm: acc_sm_L,
      ..
    } = nivc_L;
    let AllocatedNIVCState {
      io: io_R,
      accs: accs_R,
      acc_sm: acc_sm_R,
      ..
    } = nivc_R;

    let AllocatedNIVCMergeProof {
      nivc_merge_proofs,
      sm_merge_proof,
    } = merge_proof;

    let num_accs = nivc_merge_proofs.len();

    let mut scalar_mul_instances_merge = Vec::with_capacity(3 * num_accs);

    // merge the accumulators from both states.
    let accs_next = zip_with!(
      (accs_L, accs_R, nivc_merge_proofs.into_iter().enumerate()),
      |acc_L, acc_R, fold_proof_i| {
        let (i, fold_proof) = fold_proof_i;
        let (acc_next, scalar_mul_instances) = acc_L.merge(
          cs.namespace(|| format!("merge acc_L[{i}] acc_R[{i}]")),
          acc_R,
          fold_proof,
          transcript,
        )?;

        scalar_mul_instances_merge.extend(scalar_mul_instances);

        Ok(acc_next)
      }
    )
    .collect::<Result<Vec<_>, _>>()?;

    let acc_sm_merge = acc_sm_L.merge(
      cs.namespace(|| "merge acc_sm_L acc_sm_R"),
      acc_sm_R,
      sm_merge_proof,
      transcript,
    )?;

    let io_next = io_L.merge(cs.namespace(|| "merge io"), io_R)?;

    let scalar_mul_instances = chain!(
      scalar_mul_instances_L,
      scalar_mul_instances_R,
      scalar_mul_instances_merge
    );

    let acc_sm_next = acc_sm_merge.fold(
      cs.namespace(|| "fold scalar_mul_instances"),
      scalar_mul_instances,
      sm_fold_proofs,
      transcript,
    )?;

    let nivc_next = Self::new(
      cs.namespace(|| "state merge"),
      io_next,
      accs_next,
      acc_sm_next,
    )?;
    nivc_next.inputize(cs.namespace(|| "inputize nivc_next"))?;

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
      |lc| self.pc_out.get_variable() - other.pc_in.get_variable(),
    );

    // self.z_out = other.z_in
    zip_eq(&self.z_out, &other.z_in)
      .enumerate()
      .for_each(|(i, (z_L_i, z_R_i))| {
        cs.enforce(
          || format!("self.z_out[{i}] = other.z_in[{i}]"),
          |lc| lc,
          |lc| lc,
          |lc| z_L_i.get_variable() - z_R_i.get_variable(),
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

  pub fn X(&self) -> Vec<&AllocatedNum<F>> {
    let AllocatedNIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    } = self;

    chain!([pc_in], z_in.iter(), [pc_out], z_out.iter()).collect()
  }

  pub fn program_counter(&self) -> AllocatedNum<F> {
    self.pc_in.clone()
  }
}
