use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use itertools::zip_eq;

use crate::gadgets::utils::{alloc_num_equals, alloc_zero};
use crate::parafold::cycle_fold::AllocatedScalarMulAccumulator;
use crate::parafold::nifs_primary::AllocatedRelaxedR1CSInstance;
use crate::parafold::nivc::{
  AllocatedNIVCIO, AllocatedNIVCMergeProof, AllocatedNIVCState, AllocatedNIVCStateProof,
};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::traits::circuit_supernova::EnforcingStepCircuit;
use crate::traits::{Engine, ROConstantsCircuit};

impl<E1, E2> AllocatedNIVCState<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
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
  ) -> Result<
    (
      AllocatedNIVCIO<E1::Scalar>,
      Vec<AllocatedRelaxedR1CSInstance<E1>>,
      AllocatedScalarMulAccumulator<E1, E2>,
      AllocatedNum<E1::Scalar>,
    ),
    SynthesisError,
  >
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // `state_prev` is the output of the previous iteration, that was produced by the circuit
    // at index `index_prev`, where the inputs were `h_L, h_R`.
    // `fold_proof` proves this computation, but also includes auxiliary proof data to update the accumulators
    // in `state_prev`.
    let AllocatedNIVCStateProof {
      state: state_prev,
      index: index_prev,
      fold_proof,
    } = proof;

    // The actual public output of the circuit is the hash of `state_prev`,
    // so we recompute it to derive the full R1CS IO `X_prev`
    let h_prev = state_prev.hash(cs.namespace(|| "hash_prev"), hasher)?;

    let AllocatedNIVCState {
      hash_input: [h_L, h_R],
      io,
      accs: accs_prev,
      mut acc_sm,
    } = state_prev;

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
      io.enforce_trivial(cs.namespace(|| "is_init => (io.in == io.out)"), &is_init);
    }

    // Manually add the R1CS IO to the transcript to bind the inputs
    let X_prev = vec![h_prev.clone()];
    for x_prev in &X_prev {
      transcript.absorb(x_prev);
    }

    // FIXME: Use selector
    // let index = io_new.program_counter();
    // let selector = AllocatedSelector::new(index, accs_curr.len());
    // let acc_curr = selector.get(accs)
    let mut acc = accs_prev[index_prev].clone();

    acc.fold(
      cs.namespace(|| "fold"),
      X_prev,
      &mut acc_sm,
      fold_proof,
      transcript,
    )?;

    // let accs_next = selector.update(acc_curr);
    let mut accs_next = accs_prev.clone();
    accs_next[index_prev] = acc;

    Ok((io, accs_next, acc_sm, h_prev))
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
    let (io_prev, accs_next, acc_sm_next, hash_prev) =
      Self::from_proof(cs.namespace(|| "verify self"), hasher, proof, transcript)?;

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
      hash_input: [hash_prev.clone(), hash_prev],
      io: io_next,
      accs: accs_next,
      acc_sm: acc_sm_next,
    };

    // For succinctness, we only output the hash of the next state
    let hash_next = nivc_next.hash(cs.namespace(|| "hash nivc_next"), hasher)?;

    // To ensure both step and merge circuits have the same IO, we inputize the previous output twice
    hash_next.inputize(cs.namespace(|| "inputize hash_next"))?;

    Ok(nivc_next)
  }

  /// Circuit
  pub fn new_merge<CS>(
    mut cs: CS,
    hasher: &NIVCHasher<E1>,
    proof: AllocatedNIVCMergeProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let AllocatedNIVCMergeProof {
      proof_L,
      proof_R,
      sm_merge_proof,
      nivc_merge_proofs,
    } = proof;

    //
    let (io_L_prev, accs_L_next, acc_sm_L_next, hash_L_prev) = Self::from_proof(
      cs.namespace(|| "verify proof_L"),
      hasher,
      proof_L,
      transcript,
    )?;
    let (io_R_prev, accs_R_next, acc_sm_R_next, hash_R_prev) = Self::from_proof(
      cs.namespace(|| "verify proof_R"),
      hasher,
      proof_R,
      transcript,
    )?;

    let mut acc_sm_next = AllocatedScalarMulAccumulator::merge(
      cs.namespace(|| "merge acc_sm_L acc_sm_R"),
      acc_sm_L_next,
      acc_sm_R_next,
      sm_merge_proof,
      transcript,
    )?;

    // merge the accumulators from both states.
    let accs_next = AllocatedRelaxedR1CSInstance::merge_many(
      cs.namespace(|| "merge many"),
      accs_L_next,
      accs_R_next,
      &mut acc_sm_next,
      nivc_merge_proofs,
      transcript,
    )?;

    let io_next = io_L_prev.merge(cs.namespace(|| "merge io"), io_R_prev)?;

    let nivc_next = Self {
      hash_input: [hash_L_prev, hash_R_prev],
      io: io_next,
      accs: accs_next,
      acc_sm: acc_sm_next,
    };
    let hash_next = nivc_next.hash(cs.namespace(|| "hash nivc_next"), hasher)?;

    hash_next.inputize(cs.namespace(|| "inputize hash_next"))?;

    Ok(nivc_next)
  }
}

impl<F: PrimeField> AllocatedNIVCIO<F> {
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
