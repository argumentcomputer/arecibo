use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::Field;
use itertools::{chain, zip_eq};
use neptune::circuit2::{Elt, PoseidonCircuit2};

use crate::gadgets::utils::{alloc_num_equals, alloc_zero, conditionally_select};
use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::cycle_fold::nifs::circuit::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::nifs::circuit::AllocatedRelaxedR1CSInstance;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::nivc::{
  AllocatedNIVCIO, NIVCPoseidonConstants, NIVCStateInstance, NIVCUpdateProof, NIVCIO,
};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::parafold::transcript::TranscriptConstants;
use crate::supernova::EnforcingStepCircuit;
use crate::traits::CurveCycleEquipped;

/// A representation of a NIVC state, where `io` represents the computations inputs and outputs,
/// and the `accs` are the accumulators for each step function that was used to produce this result.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCState<E: CurveCycleEquipped> {
  transcript_init: AllocatedNum<E::Scalar>,
  io: AllocatedNIVCIO<E>,
  accs_hash: Vec<AllocatedNum<E::Scalar>>,
  acc_cf: AllocatedSecondaryRelaxedR1CSInstance<E>,
}

impl<E: CurveCycleEquipped> AllocatedNIVCState<E> {
  /// Loads a previously proved state from a proof of its correctness.
  pub fn from_proof<CS>(
    mut cs: CS,
    ro_consts: &TranscriptConstants<E::Scalar>,
    proof: NIVCUpdateProof<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let NIVCUpdateProof {
      transcript_buffer,
      state,
      acc_prev,
      index_prev,
    } = proof;

    // Allocate inputs
    let state = AllocatedNIVCState::alloc_unchecked(cs.namespace(|| "alloc state"), state);

    // Compute hash of inputs
    let state_hash = state.hash(cs.namespace(|| "state hash"))?;

    let Self {
      transcript_init,
      io,
      accs_hash,
      acc_cf,
    } = state;

    // Initialize transcript with the state of the transcript in the previous iteration
    let mut transcript =
      AllocatedTranscript::new(ro_consts.clone(), [state_hash.clone()], transcript_buffer);

    // Define the base case as transcript_init == 0
    let is_base_case: Boolean = {
      let zero = alloc_zero(cs.namespace(|| "alloc zero"));

      alloc_num_equals(
        cs.namespace(|| "transcript_init == 0"),
        &transcript_init,
        &zero,
      )?
    }
    .into();

    // We only need to enforce that the NIVC IO is trivial.
    // We do not need to check that `accs` and `acc_sm` are trivial, the only requirement is that they are
    // valid RelaxedR1CS accumulators. In practice, we do actually supply trivial accumulators.
    io.enforce_trivial(
      cs.namespace(|| "is_base_case => (io.in == io.out)"),
      &is_base_case,
    );

    acc_cf.enforce_trivial(
      cs.namespace(|| "is_base_case => acc_cf.is_trivial"),
      &is_base_case,
    );

    // Initialize scalar mul accumulator for folding
    let mut acc_sm = AllocatedScalarMulAccumulator::new(acc_cf);

    // Update the set of accumulators with the fresh folding proof
    let accs_hash = Self::update_accs(
      cs.namespace(|| "update accs"),
      accs_hash,
      state_hash,
      acc_prev,
      index_prev,
      &is_base_case,
      &mut acc_sm,
      &mut transcript,
    )?;

    // Prove all scalar multiplication by updating the secondary curve accumulator
    let acc_cf = acc_sm.finalize(cs.namespace(|| "finalize acc_sm"), &mut transcript)?;

    // If this is the first iteration, then reset `acc_cf` to its default state since no scalar multiplications
    // were actually computed
    let acc_cf = acc_cf.select_default(cs.namespace(|| "enforce trivial acc_cf"), &is_base_case)?;

    let transcript_state = transcript.seal(cs.namespace(|| "transcript seal"))?;

    Ok(Self {
      transcript_init: transcript_state,
      io,
      accs_hash,
      acc_cf,
    })
  }

  pub fn update_io<CS, SF>(
    &mut self,
    mut cs: CS,
    step_circuit: &SF,
  ) -> Result<NIVCIO<E>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    SF: EnforcingStepCircuit<E::Scalar>,
  {
    // Run the step circuit
    let cs_step = &mut cs.namespace(|| "synthesize");

    let (pc_curr, z_curr) = (Some(&self.io.pc_out), self.io.z_out.as_slice());

    let (pc_next, z_next) = step_circuit.enforcing_synthesize(cs_step, pc_curr, z_curr)?;

    self.io.pc_out = pc_next.ok_or(SynthesisError::AssignmentMissing)?;
    self.io.z_out = z_next;

    self.io.to_native()
  }

  // pub fn merge<CS>(
  //   mut cs: CS,
  //   self_L: Self,
  //   self_R: Self,
  //   ro_consts: &TranscriptConstants<E::Scalar>,
  //   proof: NIVCMergeProof<E>,
  //   transcript: &mut AllocatedTranscript<E>,
  // ) -> Result<(Self, NIVCIO<E::Scalar>), SynthesisError>
  // where
  //   CS: ConstraintSystem<E::Scalar>,
  // {
  //   let mut acc_sm = AllocatedScalarMulAccumulator::new();
  //
  //   let Self {
  //     io: io_L,
  //     accs_hash: accs_hash_L,
  //     acc_cf: acc_cf_L,
  //   } = self_L;
  //   let Self {
  //     io: io_R,
  //     accs_hash: accs_hash_R,
  //     acc_cf: acc_cf_R,
  //   } = self_R;
  //
  //   let io = AllocatedNIVCIO::merge(cs.namespace(|| "io merge"), io_L, io_R);
  //
  //   // Load the preimages of the accumulators in each state
  //   let (accs_L, accs_R) = {
  //     let accs_L = Self::load_accs(
  //       cs.namespace(|| "load accs_R"),
  //       proof.accs_L,
  //       accs_hash_L,
  //       ro_consts,
  //     )?;
  //     let accs_R = Self::load_accs(
  //       cs.namespace(|| "load accs_R"),
  //       proof.accs_R,
  //       accs_hash_R,
  //       ro_consts,
  //     )?;
  //     (accs_L, accs_R)
  //   };
  //
  //   // Merge the two lists of accumulators and return their hashes
  //   let accs_hash = {
  //     let accs = AllocatedRelaxedR1CSInstance::merge_many(
  //       cs.namespace(|| "accs"),
  //       accs_L,
  //       accs_R,
  //       &mut acc_sm,
  //       proof.nivc_merge_proof,
  //       transcript,
  //     )?;
  //
  //     accs
  //       .into_iter()
  //       .map(|acc| acc.hash(cs.namespace(|| "hash acc"), ro_consts))
  //       .collect::<Result<Vec<_>, _>>()?
  //   };
  //
  //   // Merge the secondary curve accumulators
  //   let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::merge(
  //     cs.namespace(|| "merge acc_cf"),
  //     acc_cf_L,
  //     acc_cf_R,
  //     proof.cf_merge_proof,
  //     transcript,
  //   )?;
  //
  //   // Prove all scalar multiplications by folding the result into the secondary curve accumulator
  //   let acc_cf = acc_sm.finalize(
  //     cs.namespace(|| "acc_sm finalize"),
  //     acc_cf,
  //     proof.sm_fold_proofs,
  //     transcript,
  //   )?;
  //   let state = Self {
  //     io,
  //     accs_hash,
  //     acc_cf,
  //   };
  //   let io = state.io.to_native()?;
  //
  //   Ok((state, io))
  // }

  pub fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let hash = self.hash(cs.namespace(|| "hash state"))?;
    hash.inputize(cs.namespace(|| "inputize hash"))
  }

  fn alloc_unchecked<CS>(mut cs: CS, state: NIVCStateInstance<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let transcript_init =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc transcript_init"), || {
        state.transcript_state
      });

    let io = AllocatedNIVCIO::alloc(cs.namespace(|| "alloc io"), state.io);

    let accs_hash = state
      .accs_hash
      .into_iter()
      .map(|acc_hash| {
        AllocatedNum::alloc_infallible(cs.namespace(|| "alloc acc_hash"), || acc_hash)
      })
      .collect::<Vec<_>>();

    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::alloc_unchecked(
      cs.namespace(|| "alloc acc_cf"),
      state.acc_cf,
    );

    Self {
      transcript_init,
      io,
      accs_hash,
      acc_cf,
    }
  }

  pub fn hash<CS>(&self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let elements = self.as_preimage().into_iter().collect::<Vec<_>>();
    let constants = NIVCPoseidonConstants::<E>::new_constant_length(elements.len());
    PoseidonCircuit2::new(elements, &constants).hash_to_allocated(cs.namespace(|| "state hash"))
  }

  fn update_accs<CS>(
    mut cs: CS,
    accs_hash: Vec<AllocatedNum<E::Scalar>>,
    state_hash: AllocatedNum<E::Scalar>,
    acc_prev: RelaxedR1CSInstance<E>,
    index_prev: Option<usize>,
    is_base_case: &Boolean,
    acc_sm: &mut AllocatedScalarMulAccumulator<E>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<Vec<AllocatedNum<E::Scalar>>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let (acc_prev_hash, acc_curr_hash) = {
      // Load pre-image of accumulator to be updated
      let acc_prev =
        AllocatedRelaxedR1CSInstance::alloc(cs.namespace(|| "alloc acc_prev"), acc_prev);

      // Compute its hash
      let acc_prev_hash = acc_prev.hash(cs.namespace(|| "hash acc_prev"))?;

      // Set the R1CS IO as the transcript init followed by the state

      let acc_curr = acc_prev.fold(cs.namespace(|| "fold"), state_hash, acc_sm, transcript)?;

      let acc_curr_hash = acc_curr.hash(cs.namespace(|| "hash acc_curr"))?;

      (acc_prev_hash, acc_curr_hash)
    };

    // Create selector for acc_prev_hash and ensure it is contained in accs_hash
    let accs_hash_selector = {
      let bits = accs_hash
        .iter()
        .enumerate()
        .map(|(i, acc_hash)| {
          // Allocate a bit which is true if i == index_prev
          let bit = index_prev.map_or(false, |index_prev| index_prev == i);
          let bit = AllocatedBit::alloc(cs.namespace(|| format!("alloc selector[{i}]")), Some(bit))
            .unwrap();

          // Ensure acc_hash[index_prev] = acc_prev_hash
          cs.enforce(
            || format!("bit[{i}] * (acc_hash[{i}] - acc_prev_hash[{i}]) = 0"),
            |lc| lc + bit.get_variable(),
            |lc| lc + acc_hash.get_variable() - acc_prev_hash.get_variable(),
            |lc| lc,
          );

          Boolean::Is(bit)
        })
        .collect::<Vec<_>>();

      // Compute sum of all bits
      let lc_sum = bits.iter().fold(LinearCombination::zero(), |lc, bit| {
        lc + &bit.lc(CS::one(), E::Scalar::ONE)
      });

      // Ensure only 1 selection bit is true, except in the base case where all bits are 0
      cs.enforce(
        || "is_base.not = ∑_i bits[i]",
        |lc| lc,
        |lc| lc,
        |_| is_base_case.not().lc(CS::one(), E::Scalar::ONE) - &lc_sum,
      );

      bits
    };

    // Update hashes of accumulators in state
    zip_eq(accs_hash.into_iter(), accs_hash_selector.iter())
      .map(|(acc_hash, bit)| {
        conditionally_select(
          cs.namespace(|| "accs_hash_curr"),
          &acc_curr_hash,
          &acc_hash,
          bit,
        )
      })
      .collect::<Result<Vec<_>, _>>()
  }

  fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> + '_ {
    chain![
      [Elt::Allocated(self.transcript_init.clone())],
      self.io.as_preimage(),
      self.accs_hash.iter().cloned().map(Elt::Allocated),
      self.acc_cf.as_preimage()
    ]
  }

  // fn load_accs<CS>(
  //   mut cs: CS,
  //   accs_native: Vec<RelaxedR1CSInstance<E>>,
  //   accs_hash: Vec<AllocatedNum<E::Scalar>>,
  // ) -> Result<Vec<AllocatedRelaxedR1CSInstance<E>>, SynthesisError>
  // where
  //   CS: ConstraintSystem<E::Scalar>,
  // {
  //   zip_eq(accs_native, accs_hash)
  //     .map(
  //       |(acc_native, acc_hash): (RelaxedR1CSInstance<E>, AllocatedNum<E::Scalar>)| {
  //         let acc = AllocatedRelaxedR1CSInstance::alloc(cs.namespace(|| "alloc acc"), acc_native);
  //         let acc_hash_real = acc.hash(cs.namespace(|| "hash acc"))?;
  //
  //         // Ensure the loaded accumulator's hash matches the one from the state
  //         cs.enforce(
  //           || "acc_hash_real == acc_hash",
  //           |lc| lc,
  //           |lc| lc,
  //           |lc| lc + acc_hash_real.get_variable() - acc_hash.get_variable(),
  //         );
  //         Ok::<_, SynthesisError>(acc)
  //       },
  //     )
  //     .collect::<Result<Vec<_>, _>>()
  // }
}

impl<E: CurveCycleEquipped> AllocatedNIVCIO<E> {
  // pub fn merge<CS>(mut cs: CS, io_L: Self, io_R: Self) -> Self
  // where
  //   CS: ConstraintSystem<F>,
  // {
  //   // io_L.pc_out = io_R.pc_in
  //   cs.enforce(
  //     || "io_L.pc_out = io_R.pc_in",
  //     |lc| lc,
  //     |lc| lc,
  //     |lc| lc + io_L.pc_out.get_variable() - io_R.pc_in.get_variable(),
  //   );
  //
  //   // io_L.z_out = io_R.z_in
  //   zip_eq(&io_L.z_out, &io_R.z_in)
  //     .enumerate()
  //     .for_each(|(i, (z_L_i, z_R_i))| {
  //       cs.enforce(
  //         || format!("io_L.z_out[{i}] = io_R.z_in[{i}]"),
  //         |lc| lc,
  //         |lc| lc,
  //         |lc| lc + z_L_i.get_variable() - z_R_i.get_variable(),
  //       );
  //     });
  //
  //   Self {
  //     pc_in: io_L.pc_in,
  //     z_in: io_L.z_in,
  //     pc_out: io_R.pc_out,
  //     z_out: io_R.z_out,
  //   }
  // }

  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &Boolean)
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let is_trivial = is_trivial.lc(CS::one(), E::Scalar::ONE);

    // (is_trivial) * (z_in - z_out) = 0
    zip_eq(&self.z_in, &self.z_out)
      .enumerate()
      .for_each(|(i, (z_in_i, z_out_i))| {
        cs.enforce(
          || format!("(is_trivial) * (z_in[{i}] - z_out[{i}]) = 0"),
          |_| is_trivial.clone(),
          |lc| lc + z_in_i.get_variable() - z_out_i.get_variable(),
          |lc| lc,
        );
      });

    // (is_trivial) * (pc_in - pc_out) = 0
    cs.enforce(
      || "(is_trivial) * (pc_in - pc_out) = 0",
      |_| is_trivial,
      |lc| lc + self.pc_in.get_variable() - self.pc_out.get_variable(),
      |lc| lc,
    );
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> + '_ {
    chain![
      [self.pc_in.clone()],
      self.z_in.iter().cloned(),
      [self.pc_out.clone()],
      self.z_out.iter().cloned()
    ]
    .map(Elt::Allocated)
  }

  pub fn alloc<CS>(mut cs: CS, state: NIVCIO<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let NIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    } = state;

    let pc_in = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_in"), || pc_in);
    let z_in = z_in
      .into_iter()
      .enumerate()
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || z)
      })
      .collect();
    let pc_out = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_out"), || pc_out);
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

  /// Attempt to extract the native representation.
  pub fn to_native(&self) -> Result<NIVCIO<E>, SynthesisError> {
    let pc_in = self
      .pc_in
      .get_value()
      .ok_or(SynthesisError::AssignmentMissing)?;
    let z_in = self
      .z_in
      .iter()
      .map(|z| z.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;
    let pc_out = self
      .pc_out
      .get_value()
      .ok_or(SynthesisError::AssignmentMissing)?;
    let z_out = self
      .z_out
      .iter()
      .map(|z| z.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(NIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    })
  }
}
