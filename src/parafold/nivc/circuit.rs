use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::{Field, PrimeField};
use itertools::{chain, zip_eq, Itertools};

use crate::gadgets::utils::{alloc_num_equals, alloc_zero, conditionally_select};
use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::nifs::circuit::AllocatedRelaxedR1CSInstance;
use crate::parafold::nifs::circuit_secondary::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::nifs::{FoldProof, RelaxedR1CSInstance};
use crate::parafold::nivc::{
  AllocatedNIVCIO, NIVCMergeProof, NIVCStateInstance, NIVCUpdateProof, NIVCIO,
};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::parafold::transcript::TranscriptConstants;
use crate::supernova::EnforcingStepCircuit;
use crate::traits::Engine;

/// A representation of a NIVC state, where `io` represents the computations inputs and outputs,
/// and the `accs` are the accumulators for each step function that was used to produce this result.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCState<E1: Engine, E2: Engine> {
  io: AllocatedNIVCIO<E1::Scalar>,
  accs_hash: Vec<AllocatedNum<E1::Scalar>>,
  acc_cf: AllocatedSecondaryRelaxedR1CSInstance<E1, E2>,
}

impl<E1, E2> AllocatedNIVCState<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  /// Loads a previously proved state from a proof of its correctness.
  ///
  /// # Details
  ///
  ///
  pub fn from_proof<CS>(
    mut cs: CS,
    ro_consts: &TranscriptConstants<E1>,
    proof: NIVCUpdateProof<E1, E2>,
  ) -> Result<(Self, AllocatedTranscript<E1>), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let NIVCUpdateProof {
      transcript_init,
      state,
      acc_prev,
      index_prev,
      nifs_fold_proof,
      sm_fold_proofs,
    } = proof;

    // Initialize transcript with the state of the transcript in the previous iteration
    let (mut transcript, transcript_init) = AllocatedTranscript::new_init(
      cs.namespace(|| "init transcript"),
      transcript_init,
      ro_consts.clone(),
    );

    // Load the initial state from the proof, adding each field to the transcript
    let mut state = Self::alloc_transcript(cs.namespace(|| "alloc state"), state, &mut transcript);

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

    // Enforce base case on loaded state
    state.enforce_base_case(cs.namespace(|| "base case"), &is_base_case);

    // Initialize scalar mul accumulator for folding
    let mut acc_sm = AllocatedScalarMulAccumulator::new(ro_consts.clone());

    state.update_accs(
      cs.namespace(|| "update accs"),
      ro_consts,
      transcript_init,
      acc_prev,
      index_prev,
      nifs_fold_proof,
      &is_base_case,
      &mut acc_sm,
      &mut transcript,
    )?;

    // Prove all scalar multiplication by updating the secondary curve accumulator
    state.acc_cf = acc_sm.finalize(
      cs.namespace(|| "finalize acc_sm"),
      state.acc_cf,
      sm_fold_proofs,
      &mut transcript,
    )?;

    state.acc_cf = state
      .acc_cf
      .select_default(cs.namespace(|| "enforce trivial acc_cf"), &is_base_case)?;

    Ok((state, transcript))
  }

  pub fn update_io<CS, SF>(
    &mut self,
    mut cs: CS,
    step_circuit: &SF,
  ) -> Result<NIVCIO<E1::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
    SF: EnforcingStepCircuit<E1::Scalar>,
  {
    // Run the step circuit
    let cs_step = &mut cs.namespace(|| "synthesize");

    let (pc_curr, z_curr) = (Some(&self.io.pc_out), self.io.z_out.as_slice());

    let (pc_next, z_next) = step_circuit.enforcing_synthesize(cs_step, pc_curr, z_curr)?;

    self.io.pc_out = pc_next.ok_or(SynthesisError::AssignmentMissing)?;
    self.io.z_out = z_next;

    self.io.to_native()
  }

  pub fn merge<CS>(
    mut cs: CS,
    self_L: Self,
    self_R: Self,
    ro_consts: &TranscriptConstants<E1>,
    proof: NIVCMergeProof<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(Self, NIVCIO<E1::Scalar>), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let mut acc_sm = AllocatedScalarMulAccumulator::new(ro_consts.clone());

    let Self {
      io: io_L,
      accs_hash: accs_hash_L,
      acc_cf: acc_cf_L,
    } = self_L;
    let Self {
      io: io_R,
      accs_hash: accs_hash_R,
      acc_cf: acc_cf_R,
    } = self_R;

    let io = AllocatedNIVCIO::merge(cs.namespace(|| "io merge"), io_L, io_R);

    // Load the preimages of the accumulators in each state
    let (accs_L, accs_R) = {
      let accs_L = Self::load_accs(
        cs.namespace(|| "load accs_R"),
        proof.accs_L,
        accs_hash_L,
        ro_consts,
      )?;
      let accs_R = Self::load_accs(
        cs.namespace(|| "load accs_R"),
        proof.accs_R,
        accs_hash_R,
        ro_consts,
      )?;
      (accs_L, accs_R)
    };

    // Merge the two lists of accumulators and return their hashes
    let accs_hash = {
      let accs = AllocatedRelaxedR1CSInstance::merge_many(
        cs.namespace(|| "accs"),
        accs_L,
        accs_R,
        &mut acc_sm,
        proof.nivc_merge_proof,
        transcript,
      )?;

      accs
        .into_iter()
        .map(|acc| acc.hash(cs.namespace(|| "hash acc"), ro_consts))
        .collect::<Result<Vec<_>, _>>()?
    };

    // Merge the secondary curve accumulators
    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::merge(
      cs.namespace(|| "merge acc_cf"),
      acc_cf_L,
      acc_cf_R,
      proof.cf_merge_proof,
      transcript,
    )?;

    // Prove all scalar multiplications by folding the result into the secondary curve accumulator
    let acc_cf = acc_sm.finalize(
      cs.namespace(|| "acc_sm finalize"),
      acc_cf,
      proof.sm_fold_proofs,
      transcript,
    )?;
    let state = Self {
      io,
      accs_hash,
      acc_cf,
    };
    let io = state.io.to_native()?;

    Ok((state, io))
  }

  pub fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    for x in self.as_preimage() {
      x.inputize(cs.namespace(|| "inputize"))?
    }
    Ok(())
  }

  fn alloc_transcript<CS>(
    mut cs: CS,
    state: NIVCStateInstance<E1, E2>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let NIVCStateInstance {
      io,
      accs_hash,
      acc_cf,
    } = state;

    let io = AllocatedNIVCIO::alloc_transcript(cs.namespace(|| "alloc io"), io, transcript);

    let accs_hash = accs_hash
      .into_iter()
      .map(|acc_hash| {
        let acc_hash =
          AllocatedNum::alloc_infallible(cs.namespace(|| "alloc acc_hash"), || acc_hash);
        transcript.absorb([acc_hash.clone()]);
        acc_hash
      })
      .collect::<Vec<_>>();

    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::alloc_transcript(
      cs.namespace(|| "alloc acc_cf"),
      acc_cf,
      transcript,
    );

    Self {
      io,
      accs_hash,
      acc_cf,
    }
  }

  fn enforce_base_case<CS>(&self, mut cs: CS, is_base_case: &Boolean)
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    // We only need to enforce that the NIVC IO is trivial.
    // We do not need to check that `accs` and `acc_sm` are trivial, the only requirement is that they are
    // valid RelaxedR1CS accumulators. In practice, we do actually supply trivial accumulators.
    self.io.enforce_trivial(
      cs.namespace(|| "is_init => (io.in == io.out)"),
      is_base_case,
    );

    self.acc_cf.enforce_trivial(
      cs.namespace(|| "is_init => acc_cf.is_trivial"),
      is_base_case,
    );
  }

  fn update_accs<CS>(
    &mut self,
    mut cs: CS,
    ro_consts: &TranscriptConstants<E1>,
    transcript_init: AllocatedNum<E1::Scalar>,
    acc_prev: RelaxedR1CSInstance<E1>,
    index_prev: Option<usize>,
    nifs_fold_proof: FoldProof<E1>,
    is_base_case: &Boolean,
    acc_sm: &mut AllocatedScalarMulAccumulator<E1>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    let (acc_prev_hash, acc_curr_hash) = {
      // Load pre-image of accumulator to be updated
      let acc_prev =
        AllocatedRelaxedR1CSInstance::alloc(cs.namespace(|| "alloc acc_prev"), acc_prev, ro_consts);

      // Compute its hash
      let acc_prev_hash = acc_prev.hash(cs.namespace(|| "hash acc_prev"), ro_consts)?;

      // Set the R1CS IO as the transcript init followed by the state
      let X_prev = chain![[transcript_init], self.as_preimage()].collect::<Vec<_>>();

      let acc_curr = acc_prev.fold(
        cs.namespace(|| "fold"),
        X_prev,
        acc_sm,
        nifs_fold_proof,
        transcript,
      )?;

      let acc_curr_hash = acc_curr.hash(cs.namespace(|| "hash acc_curr"), ro_consts)?;

      (acc_prev_hash, acc_curr_hash)
    };

    // Create selector for acc_prev_hash and ensure it is contained in accs_hash
    let accs_hash_selector = {
      let bits = self
        .accs_hash
        .iter()
        .enumerate()
        .map(|(index, acc_hash)| {
          // Allocate a bit which
          let bit = AllocatedBit::alloc(cs.namespace(|| "alloc selector"), {
            let bit = if let Some(index_prev) = index_prev {
              index_prev == index
            } else {
              false
            };
            Some(bit)
          })
          .unwrap();

          // Ensure acc_hash[index_prev] = acc_prev_hash
          cs.enforce(
            || "bit * (acc_hash - acc_prev_hash) = 0",
            |lc| lc + bit.get_variable(),
            |lc| lc + acc_hash.get_variable() - acc_prev_hash.get_variable(),
            |lc| lc,
          );

          bit
        })
        .collect::<Vec<_>>();

      let lc_sum = bits
        .iter()
        .fold(LinearCombination::zero(), |lc, bit| lc + bit.get_variable());

      // Ensure only 1 selection bit is true, except in the base case where all bits are 0
      cs.enforce(
        || "is_base.not = ∑_i bits[i]",
        |lc| lc,
        |lc| lc,
        |_| is_base_case.not().lc(CS::one(), E1::Scalar::ONE) - &lc_sum,
      );

      bits
    };

    // Update hashes of accumulators in state
    self
      .accs_hash
      .iter_mut()
      .zip_eq(accs_hash_selector)
      .for_each(|(acc_hash, bit)| {
        *acc_hash = conditionally_select(
          cs.namespace(|| "accs_hash_curr"),
          &acc_curr_hash,
          acc_hash,
          &Boolean::Is(bit),
        )
        .unwrap();
      });
    Ok(())
  }

  fn as_preimage(&self) -> impl IntoIterator<Item = AllocatedNum<E1::Scalar>> + '_ {
    chain![
      self.io.as_preimage(),
      self.accs_hash.iter().cloned(),
      self.acc_cf.as_preimage()
    ]
  }

  fn load_accs<CS>(
    mut cs: CS,
    accs_native: Vec<RelaxedR1CSInstance<E1>>,
    accs_hash: Vec<AllocatedNum<E1::Scalar>>,
    ro_consts: &TranscriptConstants<E1>,
  ) -> Result<Vec<AllocatedRelaxedR1CSInstance<E1>>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    zip_eq(accs_native, accs_hash)
      .map(
        |(acc_native, acc_hash): (RelaxedR1CSInstance<E1>, AllocatedNum<E1::Scalar>)| {
          let acc = AllocatedRelaxedR1CSInstance::alloc(
            cs.namespace(|| "alloc acc"),
            acc_native,
            ro_consts,
          );
          let acc_hash_real = acc.hash(cs.namespace(|| "hash acc"), ro_consts)?;

          // Ensure the loaded accumulator's hash matches the one from the state
          cs.enforce(
            || "acc_hash_real == acc_hash",
            |lc| lc,
            |lc| lc,
            |lc| lc + acc_hash_real.get_variable() - acc_hash.get_variable(),
          );
          Ok::<_, SynthesisError>(acc)
        },
      )
      .collect::<Result<Vec<_>, _>>()
  }
}

impl<F: PrimeField> AllocatedNIVCIO<F> {
  pub fn merge<CS>(mut cs: CS, io_L: Self, io_R: Self) -> Self
  where
    CS: ConstraintSystem<F>,
  {
    // io_L.pc_out = io_R.pc_in
    cs.enforce(
      || "io_L.pc_out = io_R.pc_in",
      |lc| lc,
      |lc| lc,
      |lc| lc + io_L.pc_out.get_variable() - io_R.pc_in.get_variable(),
    );

    // io_L.z_out = io_R.z_in
    zip_eq(&io_L.z_out, &io_R.z_in)
      .enumerate()
      .for_each(|(i, (z_L_i, z_R_i))| {
        cs.enforce(
          || format!("io_L.z_out[{i}] = io_R.z_in[{i}]"),
          |lc| lc,
          |lc| lc,
          |lc| lc + z_L_i.get_variable() - z_R_i.get_variable(),
        );
      });

    Self {
      pc_in: io_L.pc_in,
      z_in: io_L.z_in,
      pc_out: io_R.pc_out,
      z_out: io_R.z_out,
    }
  }

  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &Boolean)
  where
    CS: ConstraintSystem<F>,
  {
    let is_trivial = is_trivial.lc(CS::one(), F::ONE);

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

  pub fn as_preimage(&self) -> impl IntoIterator<Item = AllocatedNum<F>> + '_ {
    chain![
      [self.pc_in.clone()],
      self.z_in.iter().cloned(),
      [self.pc_out.clone()],
      self.z_out.iter().cloned()
    ]
  }

  pub fn alloc_transcript<CS, E1: Engine<Scalar = F>>(
    mut cs: CS,
    state: NIVCIO<F>,
    transcript: &mut AllocatedTranscript<E1>,
  ) -> Self
  where
    CS: ConstraintSystem<F>,
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

    let io = Self {
      pc_in,
      z_in,
      pc_out,
      z_out,
    };
    transcript.absorb(io.as_preimage());
    io
  }

  pub fn to_native(&self) -> Result<NIVCIO<F>, SynthesisError> {
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
