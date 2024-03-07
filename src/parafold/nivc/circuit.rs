use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::Field;
use itertools::{chain, enumerate, zip_eq};
use neptune::circuit2::Elt;
use neptune::hash_type::HashType;
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::circuit::SpongeCircuit;
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::SpongeTrait;
use neptune::Strength;

use crate::gadgets::utils::{alloc_num_equals, alloc_zero, conditionally_select};
use crate::parafold::cycle_fold::circuit::AllocatedScalarMulAccumulator;
use crate::parafold::cycle_fold::nifs::circuit::AllocatedSecondaryRelaxedR1CSInstance;
use crate::parafold::nifs::circuit::AllocatedRelaxedR1CSInstance;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::nivc::{
  AllocatedNIVCIO, NIVCCircuitInput, NIVCMergeProof, NIVCPoseidonConstants, NIVCStateInstance,
  NIVCIO,
};
use crate::parafold::transcript::circuit::AllocatedTranscript;
use crate::parafold::transcript::TranscriptConstants;
use crate::supernova::EnforcingStepCircuit;
use crate::traits::CurveCycleEquipped;

/// A representation of a NIVC state, where `io` represents the computations inputs and outputs,
/// and the `accs` are the accumulators for each step function that was used to produce this result.
#[derive(Clone, Debug)]
pub struct AllocatedNIVCState<E: CurveCycleEquipped> {
  transcript_state: AllocatedNum<E::Scalar>,
  io: AllocatedNIVCIO<E>,
  accs_hash: Vec<AllocatedNum<E::Scalar>>,
  acc_cf: AllocatedSecondaryRelaxedR1CSInstance<E>,
}

impl<E: CurveCycleEquipped> AllocatedNIVCState<E> {
  pub fn alloc_unverified<CS>(mut cs: CS, state: &NIVCStateInstance<E>) -> (Self, Boolean)
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let transcript_state =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc transcript_state"), || {
        state.transcript_state
      });

    let io = AllocatedNIVCIO::alloc(cs.namespace(|| "alloc io"), &state.io);
    let accs_hash = enumerate(&state.accs_hash)
      .map(|(i, acc_hash)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc acc_hash {i}")), || *acc_hash)
      })
      .collect::<Vec<_>>();
    let acc_cf = AllocatedSecondaryRelaxedR1CSInstance::alloc_unchecked(
      cs.namespace(|| "alloc acc_cf"),
      &state.acc_cf,
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
    ro_consts: TranscriptConstants<E::Scalar>,
    input: &NIVCCircuitInput<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let NIVCCircuitInput { instance, proof } = input;
    let (mut state, is_base_case) = Self::alloc_unverified(cs.namespace(|| "alloc"), instance);
    let state_hash = state.hash(cs.namespace(|| "state hash"))?;

    let mut transcript = AllocatedTranscript::new(
      ro_consts,
      [state_hash.clone()],
      proof.transcript_buffer.clone(),
    );

    // Initialize scalar mul accumulator for folding
    let mut acc_sm = AllocatedScalarMulAccumulator::new();

    // Load pre-image of accumulator to be updated
    let mut acc = AllocatedRelaxedR1CSInstance::alloc(cs.namespace(|| "alloc acc"), &proof.acc);

    // Compute its hash
    let acc_hash_curr = acc.hash(cs.namespace(|| "acc_hash_curr"))?;

    // Create selector for acc_hash_curr and ensure it is contained in accs_hash
    let accs_hash_selector = {
      let bits = state
        .accs_hash
        .iter()
        .enumerate()
        .map(|(i, acc_hash)| {
          // Allocate a bit which is true if i == index_prev
          let bit = proof.index.map_or(false, |index_curr| index_curr == i);
          let bit = AllocatedBit::alloc(cs.namespace(|| format!("alloc selector[{i}]")), Some(bit))
            .unwrap();

          // Ensure acc_hash[index] = acc_hash_curr
          cs.enforce(
            || format!("bit[{i}] * (acc_hash[{i}] - acc_hash_curr) = 0"),
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
    acc.fold(cs.namespace(|| "fold"), X_new, &mut acc_sm, &mut transcript)?;
    let acc_hash_next = acc.hash(cs.namespace(|| "hash acc_hash_next"))?;

    // Update hashes of accumulators in state
    state.accs_hash = zip_eq(&state.accs_hash, &accs_hash_selector)
      .enumerate()
      .map(|(i, (acc_hash, bit))| {
        conditionally_select(
          cs.namespace(|| format!("acc_hash_next {i}")),
          &acc_hash_next,
          &acc_hash,
          bit,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;

    // Prove all scalar multiplication by updating the secondary curve accumulator
    acc_sm.finalize(
      cs.namespace(|| "finalize acc_sm"),
      &mut state.acc_cf,
      &mut transcript,
    )?;

    // If this is the first iteration, then reset `acc_cf` to its default state since no scalar multiplications
    // were actually computed
    state.acc_cf = state
      .acc_cf
      .select_default(cs.namespace(|| "enforce trivial acc_cf"), &is_base_case)?;

    state.transcript_state = transcript.seal(cs.namespace(|| "checkpoint"))?;

    Ok(state)
  }

  pub fn update_io<CS, SF>(
    &mut self,
    mut cs: CS,
    step_circuit: &SF,
  ) -> Result<Option<NIVCIO<E>>, SynthesisError>
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

    Ok(self.io.to_native())
  }

  pub fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let state_hash = self.hash(cs.namespace(|| "state hash"))?;
    state_hash.inputize(cs.namespace(|| "inputize state_hash"))?;
    state_hash.inputize(cs.namespace(|| "HACK inputize state_hash"))
  }

  pub fn merge<CS>(
    mut cs: CS,
    self_L: Self,
    self_R: Self,
    proof: NIVCMergeProof<E>,
    ro_consts: TranscriptConstants<E::Scalar>,
  ) -> Result<(Self, Option<NIVCIO<E>>), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let accs_L = self_L.load_accs(cs.namespace(|| "load accs_L"), &proof.accs_L)?;
    let accs_R = self_R.load_accs(cs.namespace(|| "load accs_R"), &proof.accs_R)?;

    if let (Some(l), Some(r)) = (
      self_L.transcript_state.get_value(),
      self_R.transcript_state.get_value(),
    ) {
      println!("c: {:?} {:?}", l, r);
    }
    let mut transcript = AllocatedTranscript::new(
      ro_consts,
      [self_L.transcript_state, self_R.transcript_state],
      proof.transcript_buffer,
    );

    let io = AllocatedNIVCIO::merge(cs.namespace(|| "io merge"), self_L.io, self_R.io);

    let mut acc_cf = AllocatedSecondaryRelaxedR1CSInstance::merge(
      cs.namespace(|| "acc_cf merge"),
      self_L.acc_cf,
      self_R.acc_cf,
      &mut transcript,
    )?;

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
      .map(|acc| acc.hash(cs.namespace(|| "hash acc")))
      .collect::<Result<Vec<_>, _>>()?;

    // Prove all scalar multiplications by folding the result into the secondary curve accumulator
    acc_sm.finalize(
      cs.namespace(|| "acc_sm finalize"),
      &mut acc_cf,
      &mut transcript,
    )?;

    let state = Self {
      transcript_state: transcript.seal(cs.namespace(|| "checkpoint"))?,
      io,
      accs_hash,
      acc_cf,
    };
    let io = state.io.to_native();

    Ok((state, io))
  }

  pub fn hash<CS>(&self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let elements = self.as_preimage().into_iter().collect::<Vec<_>>();
    let num_absorbs = elements.len() as u32;
    let constants =
      NIVCPoseidonConstants::<E>::new_with_strength_and_type(Strength::Standard, HashType::Sponge);

    let pattern = IOPattern(vec![SpongeOp::Absorb(num_absorbs), SpongeOp::Squeeze(1u32)]);
    let acc = &mut cs.namespace(|| "squeeze");
    let mut sponge = SpongeCircuit::new_with_constants(&constants, Simplex);
    sponge.start(pattern, None, acc);
    SpongeAPI::absorb(&mut sponge, num_absorbs, &elements, acc);
    let state_out = SpongeAPI::squeeze(&mut sponge, 1, acc);
    SpongeAPI::finish(&mut sponge, acc).expect("no error");

    state_out[0].ensure_allocated(acc, true)
  }

  fn load_accs<CS>(
    &self,
    mut cs: CS,
    accs: &[RelaxedR1CSInstance<E>],
  ) -> Result<Vec<AllocatedRelaxedR1CSInstance<E>>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    zip_eq(accs, &self.accs_hash)
      .map(|(acc_native, acc_hash)| {
        let acc = AllocatedRelaxedR1CSInstance::alloc(cs.namespace(|| "alloc acc"), acc_native);
        let acc_hash_real = acc.hash(cs.namespace(|| "hash acc"))?;

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

  pub fn as_preimage(&self) -> impl IntoIterator<Item = Elt<E::Scalar>> + '_ {
    chain![
      [Elt::Allocated(self.transcript_state.clone())],
      self.io.as_preimage(),
      self.accs_hash.iter().cloned().map(Elt::Allocated),
      self.acc_cf.as_preimage()
    ]
  }
}

impl<E: CurveCycleEquipped> AllocatedNIVCIO<E> {
  pub fn alloc<CS>(mut cs: CS, state: &NIVCIO<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let pc_in = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_in"), || state.pc_in);
    let z_in = enumerate(&state.z_in)
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || *z)
      })
      .collect();
    let pc_out = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_out"), || state.pc_out);
    let z_out = enumerate(&state.z_out)
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_out[{i}]")), || *z)
      })
      .collect();

    Self {
      pc_in,
      z_in,
      pc_out,
      z_out,
    }
  }
  pub fn merge<CS>(mut cs: CS, io_L: Self, io_R: Self) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
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

  /// Attempt to extract the native representation.
  pub fn to_native(&self) -> Option<NIVCIO<E>> {
    let pc_in = self.pc_in.get_value()?;
    let z_in = self
      .z_in
      .iter()
      .map(|z| z.get_value())
      .collect::<Option<Vec<_>>>()?;
    let pc_out = self.pc_out.get_value()?;
    let z_out = self
      .z_out
      .iter()
      .map(|z| z.get_value())
      .collect::<Option<Vec<_>>>()?;
    Some(NIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    })
  }
}
