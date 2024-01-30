use ff::{Field, PrimeField};
use itertools::chain;

use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::{FoldProof, RelaxedR1CSInstance};
use crate::parafold::nivc::{NIVCMergeProof, NIVCStateInstance, NIVCUpdateProof, NIVCIO};
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::TranscriptConstants;
use crate::r1cs::R1CSShape;
use crate::traits::Engine;
use crate::CommitmentKey;

#[derive(Debug)]
pub struct NIVCState<E1: Engine, E2: Engine> {
  transcript: Transcript<E1>,
  io: NIVCIO<E1::Scalar>,
  accs: Vec<RelaxedR1CS<E1>>,
  acc_cf: RelaxedR1CS<E2>,
}

#[derive(Debug)]
pub struct NIVCUpdateWitness<E1: Engine> {
  pub(crate) index: usize,
  pub(crate) W: Vec<E1::Scalar>,
}

impl<E1, E2> NIVCState<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar, Scalar = E1::Base>,
{
  /// Initialize the prover state and create a default proof for the first iteration.
  ///
  /// # Details
  ///
  /// In the first iteration, the circuit verifier checks the base-case conditions, but does not update any
  /// of the accumulators. To ensure uniformity with the non-base case path, the transcript will be updated
  /// in the normal way, albeit with dummy proof data.
  ///
  ///
  pub fn init(
    shapes: &[R1CSShape<E1>],
    shape_cf: &R1CSShape<E2>,
    ro_consts: &TranscriptConstants<E1>,
    pc_init: usize,
    z_init: Vec<E1::Scalar>,
  ) -> (Self, NIVCUpdateProof<E1, E2>) {
    let transcript_init = E1::Scalar::ZERO;
    let mut state = Self {
      transcript: Transcript::new_init(transcript_init, ro_consts.clone()),
      io: NIVCIO::new(pc_init, z_init),
      accs: shapes.iter().map(|shape| RelaxedR1CS::new(shape)).collect(),
      acc_cf: RelaxedR1CS::new(shape_cf),
    };

    let state_instance = state.instance(ro_consts);

    let num_io = state_instance.io_size();
    state.transcript.absorb(state_instance.as_preimage());
    let acc_prev = RelaxedR1CSInstance::default(num_io);

    let mut acc_sm = ScalarMulAccumulator::new(ro_consts.clone());
    let nifs_fold_proof = RelaxedR1CS::simulate_fold_primary(&mut acc_sm, &mut state.transcript);
    let sm_fold_proofs: [FoldProof<E2>; 2] = acc_sm
      .simulate_finalize(&mut state.transcript)
      .try_into()
      .unwrap();

    let proof = NIVCUpdateProof {
      transcript_init,
      state: state_instance,
      acc_prev,
      index_prev: None,
      nifs_fold_proof,
      sm_fold_proofs,
    };

    (state, proof)
  }

  fn update(
    &mut self,
    ck: &CommitmentKey<E1>,
    ck_cf: &CommitmentKey<E2>,
    ro_consts: &TranscriptConstants<E1>,
    shapes: &[R1CSShape<E1>],
    shape_cf: &R1CSShape<E2>,
    witness_prev: &NIVCUpdateWitness<E1>,
  ) -> NIVCUpdateProof<E1, E2> {
    let mut acc_sm = ScalarMulAccumulator::<E1>::new(ro_consts.clone());
    let transcript_init = self.transcript.seal();

    let state = self.instance(ro_consts);

    let X_prev = chain![[transcript_init], state.as_preimage()].collect();

    let NIVCUpdateWitness {
      index: index_prev,
      W: W_prev,
    } = witness_prev;
    let index_prev = *index_prev;

    let acc_prev = self.accs[index_prev].instance().clone();

    let shape_prev = &shapes[index_prev];

    // Fold the proof for the previous iteration into the correct accumulator
    let nifs_fold_proof = self.accs[index_prev].fold_primary(
      ck,
      shape_prev,
      X_prev,
      W_prev,
      &mut acc_sm,
      &mut self.transcript,
    );

    let sm_fold_proofs: [FoldProof<E2>; 2] = acc_sm
      .finalize(ck_cf, shape_cf, &mut self.acc_cf, &mut self.transcript)
      .try_into()
      .unwrap();

    NIVCUpdateProof {
      transcript_init,
      state,
      acc_prev,
      index_prev: Some(index_prev),
      nifs_fold_proof,
      sm_fold_proofs,
    }
  }

  pub fn merge(
    ck: &CommitmentKey<E1>,
    ck_cf: &CommitmentKey<E2>,
    shapes: &[R1CSShape<E1>],
    shape_cf: &R1CSShape<E2>,
    ro_consts: &TranscriptConstants<E1>,
    self_L: Self,
    self_R: &Self,
  ) -> (Self, NIVCMergeProof<E1, E2>) {
    let Self {
      transcript: transcript_L,
      io: io_L,
      accs: accs_L,
      acc_cf: acc_cf_L,
    } = self_L;
    let Self {
      transcript: transcript_R,
      io: io_R,
      accs: accs_R,
      acc_cf: acc_cf_R,
    } = self_R;

    let mut acc_sm = ScalarMulAccumulator::new(ro_consts.clone());
    let mut transcript = Transcript::merge(transcript_L, transcript_R);

    let io = NIVCIO::merge(io_L, io_R.clone());

    let accs_L_instance = accs_L
      .iter()
      .map(|acc| acc.instance())
      .cloned()
      .collect::<Vec<_>>();
    let accs_R_instance = accs_R
      .iter()
      .map(|acc| acc.instance())
      .cloned()
      .collect::<Vec<_>>();

    let (accs, nivc_merge_proof) =
      RelaxedR1CS::merge_many(ck, shapes, accs_L, accs_R, &mut acc_sm, &mut transcript);

    let (mut acc_cf, cf_merge_proof) =
      RelaxedR1CS::merge_secondary(ck_cf, shape_cf, acc_cf_L, acc_cf_R, &mut transcript);

    let sm_fold_proofs = acc_sm.finalize(ck_cf, shape_cf, &mut acc_cf, &mut transcript);

    let self_next = Self {
      transcript,
      io,
      accs,
      acc_cf,
    };

    let merge_proof = NIVCMergeProof {
      accs_L: accs_L_instance,
      accs_R: accs_R_instance,
      nivc_merge_proof,
      cf_merge_proof,
      sm_fold_proofs,
    };

    (self_next, merge_proof)
  }

  pub fn instance(&self, ro_consts: &TranscriptConstants<E1>) -> NIVCStateInstance<E1, E2> {
    let accs_hash = self
      .accs
      .iter()
      .map(|acc| acc.instance().hash(ro_consts))
      .collect();

    NIVCStateInstance {
      io: self.io.clone(),
      accs_hash,
      acc_cf: self.acc_cf.instance().clone(),
    }
  }
}

impl<E1, E2> NIVCStateInstance<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn as_preimage(&self) -> impl IntoIterator<Item = E1::Scalar> + '_ {
    chain![
      self.io.as_preimage(),
      self.accs_hash.iter().cloned(),
      self.acc_cf.as_preimage()
    ]
  }

  pub fn io_size(&self) -> usize {
    [
      1,                     // transcript init
      self.io.io_size(),     // io
      self.accs_hash.len(),  // accs_hash
      self.acc_cf.io_size(), // acc_cf
    ]
    .into_iter()
    .sum()
  }
}

impl<F: PrimeField> NIVCIO<F> {
  pub fn new(pc_init: usize, z_init: Vec<F>) -> Self {
    Self {
      pc_in: F::from(pc_init as u64),
      z_in: z_init.clone(),
      pc_out: F::from(pc_init as u64),
      z_out: z_init,
    }
  }

  pub fn merge(self_L: Self, self_R: Self) -> Self {
    assert_eq!(self_L.pc_out, self_R.pc_in);
    assert_eq!(self_L.z_out, self_R.z_in);
    Self {
      pc_in: self_L.pc_in,
      z_in: self_L.z_in,
      pc_out: self_R.pc_out,
      z_out: self_R.z_out,
    }
  }
  pub fn as_preimage(&self) -> impl IntoIterator<Item = F> + '_ {
    chain![
      [self.pc_in],
      self.z_in.iter().cloned(),
      [self.pc_out],
      self.z_out.iter().cloned()
    ]
  }

  pub fn io_size(&self) -> usize {
    [
      1,                // pc_in
      self.z_in.len(),  // z_in
      1,                // pc_out
      self.z_out.len(), // z_out
    ]
    .into_iter()
    .sum()
  }
}
