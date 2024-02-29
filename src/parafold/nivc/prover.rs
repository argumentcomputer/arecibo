use ff::Field;
use itertools::chain;
use neptune::Poseidon;

use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CS;
use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::nivc::{NIVCPoseidonConstants, NIVCStateInstance, NIVCUpdateProof, NIVCIO};
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::{TranscriptConstants, TranscriptElement};
use crate::r1cs::R1CSShape;
use crate::traits::CurveCycleEquipped;
use crate::CommitmentKey;

#[derive(Debug)]
pub struct NIVCState<E: CurveCycleEquipped> {
  transcript_state: E::Scalar,
  io: NIVCIO<E>,
  accs: Vec<RelaxedR1CS<E>>,
  acc_cf: RelaxedSecondaryR1CS<E>,
}

#[derive(Debug)]
pub struct NIVCUpdateWitness<E: CurveCycleEquipped> {
  pub(crate) index: usize,
  pub(crate) W: Vec<E::Scalar>,
  pub(crate) io: NIVCIO<E>,
}

impl<E: CurveCycleEquipped> NIVCState<E> {
  /// Initialize the prover state and create a default proof for the first iteration.
  ///
  /// # Details
  ///
  /// In the first iteration, the circuit verifier checks the base-case conditions, but does not update any
  /// of the accumulators. To ensure uniformity with the non-base case path, the transcript will be updated
  /// in the normal way, albeit with dummy proof data.
  pub fn new(
    shapes: &[R1CSShape<E>],
    shape_cf: &R1CSShape<E::Secondary>,
    pc_init: usize,
    z_init: Vec<E::Scalar>,
    ro_consts: &TranscriptConstants<E::Scalar>,
  ) -> (Self, NIVCUpdateProof<E>) {
    let transcript_state = E::Scalar::ZERO;
    let io = NIVCIO::new(pc_init, z_init);
    let accs = shapes
      .iter()
      .map(|shape| RelaxedR1CS::new(shape))
      .collect::<Vec<_>>();
    let acc_cf = RelaxedSecondaryR1CS::new(shape_cf);

    let state_instance = NIVCStateInstance {
      transcript_state,
      io: io.clone(),
      accs_hash: accs.iter().map(|acc| acc.instance().hash()).collect(),
      acc_cf: acc_cf.instance().clone(),
    };

    let state_hash = state_instance.hash();

    let mut transcript = Transcript::new(ro_consts.clone(), [state_hash]);

    let mut acc_sm = ScalarMulAccumulator::new(acc_cf);
    RelaxedR1CS::simulate_fold(&mut acc_sm, &mut transcript);
    let acc_cf = acc_sm.simulate_finalize(&mut transcript);

    let (transcript_state, transcript_buffer) = transcript.seal();

    let proof = NIVCUpdateProof {
      transcript_buffer,
      state: state_instance,
      acc_prev: RelaxedR1CSInstance::<E>::default(),
      index_prev: None,
    };

    let state = Self {
      transcript_state,
      io,
      accs,
      acc_cf,
    };

    (state, proof)
  }

  pub fn update(
    self,
    ck: &CommitmentKey<E>,
    ck_cf: &CommitmentKey<E::Secondary>,
    ro_consts: &TranscriptConstants<E::Scalar>,
    shapes: &[R1CSShape<E>],
    shape_cf: &R1CSShape<E::Secondary>,
    witness_prev: &NIVCUpdateWitness<E>,
  ) -> (Self, NIVCUpdateProof<E>) {
    let state_instance = self.instance();
    let state_hash = state_instance.hash();
    let mut transcript = Transcript::new(ro_consts.clone(), [state_hash]);

    let Self {
      transcript_state,
      mut io,
      mut accs,
      acc_cf,
    } = self;

    let mut acc_sm = ScalarMulAccumulator::new(acc_cf);

    let X_prev = transcript_state;

    let NIVCUpdateWitness {
      index: index_prev,
      W: W_prev,
      io: io_next,
    } = witness_prev;

    io.update(io_next.clone());

    let index_prev = *index_prev;

    let acc_prev = accs[index_prev].instance().clone();

    let shape_prev = &shapes[index_prev];

    // Fold the proof for the previous iteration into the correct accumulator
    accs[index_prev].fold(ck, shape_prev, X_prev, W_prev, &mut acc_sm, &mut transcript);
    let acc_cf = acc_sm.finalize(ck_cf, shape_cf, &mut transcript);

    let (transcript_state, transcript_buffer) = transcript.seal();

    let proof = NIVCUpdateProof {
      transcript_buffer,
      state: state_instance,
      acc_prev,
      index_prev: Some(index_prev),
    };
    let state = Self {
      transcript_state,
      io,
      accs,
      acc_cf,
    };
    (state, proof)
  }

  // pub fn merge(
  //   ck: &CommitmentKey<E>,
  //   ck_cf: &CommitmentKey<E::Secondary>,
  //   shapes: &[R1CSShape<E>],
  //   shape_cf: &R1CSShape<E::Secondary>,
  //   self_L: Self,
  //   self_R: &Self,
  // ) -> (Self, NIVCMergeProof<E>) {
  //   let Self {
  //     transcript: transcript_L,
  //     io: io_L,
  //     accs: accs_L,
  //     acc_cf: acc_cf_L,
  //   } = self_L;
  //   let Self {
  //     transcript: transcript_R,
  //     io: io_R,
  //     accs: accs_R,
  //     acc_cf: acc_cf_R,
  //   } = self_R;
  //
  //   let mut acc_sm = ScalarMulAccumulator::new();
  //   let mut transcript = Transcript::merge(transcript_L, transcript_R);
  //
  //   let io = NIVCIO::merge(io_L, io_R.clone());
  //
  //   let accs_L_instance = accs_L
  //     .iter()
  //     .map(|acc| acc.instance())
  //     .cloned()
  //     .collect::<Vec<_>>();
  //   let accs_R_instance = accs_R
  //     .iter()
  //     .map(|acc| acc.instance())
  //     .cloned()
  //     .collect::<Vec<_>>();
  //
  //   let (accs, nivc_merge_proof) =
  //     RelaxedR1CS::merge_many(ck, shapes, accs_L, accs_R, &mut acc_sm, &mut transcript);
  //
  //   let (mut acc_cf, cf_merge_proof) = RelaxedR1CS::<E::Secondary>::merge_secondary::<E>(
  //     ck_cf,
  //     shape_cf,
  //     acc_cf_L,
  //     acc_cf_R,
  //     &mut transcript,
  //   );
  //
  //   let sm_fold_proofs = acc_sm.finalize(ck_cf, shape_cf, &mut acc_cf, &mut transcript);
  //
  //   let self_next = Self {
  //     transcript,
  //     io,
  //     accs,
  //     acc_cf,
  //   };
  //
  //   let merge_proof = NIVCMergeProof {
  //     accs_L: accs_L_instance,
  //     accs_R: accs_R_instance,
  //     nivc_merge_proof,
  //     cf_merge_proof,
  //     sm_fold_proofs,
  //   };
  //
  //   (self_next, merge_proof)
  // }

  pub fn instance(&self) -> NIVCStateInstance<E> {
    let accs_hash = self.accs.iter().map(|acc| acc.instance().hash()).collect();

    NIVCStateInstance {
      transcript_state: self.transcript_state,
      io: self.io.clone(),
      accs_hash,
      acc_cf: self.acc_cf.instance().clone(),
    }
  }
}

impl<E: CurveCycleEquipped> NIVCStateInstance<E> {
  pub fn hash(&self) -> E::Scalar {
    let elements = self
      .as_preimage()
      .into_iter()
      .map(|x| x.to_field())
      .flatten()
      .collect::<Vec<_>>();
    let constants = NIVCPoseidonConstants::<E>::new_constant_length(elements.len());
    Poseidon::new_with_preimage(&elements, &constants).hash()
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = TranscriptElement<E>> + '_ {
    chain![
      [TranscriptElement::Scalar(self.transcript_state)],
      self.io.as_preimage(),
      self
        .accs_hash
        .iter()
        .cloned()
        .map(TranscriptElement::Scalar),
      self.acc_cf.as_preimage()
    ]
  }
}

impl<E: CurveCycleEquipped> NIVCIO<E> {
  pub fn new(pc_init: usize, z_init: Vec<E::Scalar>) -> Self {
    Self {
      pc_in: E::Scalar::from(pc_init as u64),
      z_in: z_init.clone(),
      pc_out: E::Scalar::from(pc_init as u64),
      z_out: z_init,
    }
  }

  pub fn update(&mut self, io_next: Self) {
    assert_eq!(self.pc_in, io_next.pc_in);
    assert_eq!(self.z_in, io_next.z_in);
    self.pc_out = io_next.pc_out;
    self.z_out = io_next.z_out;
  }

  // pub fn merge(self_L: Self, self_R: Self) -> Self {
  //   assert_eq!(self_L.pc_out, self_R.pc_in);
  //   assert_eq!(self_L.z_out, self_R.z_in);
  //   Self {
  //     pc_in: self_L.pc_in,
  //     z_in: self_L.z_in,
  //     pc_out: self_R.pc_out,
  //     z_out: self_R.z_out,
  //   }
  // }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = TranscriptElement<E>> + '_ {
    chain![
      [self.pc_in],
      self.z_in.iter().cloned(),
      [self.pc_out],
      self.z_out.iter().cloned()
    ]
    .map(TranscriptElement::Scalar)
  }
}
