use ff::Field;
use itertools::{chain, zip_eq};
use neptune::hash_type::HashType;
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::Strength;

use crate::CommitmentKey;
use crate::parafold::cycle_fold::nifs::prover::{
  RelaxedSecondaryR1CS, RelaxedSecondaryR1CSInstance,
};
use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::nivc::{NIVCIO, NIVCPoseidonConstants, NIVCStateInstance, NIVCUpdateProof};
use crate::parafold::transcript::{TranscriptConstants, TranscriptElement};
use crate::parafold::transcript::prover::Transcript;
use crate::r1cs::R1CSShape;
use crate::supernova::error::SuperNovaError;
use crate::traits::CurveCycleEquipped;

#[derive(Debug)]
pub struct NIVCState<E: CurveCycleEquipped> {
  pub(crate) transcript_state: E::Scalar,
  pub(crate) io: NIVCIO<E>,
  accs: Vec<RelaxedR1CS<E>>,
  acc_cf: RelaxedSecondaryR1CS<E>,
}

#[derive(Debug)]
pub struct NIVCUpdateWitness<E: CurveCycleEquipped> {
  pub(crate) index: usize,
  pub(crate) W: Vec<E::Scalar>,
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
    let transcript_init: E::Scalar = E::Scalar::ZERO;
    let io = NIVCIO::new(pc_init, z_init);
    let accs = shapes
      .iter()
      .map(|shape| RelaxedR1CS::new(shape))
      .collect::<Vec<_>>();
    let acc_cf = RelaxedSecondaryR1CS::new(shape_cf);

    let state_instance = NIVCStateInstance::new(
      io.clone(),
      accs.iter().map(|acc| acc.instance().clone()).collect(),
      acc_cf.instance().clone(),
    );

    let state_hash = state_instance.hash();

    let mut transcript = Transcript::new(ro_consts.clone(), [state_hash, transcript_init]);

    let mut acc_sm = ScalarMulAccumulator::dummy();
    RelaxedR1CS::simulate_fold(&mut acc_sm, &mut transcript);
    let _ = acc_sm.simulate_finalize(&mut transcript);

    let (transcript_state, transcript_buffer) = transcript.seal();

    let state = Self {
      transcript_state,
      io,
      accs,
      acc_cf,
    };
    let proof = NIVCUpdateProof {
      transcript_prev: transcript_init,
      transcript_buffer,
      state: state_instance,
      acc_prev: RelaxedR1CSInstance::<E>::dummy(),
      index_prev: None,
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
    let state_instance_prev = self.instance();

    let Self {
      transcript_state: transcript_prev,
      io,
      mut accs,
      acc_cf,
    } = self;

    let state_hash_prev = state_instance_prev.hash();
    let X_prev = [state_hash_prev, transcript_prev];

    let mut transcript = Transcript::new(ro_consts.clone(), X_prev.clone());

    let mut acc_sm = ScalarMulAccumulator::new(acc_cf);

    let NIVCUpdateWitness {
      index: index_prev,
      W: W_prev,
    } = witness_prev;

    let index_prev = *index_prev;

    let acc_prev = accs[index_prev].instance().clone();

    let shape_prev = &shapes[index_prev];

    // Fold the proof for the previous iteration into the correct accumulator
    accs[index_prev].fold(ck, shape_prev, X_prev, W_prev, &mut acc_sm, &mut transcript);
    let acc_cf = acc_sm.finalize(ck_cf, shape_cf, &mut transcript).unwrap();

    let (transcript_state, transcript_buffer) = transcript.seal();

    let proof = NIVCUpdateProof {
      transcript_prev,
      transcript_buffer,
      state: state_instance_prev,
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
    NIVCStateInstance {
      io: self.io.clone(),
      accs: self.accs.iter().map(|acc| acc.instance().clone()).collect(),
      acc_cf: self.acc_cf.instance().clone(),
    }
  }

  pub fn verify(
    &self,
    ck: &CommitmentKey<E>,
    ck_cf: &CommitmentKey<E::Secondary>,
    shapes: &[R1CSShape<E>],
    shape_cf: &R1CSShape<E::Secondary>,
  ) -> Result<(), SuperNovaError> {
    for (acc, shape) in zip_eq(&self.accs, shapes) {
      acc.verify(ck, shape)?;
    }
    self.acc_cf.verify(ck_cf, shape_cf)?;
    Ok(())
  }
}

impl<E: CurveCycleEquipped> NIVCStateInstance<E> {
  pub fn new(
    io: NIVCIO<E>,
    accs: Vec<RelaxedR1CSInstance<E>>,
    acc_cf: RelaxedSecondaryR1CSInstance<E>,
  ) -> Self {
    Self { io, accs, acc_cf }
  }

  pub fn dummy(arity: usize, num_circuit: usize) -> Self {
    Self {
      io: NIVCIO::dummy(arity),
      accs: vec![RelaxedR1CSInstance::dummy(); num_circuit],
      acc_cf: RelaxedSecondaryR1CSInstance::dummy(),
    }
  }

  pub fn hash(&self) -> E::Scalar {
    let elements = self
      .as_preimage()
      .into_iter()
      .map(|x| x.to_field())
      .flatten()
      .collect::<Vec<_>>();

    let num_absorbs = elements.len() as u32;
    let constants =
      NIVCPoseidonConstants::<E>::new_with_strength_and_type(Strength::Standard, HashType::Sponge);

    let acc = &mut ();
    let mut sponge = Sponge::new_with_constants(&constants, Simplex);
    let parameter = IOPattern(vec![SpongeOp::Absorb(num_absorbs), SpongeOp::Squeeze(1u32)]);
    sponge.start(parameter, None, acc);
    SpongeAPI::absorb(&mut sponge, num_absorbs, &elements, acc);
    let hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
    SpongeAPI::finish(&mut sponge, acc).expect("no error");
    hash[0]
  }

  pub fn as_preimage(&self) -> impl IntoIterator<Item = TranscriptElement<E>> + '_ {
    let accs_hash = self
      .accs
      .iter()
      .map(|acc| TranscriptElement::Scalar(acc.hash()));
    chain![self.io.as_preimage(), accs_hash, self.acc_cf.as_preimage()]
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

  pub fn dummy(arity: usize) -> Self {
    Self {
      pc_in: Default::default(),
      z_in: vec![Default::default(); arity],
      pc_out: Default::default(),
      z_out: vec![Default::default(); arity],
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
