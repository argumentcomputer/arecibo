use ff::Field;
use itertools::{chain, zip_eq};
use neptune::hash_type::HashType;
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::Strength;

use crate::errors::NovaError;
use crate::parafold::cycle_fold::nifs::prover::{
  RelaxedSecondaryR1CS, RelaxedSecondaryR1CSInstance,
};
use crate::parafold::cycle_fold::prover::ScalarMulAccumulator;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs::RelaxedR1CSInstance;
use crate::parafold::nivc::{
  NIVCCircuitInput, NIVCMergeProof, NIVCPoseidonConstants, NIVCStateInstance, NIVCStateProof,
  NIVCIO,
};
use crate::parafold::prover::{NIVCUpdateWitness, ProvingKey};
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::transcript::{TranscriptConstants, TranscriptElement};
use crate::r1cs::R1CSShape;
use crate::supernova::error::SuperNovaError;
use crate::traits::CurveCycleEquipped;
use crate::CommitmentKey;

#[derive(Debug)]
pub struct NIVCState<E: CurveCycleEquipped> {
  transcript_state: E::Scalar,
  io: NIVCIO<E>,
  accs: Vec<RelaxedR1CS<E>>,
  acc_cf: RelaxedSecondaryR1CS<E>,
}

impl<E: CurveCycleEquipped> NIVCState<E> {
  pub fn new(io: NIVCIO<E>, accs: Vec<RelaxedR1CS<E>>, acc_cf: RelaxedSecondaryR1CS<E>) -> Self {
    Self {
      transcript_state: E::Scalar::ZERO,
      io,
      accs,
      acc_cf,
    }
  }

  pub fn init(&mut self, ro_consts: TranscriptConstants<E::Scalar>) -> NIVCCircuitInput<E> {
    let instance = self.instance();
    let transcript = instance.simulate_update(ro_consts);
    let (transcript_state, transcript_buffer) = transcript.seal();
    self.transcript_state = transcript_state;

    let proof = NIVCStateProof {
      transcript_buffer,
      acc: RelaxedR1CSInstance::dummy(),
      index: None,
    };

    NIVCCircuitInput { instance, proof }
  }

  pub fn update(
    &mut self,
    pk: &ProvingKey<E>,
    witness: &NIVCUpdateWitness<E>,
  ) -> Result<NIVCCircuitInput<E>, NovaError> {
    self.io.update(witness.io_next.clone());

    let instance = self.instance();

    let state_hash = instance.hash();

    assert_eq!(state_hash, witness.X);

    let mut transcript = Transcript::new(pk.ro_consts.clone(), [state_hash]);

    let mut acc_sm = ScalarMulAccumulator::new();

    let index_prev = witness.index;
    let acc_prev = &mut self.accs[index_prev];
    let acc_prev_instance = acc_prev.instance().clone();

    let shape_prev = &pk.shapes[index_prev];

    // Fold the proof for the previous iteration into the correct accumulator
    let X_prev = state_hash;
    acc_prev.fold(
      &pk.ck,
      shape_prev,
      X_prev,
      &witness.W,
      &mut acc_sm,
      &mut transcript,
    );
    acc_sm.finalize(&pk.ck_cf, &pk.shape_cf, &mut self.acc_cf, &mut transcript)?;

    let (transcript_state, transcript_buffer) = transcript.seal();
    self.transcript_state = transcript_state;

    let proof = NIVCStateProof {
      transcript_buffer,
      acc: acc_prev_instance,
      index: Some(index_prev),
    };

    Ok(NIVCCircuitInput { instance, proof })
  }

  pub fn merge(pk: &ProvingKey<E>, self_L: Self, self_R: Self) -> (Self, NIVCMergeProof<E>) {
    println!(
      "p: {:?} {:?}",
      self_L.transcript_state, self_R.transcript_state
    );
    let mut transcript = Transcript::new(
      pk.ro_consts.clone(),
      [self_L.transcript_state, self_R.transcript_state],
    );

    let io = NIVCIO::merge(self_L.io, self_R.io);

    let mut acc_cf = RelaxedSecondaryR1CS::<E>::merge(
      &pk.ck_cf,
      &pk.shape_cf,
      self_L.acc_cf,
      self_R.acc_cf,
      &mut transcript,
    );

    let mut acc_sm = ScalarMulAccumulator::new();

    let accs_L_instance = self_L
      .accs
      .iter()
      .map(|acc| acc.instance().clone())
      .collect();
    let accs_R_instance = self_R
      .accs
      .iter()
      .map(|acc| acc.instance().clone())
      .collect();

    let accs = RelaxedR1CS::<E>::merge_many(
      &pk.ck,
      &pk.shapes,
      self_L.accs,
      &self_R.accs,
      &mut acc_sm,
      &mut transcript,
    );

    acc_sm
      .finalize(&pk.ck_cf, &pk.shape_cf, &mut acc_cf, &mut transcript)
      .unwrap();

    let (transcript_state, transcript_buffer) = transcript.seal();

    let self_next = Self {
      transcript_state,
      io,
      accs,
      acc_cf,
    };

    let merge_proof = NIVCMergeProof {
      transcript_buffer,
      accs_L: accs_L_instance,
      accs_R: accs_R_instance,
    };

    (self_next, merge_proof)
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

  pub fn instance(&self) -> NIVCStateInstance<E> {
    NIVCStateInstance {
      transcript_state: self.transcript_state,
      io: self.io.clone(),
      accs_hash: self.accs.iter().map(|acc| acc.instance().hash()).collect(),
      acc_cf: self.acc_cf.instance().clone(),
    }
  }
}

impl<E: CurveCycleEquipped> NIVCStateInstance<E> {
  pub fn simulate_update(&self, ro_consts: TranscriptConstants<E::Scalar>) -> Transcript<E> {
    let state_hash = self.hash();

    let mut transcript = Transcript::new(ro_consts, [state_hash]);

    let mut acc_sm = ScalarMulAccumulator::new();
    RelaxedR1CS::simulate_fold(&mut acc_sm, &mut transcript);
    let _ = acc_sm.simulate_finalize(&mut transcript);
    transcript
  }

  pub fn simulate_merge(
    transcript_L: E::Scalar,
    transcript_R: E::Scalar,
    num_circuits: usize,
    ro_consts: TranscriptConstants<E::Scalar>,
  ) -> Transcript<E> {
    let mut transcript = Transcript::new(ro_consts.clone(), [transcript_L, transcript_R]);

    let mut acc_sm = ScalarMulAccumulator::new();
    RelaxedSecondaryR1CS::simulate_merge(&mut transcript);
    RelaxedR1CS::simulate_merge_many(num_circuits, &mut acc_sm, &mut transcript);
    let _ = acc_sm.simulate_finalize(&mut transcript);
    transcript
  }

  pub fn dummy(arity: usize, num_circuit: usize) -> Self {
    Self {
      transcript_state: E::Scalar::ZERO,
      io: NIVCIO::dummy(arity),
      accs_hash: vec![E::Scalar::ZERO; num_circuit],
      acc_cf: RelaxedSecondaryR1CSInstance::dummy(),
    }
  }

  pub fn hash(&self) -> E::Scalar {
    let elements = chain![
      [TranscriptElement::Scalar(self.transcript_state)],
      self.io.as_preimage(),
      self
        .accs_hash
        .iter()
        .map(|acc_hash| TranscriptElement::Scalar(*acc_hash)),
      self.acc_cf.as_preimage()
    ]
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
