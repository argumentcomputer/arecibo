use std::sync::Arc;

use bellpepper_core::ConstraintSystem;
use itertools::zip_eq;
use rayon::prelude::*;

use crate::bellpepper::r1cs::NovaShape;
use crate::bellpepper::shape_cs::ShapeCS;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::errors::NovaError;
use crate::parafold::{NIVCIO, NIVCPoseidonConstants, NIVCStepProof, ProvingKey};
use crate::parafold::cycle_fold::prover::{ScalarMulAccumulator, ScalarMulInstance};
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nifs_secondary::prover::RelaxedSecondaryR1CS;
use crate::parafold::NIVCMergeProof;
use crate::parafold::transcript::prover::Transcript;
use crate::parafold::verifier::VerifierState;
use crate::r1cs::{commitment_key_size, CommitmentKeyHint};
use crate::supernova::{NonUniformCircuit, StepCircuit};
use crate::supernova::error::SuperNovaError;
use crate::traits::{CurveCycleEquipped, Engine};
use crate::traits::commitment::CommitmentEngineTrait;

#[derive(Debug)]
pub struct RecursiveSNARK<E: CurveCycleEquipped> {
  accs: Vec<RelaxedR1CS<E>>,
  acc_cf: RelaxedSecondaryR1CS<E>,
}

pub struct RecursiveSNARKProof<E: CurveCycleEquipped> {
  verifier_state: VerifierState<E>,
  step_proof: NIVCStepProof<E>,
}

#[derive(Debug)]
pub struct NIVCUpdateWitness<E: CurveCycleEquipped> {
  index: usize,
  X: E::Scalar,
  W: Vec<E::Scalar>,
}

impl<E: CurveCycleEquipped> ProvingKey<E> {
  pub fn setup<NC: NonUniformCircuit<E>>(
    non_uniform_circuit: &NC,
    ck_hint1: &CommitmentKeyHint<E>,
    ck_hint2: &CommitmentKeyHint<E::Secondary>,
  ) -> Self {
    let num_circuits_nivc = non_uniform_circuit.num_circuits();
    // total number of circuits also contains merge circuit.
    let num_circuits = num_circuits_nivc + 1;

    let constants = NIVCPoseidonConstants::<E>::new();

    let arity = non_uniform_circuit.primary_circuit(0).arity();

    let dummy_state = VerifierState::<E>::dummy(arity, num_circuits);
    let dummy_state_proof = NIVCStepProof::dummy();
    let dummy_merge_proof = NIVCMergeProof::dummy(num_circuits);

    let circuits = (0..num_circuits_nivc)
      .map(|i| non_uniform_circuit.primary_circuit(i))
      .collect::<Vec<_>>();
    let mut shapes = circuits
      .into_par_iter()
      .map(|circuit| {
        assert_eq!(circuit.arity(), arity);

        let mut cs: ShapeCS<E> = ShapeCS::new();
        let _ = dummy_state
          .clone()
          .synthesize_step(&mut cs, dummy_state_proof.clone(), &circuit, &constants)
          .unwrap();
        // We use the largest commitment_key for all instances
        cs.r1cs_shape()
      })
      .collect::<Vec<_>>();
    let shape_merge = {
      let mut cs: ShapeCS<E> = ShapeCS::new();
      let _ = VerifierState::synthesize_merge(
        &mut cs,
        dummy_state.clone(),
        dummy_state.clone(),
        dummy_merge_proof,
        &constants,
      )
      .unwrap();
      cs.r1cs_shape()
    };
    shapes.push(shape_merge);

    let shape_cf = {
      let mut cs: ShapeCS<E::Secondary> = ShapeCS::new();
      let dummy_instance = ScalarMulInstance::<E>::default();
      dummy_instance.synthesize(&mut cs).unwrap();
      cs.r1cs_shape()
    };

    let size_primary = shapes
      .iter()
      .map(|shape| commitment_key_size(shape, ck_hint1))
      .max()
      .unwrap();
    let size_secondary = commitment_key_size(&shape_cf, ck_hint2);

    let ck = Arc::new(E::CE::setup(b"ck", size_primary));
    let ck_cf = Arc::new(<E::Secondary as Engine>::CE::setup(b"ck", size_secondary));

    Self {
      ck,
      ck_cf,
      arity,
      shapes,
      shape_cf,
      constants,
    }
  }
}

impl<E: CurveCycleEquipped> RecursiveSNARK<E> {
  /// Initialize the prover state and create a default proof for the first iteration.
  ///
  /// # Details
  ///
  /// In the first iteration, the circuit verifier checks the base-case conditions, but does not update any
  /// of the accumulators. To ensure uniformity with the non-base case path, the transcript will be updated
  /// in the normal way, albeit with dummy proof data.
  pub fn new(
    pk: &ProvingKey<E>,
    pc_init: usize,
    z_init: Vec<E::Scalar>,
  ) -> (Self, RecursiveSNARKProof<E>) {
    let num_circuits = pk.shapes.len();
    assert!(pc_init < num_circuits);
    assert_eq!(z_init.len(), pk.arity);

    let io = NIVCIO::new(pc_init, z_init);
    let accs = pk.shapes.iter().map(RelaxedR1CS::new).collect::<Vec<_>>();
    let acc_cf = RelaxedSecondaryR1CS::new(&pk.shape_cf);

    let proof = RecursiveSNARKProof {
      verifier_state: VerifierState::new(io, &accs, &acc_cf, &pk.constants),
      step_proof: NIVCStepProof::dummy(),
    };
    let snark = Self { accs, acc_cf };
    (snark, proof)
  }

  pub fn prove_step<C: StepCircuit<E::Scalar>>(
    &mut self,
    pk: &ProvingKey<E>,
    step_circuit: &C,
    proof: RecursiveSNARKProof<E>,
  ) -> Result<RecursiveSNARKProof<E>, NovaError> {
    let RecursiveSNARKProof {
      verifier_state,
      step_proof,
    } = proof;
    let circuit_index = step_circuit.circuit_index();

    let mut cs = SatisfyingAssignment::<E>::new();
    let verifier_state = verifier_state
      .synthesize_step(&mut cs, step_proof, step_circuit, &pk.constants)?
      .expect("synthesis should return value");

    let (X, W) = cs.to_assignments();
    assert_eq!(X.len(), 3);
    assert_eq!(X[1], X[2]); // TOD HACK IO needs to be even
    let X = X[1];

    let witness = NIVCUpdateWitness {
      index: circuit_index,
      X,
      W,
    };

    let step_proof = self.update(pk, &witness)?;

    Ok(RecursiveSNARKProof {
      verifier_state,
      step_proof,
    })
  }

  pub fn verify(
    &self,
    pk: &ProvingKey<E>,
    // proof: &RecursiveSNARKProof<E>,
  ) -> Result<(), SuperNovaError> {
    // ) -> Result<NIVCIO<E>, SuperNovaError> {
    // for (acc, acc_hash) in zip_eq(self.accs, proof.)

    for (acc, shape) in zip_eq(&self.accs, &pk.shapes) {
      acc.verify(&pk.ck, shape)?;
    }
    self.acc_cf.verify(&pk.ck_cf, &pk.shape_cf)?;
    Ok(())
  }

  pub fn merge(
    pk: &ProvingKey<E>,
    self_L: Self,
    proof_L: RecursiveSNARKProof<E>,
    self_R: Self,
    proof_R: RecursiveSNARKProof<E>,
  ) -> Result<(Self, RecursiveSNARKProof<E>), NovaError> {
    let RecursiveSNARKProof {
      verifier_state: verifier_state_L,
      step_proof: step_proof_L,
    } = proof_L;
    let RecursiveSNARKProof {
      verifier_state: verifier_state_R,
      step_proof: step_proof_R,
    } = proof_R;

    let mut transcript = Transcript::new(
      pk.constants.transcript.clone(),
      [
        verifier_state_L.transcript_state,
        verifier_state_R.transcript_state,
      ],
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

    let mut acc_cf = RelaxedSecondaryR1CS::<E>::merge(
      &pk.ck_cf,
      &pk.shape_cf,
      self_L.acc_cf,
      self_R.acc_cf,
      &mut transcript,
    );
    acc_sm
      .finalize(&pk.ck_cf, &pk.shape_cf, &mut acc_cf, &mut transcript)
      .unwrap();

    let (_, transcript_buffer) = transcript.seal();

    let mut self_next = Self { accs, acc_cf };

    let merge_proof = NIVCMergeProof {
      step_proof_L,
      step_proof_R,
      transcript_buffer: Some(transcript_buffer),
      accs_L: accs_L_instance,
      accs_R: accs_R_instance,
    };

    let mut cs = SatisfyingAssignment::<E>::new();
    let verifier_state = VerifierState::synthesize_merge(
      &mut cs,
      verifier_state_L,
      verifier_state_R,
      merge_proof,
      &pk.constants,
    )?
    .unwrap();

    let (X, W) = cs.to_assignments();
    assert_eq!(X.len(), 3);
    assert_eq!(X[1], X[2]); // TOD HACK IO needs to be even
    let X = X[1];

    // Index of merge
    let merge_circuit_index = pk.shapes.len() - 1;

    let witness = NIVCUpdateWitness {
      index: merge_circuit_index,
      X,
      W,
    };

    let step_proof = self_next.update(pk, &witness)?;
    let proof = RecursiveSNARKProof {
      verifier_state,
      step_proof,
    };
    Ok((self_next, proof))
  }

  fn update(
    &mut self,
    pk: &ProvingKey<E>,
    witness: &NIVCUpdateWitness<E>,
  ) -> Result<NIVCStepProof<E>, NovaError> {
    let mut transcript = Transcript::new(pk.constants.transcript.clone(), [witness.X]);

    let mut acc_sm = ScalarMulAccumulator::new();

    let index_prev = witness.index;
    let acc_prev = &mut self.accs[index_prev];
    let acc_prev_instance = acc_prev.instance().clone();

    let shape_prev = &pk.shapes[index_prev];

    // Fold the proof for the previous iteration into the correct accumulator
    acc_prev.fold(
      &pk.ck,
      shape_prev,
      witness.X,
      &witness.W,
      &mut acc_sm,
      &mut transcript,
    );
    acc_sm.finalize(&pk.ck_cf, &pk.shape_cf, &mut self.acc_cf, &mut transcript)?;

    let (_, transcript_buffer) = transcript.seal();

    let proof = NIVCStepProof {
      transcript_buffer: Some(transcript_buffer),
      acc: acc_prev_instance,
      index: Some(index_prev),
    };

    Ok(proof)
  }
}

#[cfg(test)]
mod tests {
  use bellpepper_core::test_cs::TestConstraintSystem;
  use expect_test::expect;
  use ff::Field;

  use crate::parafold::test::TrivialNonUniform;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;
  use crate::traits::snark::default_ck_hint;

  use super::*;

  type Scalar = <E as Engine>::Scalar;

  #[test]
  fn test_new() {
    let num_circuits: usize = 1;
    let nc = TrivialNonUniform::<E>::new(num_circuits);
    let circuit = nc.primary_circuit(0);
    let constants = NIVCPoseidonConstants::<E>::new();

    let verifier_state = VerifierState::<E>::dummy(circuit.arity(), num_circuits);
    let step_proof = NIVCStepProof::<E>::dummy();

    let mut cs = TestConstraintSystem::<Scalar>::new();
    let _ = verifier_state
      .synthesize_step(&mut cs, step_proof, &circuit, &constants)
      .unwrap();

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied().unwrap());
    }

    expect!["18682"].assert_eq(&cs.num_constraints().to_string());
  }

  #[test]
  fn test_prove_step() {
    let num_circuits: usize = 2;
    let nc = TrivialNonUniform::<E>::new(num_circuits);
    let pk = ProvingKey::<E>::setup(&nc, &*default_ck_hint(), &*default_ck_hint());

    let pc_init = 0;
    let z_init = vec![Scalar::ZERO];

    println!("NEW");
    let (mut snark, mut proof) = RecursiveSNARK::new(&pk, pc_init, z_init);

    for i in 0..3 {
      println!("{i}");
      proof = snark
        .prove_step(&pk, &nc.primary_circuit(i % num_circuits), proof)
        .unwrap();
    }
    snark.verify(&pk).unwrap();
  }

  #[test]
  fn test_prove_merge() {
    let num_circuits: usize = 2;
    let nc = TrivialNonUniform::<E>::new(num_circuits);
    let pk = ProvingKey::<E>::setup(&nc, &*default_ck_hint(), &*default_ck_hint());

    let pc_init_L = 0;
    let z_init_L = vec![Scalar::from(0)];
    let pc_init_R = 1;
    let z_init_R = vec![Scalar::from(1)];

    println!("NEW");
    let (mut snark_L, mut proof_L) = RecursiveSNARK::new(&pk, pc_init_L, z_init_L);
    let (mut snark_R, mut proof_R) = RecursiveSNARK::new(&pk, pc_init_R, z_init_R);

    proof_L = snark_L
      .prove_step(&pk, &nc.primary_circuit(0), proof_L)
      .unwrap();
    proof_R = snark_R
      .prove_step(&pk, &nc.primary_circuit(1), proof_R)
      .unwrap();

    snark_L.verify(&pk).unwrap();
    snark_R.verify(&pk).unwrap();
    let (snark, _proof) = RecursiveSNARK::merge(&pk, snark_L, proof_L, snark_R, proof_R).unwrap();
    snark.verify(&pk).unwrap();
  }

  #[test]
  fn test_merge() {
    let num_circuits: usize = 1;
    let nc = TrivialNonUniform::<E>::new(num_circuits);
    let pk = ProvingKey::<E>::setup(&nc, &*default_ck_hint(), &*default_ck_hint());

    let pc_init = 0;
    let z_init = vec![Scalar::from(0)];

    println!("NEW");
    let (snark_L, proof_L) = RecursiveSNARK::new(&pk, pc_init, z_init.clone());
    let (snark_R, proof_R) = RecursiveSNARK::new(&pk, pc_init, z_init.clone());

    let (snark, _proof) = RecursiveSNARK::merge(&pk, snark_L, proof_L, snark_R, proof_R).unwrap();
    snark.verify(&pk).unwrap();
  }
}
