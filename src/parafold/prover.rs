use std::sync::Arc;

use bellpepper_core::ConstraintSystem;
use neptune::hash_type::HashType;
use neptune::Strength;
use rayon::prelude::*;

use crate::bellpepper::r1cs::NovaShape;
use crate::bellpepper::shape_cs::ShapeCS;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::CommitmentKey;
use crate::parafold::circuit::synthesize_step;
use crate::parafold::cycle_fold::prover::ScalarMulInstance;
use crate::parafold::nivc::NIVCUpdateProof;
use crate::parafold::nivc::prover::{NIVCState, NIVCUpdateWitness};
use crate::parafold::transcript::TranscriptConstants;
use crate::r1cs::{commitment_key_size, CommitmentKeyHint, R1CSShape};
use crate::supernova::{NonUniformCircuit, StepCircuit};
use crate::traits::{CurveCycleEquipped, Engine};
use crate::traits::commitment::CommitmentEngineTrait;

pub struct ProvingKey<E: CurveCycleEquipped> {
  // public params
  ck: Arc<CommitmentKey<E>>,
  ck_cf: Arc<CommitmentKey<E::Secondary>>,
  // Shapes for each augmented StepCircuit. The last shape is for the merge circuit.
  arity: usize,
  shapes: Vec<R1CSShape<E>>,
  shape_cf: R1CSShape<E::Secondary>,
  ro_consts: TranscriptConstants<E::Scalar>,
}

impl<E: CurveCycleEquipped> ProvingKey<E> {
  pub fn setup<NC: NonUniformCircuit<E>>(
    non_uniform_circuit: &NC,
    ck_hint1: &CommitmentKeyHint<E>,
    ck_hint2: &CommitmentKeyHint<E::Secondary>,
  ) -> Self {
    let num_circuits_nivc = non_uniform_circuit.num_circuits();
    // total number of circuits also contains merge circuit.
    let num_circuits = num_circuits_nivc; // +1 when supporting merge
    let transcript_constants = TranscriptConstants::<E::Scalar>::new_with_strength_and_type(
      Strength::Standard,
      HashType::Sponge,
    );
    let arity = non_uniform_circuit.primary_circuit(0).arity();
    let default_proof =
      NIVCUpdateProof::<E>::dummy(transcript_constants.clone(), arity, num_circuits);

    let circuits = (0..num_circuits)
      .map(|i| non_uniform_circuit.primary_circuit(i))
      .collect::<Vec<_>>();
    let shapes = circuits
      .into_par_iter()
      .map(|circuit| {
        assert_eq!(circuit.arity(), arity);

        let mut cs: ShapeCS<E> = ShapeCS::new();
        let _ = synthesize_step(
          &mut cs,
          &transcript_constants,
          default_proof.clone(),
          &circuit,
        )
        .unwrap();
        // We use the largest commitment_key for all instances
        cs.r1cs_shape()
      })
      .collect::<Vec<_>>();

    let shape_cf = {
      let mut cs: ShapeCS<E::Secondary> = ShapeCS::new();
      let dummy = ScalarMulInstance::<E>::dummy();
      dummy.synthesize(&mut cs).unwrap();
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

    let ro_consts = TranscriptConstants::<E::Scalar>::new_with_strength_and_type(
      Strength::Standard,
      HashType::Sponge,
    );

    Self {
      ck,
      ck_cf,
      arity,
      shapes,
      shape_cf,
      ro_consts,
    }
  }
}

pub struct RecursiveSNARK<E: CurveCycleEquipped> {
  // state
  state: NIVCState<E>,
  proof: NIVCUpdateProof<E>,
}

impl<E: CurveCycleEquipped> RecursiveSNARK<E> {
  pub fn new(pk: &ProvingKey<E>, pc_init: usize, z_init: Vec<E::Scalar>) -> Self {
    let num_circuits = pk.shapes.len();
    assert!(pc_init < num_circuits);
    assert_eq!(z_init.len(), pk.arity);

    let (state, proof) = NIVCState::new(&pk.shapes, &pk.shape_cf, pc_init, z_init, &pk.ro_consts);

    Self { state, proof }
  }

  pub fn prove_step<C: StepCircuit<E::Scalar>>(self, pk: &ProvingKey<E>, step_circuit: &C) -> Self {
    let Self { mut state, proof } = self;
    let circuit_index = step_circuit.circuit_index();
    let mut cs = SatisfyingAssignment::<E>::new();
    let (io_next, alloc_state) =
      synthesize_step(&mut cs, &pk.ro_consts, proof, step_circuit).unwrap();

    let (X, W) = cs.to_assignments();

    state.io.update(io_next.unwrap());
    let state_instance = state.instance();
    debug_assert!(alloc_state.eq_native(&state_instance).unwrap());

    debug_assert_eq!(state_instance.hash(), X[1]);
    debug_assert_eq!(state.transcript_state, X[2]);

    let witness = NIVCUpdateWitness {
      index: circuit_index,
      W: W.to_vec(),
    };

    let (state, proof) = state.update(
      &pk.ck,
      &pk.ck_cf,
      &pk.ro_consts,
      &pk.shapes,
      &pk.shape_cf,
      &witness,
    );

    Self { state, proof }
  }

  pub fn verify(&self, pk: &ProvingKey<E>) -> bool {
    self
      .state
      .verify(&pk.ck, &pk.ck_cf, &pk.shapes, &pk.shape_cf)
      .expect("f");
    true
  }

  //   pub fn merge<C: StepCircuit<E1::Scalar>>(
  //     pk: &ProvingKey<E1>,
  //     self_L: Self,
  //     self_R: &Self,
  //   ) -> Self {
  //     let Self {
  //       state: state_L,
  //       proof: proof_L,
  //     } = self_L;
  //     let Self {
  //       state: state_R,
  //       proof: proof_R,
  //     } = self_R;
  //
  //     let mut transcript = Transcript::new();
  //
  //     let (state, proof) = NIVCState::merge(
  //       &pk.ck,
  //       &pk.shapes,
  //       state_L,
  //       state_R,
  //       proof_L,
  //       proof_R.clone(),
  //       &mut transcript,
  //     );
  //
  //     let circuit_index = pk.shapes.len();
  //     let mut cs = SatisfyingAssignment::<E1>::new();
  //     let state_instance = AllocatedNIVCState::new_merge(&mut cs, &pk.nivc_hasher, proof).unwrap();
  //     let W = cs.aux_assignment();
  //     // assert state_instance == state.instance
  //     let witness = NIVCUpdateWitness {
  //       state: state_instance,
  //       index: circuit_index,
  //       W: W.to_vec(),
  //     };
  //
  //     let mut transcript = Transcript::new();
  //
  //     let proof = state.update(
  //       &pk.ck,
  //       &pk.shapes,
  //       &pk.nivc_hasher,
  //       &witness,
  //       &mut transcript,
  //     );
  //
  //     Self { state, proof }
  //   }
}

#[cfg(test)]
mod tests {
  use std::marker::PhantomData;

  use bellpepper_core::{ConstraintSystem, SynthesisError};
  use bellpepper_core::num::AllocatedNum;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use expect_test::expect;
  use ff::PrimeField;

  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;
  use crate::traits::snark::default_ck_hint;

  use super::*;

  type Scalar = <E as Engine>::Scalar;

  type CS = TestConstraintSystem<Scalar>;

  #[derive(Clone, Debug)]
  struct TrivialCircuit<F: PrimeField> {
    index: usize,
    pc_next: usize,
    _marker: PhantomData<F>,
  }

  impl<F: PrimeField> StepCircuit<F> for TrivialCircuit<F> {
    fn arity(&self) -> usize {
      0
    }

    fn circuit_index(&self) -> usize {
      self.index
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      _pc: Option<&AllocatedNum<F>>,
      _z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
      let pc_next = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc"), || {
        F::from(self.pc_next as u64)
      });
      Ok((Some(pc_next), vec![]))
    }
  }

  #[derive(Clone, Debug)]
  struct TrivialNonUniform<E: CurveCycleEquipped> {
    num_circuits: usize,
    _marker: PhantomData<E>,
  }

  impl<E: CurveCycleEquipped> NonUniformCircuit<E> for TrivialNonUniform<E> {
    type C1 = TrivialCircuit<E::Scalar>;
    type C2 = TrivialCircuit<E::Base>;

    fn num_circuits(&self) -> usize {
      self.num_circuits
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
      TrivialCircuit {
        index: circuit_index,
        pc_next: (circuit_index + 1) % self.num_circuits,
        _marker: Default::default(),
      }
    }

    fn secondary_circuit(&self) -> Self::C2 {
      TrivialCircuit {
        index: 0,
        pc_next: 0,
        _marker: Default::default(),
      }
    }
  }

  #[test]
  fn test_new() {
    let num_circuits: usize = 1;
    let nc = TrivialNonUniform::<E> {
      num_circuits,
      _marker: Default::default(),
    };
    let circuit = nc.primary_circuit(0);
    let ro_consts = TranscriptConstants::<Scalar>::new();

    let proof = NIVCUpdateProof::<E>::dummy(ro_consts.clone(), circuit.arity(), num_circuits);

    let mut cs = TestConstraintSystem::<Scalar>::new();
    let _ = synthesize_step(&mut cs, &ro_consts, proof.clone(), &circuit).unwrap();

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied().unwrap());
    }

    expect![["18752"]].assert_eq(&cs.num_constraints().to_string());
  }

  #[test]
  fn test_prove_step() {
    let num_circuits: usize = 2;
    let nc = TrivialNonUniform::<E> {
      num_circuits,
      _marker: Default::default(),
    };
    let pk = ProvingKey::<E>::setup(&nc, &*default_ck_hint(), &*default_ck_hint());

    let pc_init = 0;
    let z_init = vec![];

    println!("NEW");
    let mut snark = RecursiveSNARK::new(&pk, pc_init, z_init);

    for i in 0..5 {
      println!("{i}");
      snark = snark.prove_step(&pk, &nc.primary_circuit(i % num_circuits));
    }
    assert!(snark.verify(&pk))
  }
}
