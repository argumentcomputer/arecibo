use std::sync::Arc;

use bellpepper_core::ConstraintSystem;
use neptune::hash_type::HashType;
use neptune::Strength;
use rayon::prelude::*;

use crate::bellpepper::r1cs::NovaShape;
use crate::bellpepper::shape_cs::ShapeCS;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::CommitmentKey;
use crate::errors::NovaError;
use crate::parafold::circuit::{synthesize_merge, synthesize_step};
use crate::parafold::cycle_fold::nifs::prover::RelaxedSecondaryR1CS;
use crate::parafold::cycle_fold::prover::ScalarMulInstance;
use crate::parafold::nifs::prover::RelaxedR1CS;
use crate::parafold::nivc::{NIVCCircuitInput, NIVCIO, NIVCMergeProof};
use crate::parafold::nivc::prover::NIVCState;
use crate::parafold::transcript::TranscriptConstants;
use crate::r1cs::{commitment_key_size, CommitmentKeyHint, R1CSShape};
use crate::supernova::{NonUniformCircuit, StepCircuit};
use crate::traits::{CurveCycleEquipped, Engine};
use crate::traits::commitment::CommitmentEngineTrait;

pub struct ProvingKey<E: CurveCycleEquipped> {
  // public params
  pub(crate) ck: Arc<CommitmentKey<E>>,
  pub(crate) ck_cf: Arc<CommitmentKey<E::Secondary>>,
  // Shapes for each augmented StepCircuit. The last shape is for the merge circuit.
  pub(crate) arity: usize,
  pub(crate) shapes: Vec<R1CSShape<E>>,
  pub(crate) shape_cf: R1CSShape<E::Secondary>,
  pub(crate) ro_consts: TranscriptConstants<E::Scalar>,
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
    let transcript_constants = TranscriptConstants::<E::Scalar>::new_with_strength_and_type(
      Strength::Standard,
      HashType::Sponge,
    );
    let arity = non_uniform_circuit.primary_circuit(0).arity();

    let dummy_input =
      NIVCCircuitInput::<E>::dummy(transcript_constants.clone(), arity, num_circuits);
    let dummy_merge_proof = NIVCMergeProof::<E>::dummy(transcript_constants.clone(), num_circuits);

    let circuits = (0..num_circuits_nivc)
      .map(|i| non_uniform_circuit.primary_circuit(i))
      .collect::<Vec<_>>();
    let mut shapes = circuits
      .into_par_iter()
      .map(|circuit| {
        assert_eq!(circuit.arity(), arity);

        let mut cs: ShapeCS<E> = ShapeCS::new();
        let _ = synthesize_step(
          &mut cs,
          &dummy_input,
          transcript_constants.clone(),
          &circuit,
        )
        .unwrap();
        // We use the largest commitment_key for all instances
        cs.r1cs_shape()
      })
      .collect::<Vec<_>>();
    let shape_merge = {
      let mut cs: ShapeCS<E> = ShapeCS::new();
      let _ = synthesize_merge(
        &mut cs,
        &dummy_input,
        &dummy_input,
        dummy_merge_proof,
        transcript_constants.clone(),
      )
      .unwrap();
      cs.r1cs_shape()
    };
    shapes.push(shape_merge);

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

#[derive(Debug)]
pub struct RecursiveSNARK<E: CurveCycleEquipped> {
  state: NIVCState<E>,

  circuit_input: NIVCCircuitInput<E>,
}

#[derive(Debug)]
pub struct NIVCUpdateWitness<E: CurveCycleEquipped> {
  pub(crate) index: usize,
  pub(crate) X: E::Scalar,
  pub(crate) W: Vec<E::Scalar>,
  pub(crate) io_next: NIVCIO<E>,
}

impl<E: CurveCycleEquipped> RecursiveSNARK<E> {
  /// Initialize the prover state and create a default proof for the first iteration.
  ///
  /// # Details
  ///
  /// In the first iteration, the circuit verifier checks the base-case conditions, but does not update any
  /// of the accumulators. To ensure uniformity with the non-base case path, the transcript will be updated
  /// in the normal way, albeit with dummy proof data.
  pub fn new(pk: &ProvingKey<E>, pc_init: usize, z_init: Vec<E::Scalar>) -> Self {
    let num_circuits = pk.shapes.len();
    assert!(pc_init < num_circuits);
    assert_eq!(z_init.len(), pk.arity);

    let io = NIVCIO::new(pc_init, z_init);
    let accs = pk.shapes.iter().map(RelaxedR1CS::new).collect();
    let acc_cf = RelaxedSecondaryR1CS::new(&pk.shape_cf);

    let mut state = NIVCState::new(io, accs, acc_cf);

    let circuit_input = state.init(pk.ro_consts.clone());

    Self {
      state,
      circuit_input,
    }
  }

  pub fn prove_step<C: StepCircuit<E::Scalar>>(
    &mut self,
    pk: &ProvingKey<E>,
    step_circuit: &C,
  ) -> Result<(), NovaError> {
    let circuit_index = step_circuit.circuit_index();

    let mut cs = SatisfyingAssignment::<E>::new();
    let io_next = synthesize_step(
      &mut cs,
      &self.circuit_input,
      pk.ro_consts.clone(),
      step_circuit,
    )?
    .unwrap();

    let (X, W) = cs.to_assignments();
    assert_eq!(X.len(), 3);
    assert_eq!(X[1], X[2]); // TOD HACK IO needs to be even

    let witness = NIVCUpdateWitness {
      index: circuit_index,
      X: X[1],
      W,
      io_next,
    };

    self.circuit_input = self.state.update(pk, &witness)?;

    Ok(())
  }

  pub fn verify(&self, pk: &ProvingKey<E>) -> bool {
    self
      .state
      .verify(&pk.ck, &pk.ck_cf, &pk.shapes, &pk.shape_cf)
      .expect("f");
    true
  }

  pub fn merge(pk: &ProvingKey<E>, self_L: Self, self_R: Self) -> Result<Self, NovaError> {
    let (mut state, proof) = NIVCState::merge(pk, self_L.state, self_R.state);

    let mut cs = SatisfyingAssignment::<E>::new();
    let io = synthesize_merge(
      &mut cs,
      &self_L.circuit_input,
      &self_R.circuit_input,
      proof,
      pk.ro_consts.clone(),
    )?
    .unwrap();

    let (X, W) = cs.to_assignments();
    assert_eq!(X.len(), 3);
    assert_eq!(X[1], X[2]); // TOD HACK IO needs to be even

    let index = pk.shapes.len() - 1;

    let witness = NIVCUpdateWitness {
      index,
      X: X[1],
      W,
      io_next: io,
    };

    let circuit_input = state.update(pk, &witness)?;

    Ok(Self {
      state,
      circuit_input,
    })
  }
}

#[cfg(test)]
mod tests {
  use std::marker::PhantomData;

  use bellpepper_core::{ConstraintSystem, SynthesisError};
  use bellpepper_core::num::AllocatedNum;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use expect_test::expect;
  use ff::{Field, PrimeField};

  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::Engine;
  use crate::traits::snark::default_ck_hint;

  use super::*;

  type Scalar = <E as Engine>::Scalar;

  #[derive(Clone, Debug)]
  struct TrivialCircuit<F: PrimeField> {
    index: usize,
    pc_next: usize,
    _marker: PhantomData<F>,
  }

  impl<F: PrimeField> StepCircuit<F> for TrivialCircuit<F> {
    fn arity(&self) -> usize {
      1
    }

    fn circuit_index(&self) -> usize {
      self.index
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      _pc: Option<&AllocatedNum<F>>,
      z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
      let pc_next = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc"), || {
        F::from(self.pc_next as u64)
      });

      let z_next = AllocatedNum::alloc(cs.namespace(|| "alloc z_next"), || {
        let z_next = z[0].get_value().unwrap_or_default();
        Ok(z_next + F::ONE)
      })?;
      Ok((Some(pc_next), vec![z_next]))
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

    let inputs = NIVCCircuitInput::<E>::dummy(ro_consts.clone(), circuit.arity(), num_circuits);

    let mut cs = TestConstraintSystem::<Scalar>::new();
    let _ = synthesize_step(&mut cs, &inputs, ro_consts, &circuit).unwrap();

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied().unwrap());
    }

    expect!["18682"].assert_eq(&cs.num_constraints().to_string());
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
    let z_init = vec![Scalar::ZERO];

    println!("NEW");
    let mut snark = RecursiveSNARK::new(&pk, pc_init, z_init);

    for i in 0..3 {
      println!("{i}");
      snark
        .prove_step(&pk, &nc.primary_circuit(i % num_circuits))
        .unwrap();
    }
    assert!(snark.verify(&pk))
  }

  #[test]
  fn test_prove_merge() {
    let num_circuits: usize = 2;
    let nc = TrivialNonUniform::<E> {
      num_circuits,
      _marker: Default::default(),
    };
    let pk = ProvingKey::<E>::setup(&nc, &*default_ck_hint(), &*default_ck_hint());

    let pc_init_L = 0;
    let z_init_L = vec![Scalar::from(0)];
    let pc_init_R = 1;
    let z_init_R = vec![Scalar::from(1)];

    println!("NEW");
    let mut snark_L = RecursiveSNARK::new(&pk, pc_init_L, z_init_L);
    let mut snark_R = RecursiveSNARK::new(&pk, pc_init_R, z_init_R);

    snark_L.prove_step(&pk, &nc.primary_circuit(0)).unwrap();
    snark_R.prove_step(&pk, &nc.primary_circuit(1)).unwrap();

    assert!(snark_L.verify(&pk));
    assert!(snark_R.verify(&pk));
    let snark = RecursiveSNARK::merge(&pk, snark_L, snark_R).unwrap();
    assert!(snark.verify(&pk));
  }

  #[test]
  fn test_merge() {
    let num_circuits: usize = 1;
    let nc = TrivialNonUniform::<E> {
      num_circuits,
      _marker: Default::default(),
    };
    let pk = ProvingKey::<E>::setup(&nc, &*default_ck_hint(), &*default_ck_hint());

    let pc_init = 0;
    let z_init = vec![Scalar::from(0)];

    println!("NEW");
    let snark_L = RecursiveSNARK::new(&pk, pc_init, z_init.clone());
    let snark_R = RecursiveSNARK::new(&pk, pc_init, z_init.clone());

    let snark = RecursiveSNARK::merge(&pk, snark_L, snark_R).unwrap();
    assert!(snark.verify(&pk));
  }
}
