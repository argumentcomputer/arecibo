use bellpepper_core::ConstraintSystem;

use crate::bellpepper::solver::SatisfyingAssignment;
use crate::parafold::cycle_fold::HashedCommitment;
use crate::parafold::nivc::hash::NIVCHasher;
use crate::parafold::nivc::prover::{NIVCState, NIVCUpdateWitness};
use crate::parafold::nivc::{AllocatedNIVCState, NIVCUpdateProof};
use crate::parafold::transcript::prover::Transcript;
use crate::r1cs::R1CSShape;
use crate::traits::circuit_supernova::StepCircuit;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::Engine;

pub struct CommitmentKey<E: Engine> {
  // TODO: ro for secondary circuit to compute the hash of the point
  // this should only be a 2-to-1 hash since we are hashing the coordinates
  ck: crate::CommitmentKey<E>,
}

impl<E: Engine> CommitmentKey<E> {
  pub fn commit(&self, elements: &[E::Scalar]) -> HashedCommitment<E> {
    let c = E::CE::commit(&self.ck, elements);
    HashedCommitment::new(c)
  }
}

pub struct ProvingKey<E1: Engine> {
  // public params
  ck: CommitmentKey<E1>,
  nivc_hasher: NIVCHasher<E1>,
  shapes: Vec<R1CSShape<E1>>,
}

pub struct RecursiveSNARK<E1: Engine, E2: Engine> {
  // state
  state: NIVCState<E1, E2>,
  proof: NIVCUpdateProof<E1, E2>,
}

impl<E1, E2> RecursiveSNARK<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  // pub fn new(pc_init: usize, shapes: &[R1CSShape<E1::Scalar>]) -> Self {
  //   let num_circuits = shapes.len();
  //   let arity = assert!(pc_init < num_circuits);
  // }

  pub fn prove_step<C: StepCircuit<E1::Scalar>>(
    mut self,
    pk: &ProvingKey<E1>,
    step_circuit: C,
  ) -> Self {
    let Self { mut state, proof } = self;
    let circuit_index = step_circuit.circuit_index();
    let mut cs = SatisfyingAssignment::<E1>::new();
    let state_instance =
      AllocatedNIVCState::new_step(&mut cs, &pk.nivc_hasher, proof, step_circuit).unwrap();
    let W = cs.aux_assignment();
    // assert state_instance == state.instance
    let witness = NIVCUpdateWitness {
      state: state_instance,
      index: circuit_index,
      W: W.to_vec(),
    };

    let mut transcript = Transcript::new();

    let proof = state.update(
      &pk.ck,
      &pk.shapes,
      &pk.nivc_hasher,
      &witness,
      &mut transcript,
    );

    Self { state, proof }
  }
  // pub fn merge<C: StepCircuit<E1::Scalar>>(
  //   pk: &ProvingKey<E1>,
  //   self_L: Self,
  //   self_R: &Self,
  // ) -> Self {
  //   let Self {
  //     state: state_L,
  //     proof: proof_L,
  //   } = self_L;
  //   let Self {
  //     state: state_R,
  //     proof: proof_R,
  //   } = self_R;
  //
  //   let mut transcript = Transcript::new();
  //
  //   let (state, proof) = NIVCState::merge(
  //     &pk.ck,
  //     &pk.shapes,
  //     state_L,
  //     state_R,
  //     proof_L,
  //     proof_R.clone(),
  //     &mut transcript,
  //   );
  //
  //   let circuit_index = pk.shapes.len();
  //   let mut cs = SatisfyingAssignment::<E1>::new();
  //   let state_instance = AllocatedNIVCState::new_merge(&mut cs, &pk.nivc_hasher, proof).unwrap();
  //   let W = cs.aux_assignment();
  //   // assert state_instance == state.instance
  //   let witness = NIVCUpdateWitness {
  //     state: state_instance,
  //     index: circuit_index,
  //     W: W.to_vec(),
  //   };
  //
  //   let mut transcript = Transcript::new();
  //
  //   let proof = state.update(
  //     &pk.ck,
  //     &pk.shapes,
  //     &pk.nivc_hasher,
  //     &witness,
  //     &mut transcript,
  //   );
  //
  //   Self { state, proof }
  // }
}

pub struct CompressedSNARK<E1: Engine, E2: Engine> {}
