use crate::bellpepper::solver::SatisfyingAssignment;
use crate::parafold::circuit::synthesize_step;
use crate::parafold::nivc::prover::{NIVCState, NIVCUpdateWitness};
use crate::parafold::nivc::NIVCUpdateProof;
use crate::parafold::transcript::TranscriptConstants;
use crate::r1cs::R1CSShape;
use crate::supernova::StepCircuit;
use crate::traits::CurveCycleEquipped;
use crate::CommitmentKey;
use bellpepper_core::ConstraintSystem;

pub struct ProvingKey<E: CurveCycleEquipped> {
  // public params
  ck: CommitmentKey<E>,
  ck_cf: CommitmentKey<E::Secondary>,
  // Shapes for each augmented StepCircuit. The last shape is for the merge circuit.
  shapes: Vec<R1CSShape<E>>,
  shape_cf: R1CSShape<E::Secondary>,
  ro_consts: TranscriptConstants<E::Scalar>,
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
    // Check arity z_init.len();

    let (state, proof) = NIVCState::new(&pk.shapes, &pk.shape_cf, pc_init, z_init, &pk.ro_consts);

    Self { state, proof }
  }

  pub fn prove_step<C: StepCircuit<E::Scalar>>(self, pk: &ProvingKey<E>, step_circuit: &C) -> Self {
    let Self { state, proof } = self;
    let circuit_index = step_circuit.circuit_index();
    let mut cs = SatisfyingAssignment::<E>::new();
    let io = synthesize_step(&mut cs, &pk.ro_consts, proof, step_circuit).unwrap();
    let W = cs.aux_assignment();

    let witness = NIVCUpdateWitness {
      index: circuit_index,
      W: W.to_vec(),
      io,
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
