use bellpepper_core::ConstraintSystem;

use crate::bellpepper::r1cs::NovaWitness;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::parafold::circuit::StateTransitionCircuit;
use crate::parafold::nifs::RelaxedR1CS;
use crate::parafold::nivc::NIVCIO;
use crate::parafold::ProvingKey;
use crate::traits::{Engine, TranscriptEngineTrait};

pub mod cyclefold;

pub struct RecursionState<E: Engine> {
  hash_inputs: Vec<E::Scalar>,
  self_acc_prev: RelaxedR1CS<E>,
  nivc_acc_curr: Vec<Option<RelaxedR1CS<E>>>,
  nivc_state: NIVCIO<E::Scalar>,
  // self_input_hashes: Vec<E::Scalar>,
  // scalar_mul_instances: Vec<ScalarMulInstance<E>>,
  // self_proof_curr: R1CSProof<E>,
}

pub struct Prover<E: Engine> {
  state: RecursionState<E>,
}

impl<E: Engine> RecursionState<E> {
  pub fn new(_pk: &ProvingKey<E>) -> Self {
    todo!()
  }

  fn fold_proofs(self, pk: &ProvingKey<E>, nivc_witnesses: &[NIVCWitness<E>]) -> Self {
    let mut transcript = E::TE::new(b"fold");
    let self_io_hash_curr = self.io_hash();

    // Destructure current state
    let Self {
      self_acc_prev,
      nivc_acc_curr,
      nivc_state: nivc_state_curr,
      self_proof_curr,
    } = self;

    // sanity check
    assert_eq!(self_proof_curr.instance.X.len(), 2);
    assert_eq!(self_proof_curr.instance.X[1], self_io_hash_curr);

    let mut cs = SatisfyingAssignment::<E>::with_capacity(pk.shape.num_io + 1, pk.shape.num_vars);

    let circuit = StateTransitionCircuit::new(
      cs.namespace(|| "circuit init"),
      pk,
      self_acc_prev.instance.clone(),
      nivc_acc_curr
        .iter()
        .map(|acc| acc.as_ref().map(|acc| acc.instance.clone())),
      nivc_state_curr.clone(),
    );

    // Fold the proof of the current state into the accumulator for `Self`
    // Generate a proof adding the witness of the current accumulator
    let (self_acc_curr, self_fold_proof_curr, self_fold_scalar_mul_instances) =
      RelaxedR1CSAccumulator::nifs_fold(
        &pk.ck,
        &pk.shape,
        self_acc_prev,
        &self_proof_curr,
        &mut transcript,
      );
    let circuit = circuit
      .fold_self(cs.namespace(|| "circuit fold self"), self_fold_proof_curr)
      .unwrap();

    // Fold a list of `m` proofs into the current NIVC accumulator.
    // Generate the outputs of each NIVC circuit, and a folding proof
    let (nivc_acc_next, nivc_state_next, nivc_folding_proofs) =
      Self::fold_many_nivc(pk, nivc_acc_curr, nivc_state_curr, nivc_witnesses);

    let circuit = circuit
      .fold_many_nivc(cs.namespace(|| "circuit fold nivc"), nivc_folding_proofs)
      .unwrap();

    circuit
      .finalize(cs.namespace(|| "circuit finalize"))
      .unwrap();

    let self_proof_next: R1CSProof<E> = Self::prove_transition(pk, cs);

    Self {
      self_acc_prev: self_acc_curr,
      nivc_acc_curr: nivc_acc_next,
      nivc_state: nivc_state_next,
      self_proof_curr: self_proof_next,
    }
  }

  /// Compute a collision-resistant hash of the circuit's state.
  fn io_hash(&self) -> E::Scalar {
    todo!()
  }

  /// Given a list NIVC accumulators `accs_init` that resulted in the computation of `state_init`,
  /// and a list of NIVC proofs of `m` sequential iterations, this function folds all the proofs into an `accs_init`,
  /// and returns proofs of this folding.   
  fn fold_many_nivc(
    pk: &ProvingKey<E>,
    accs_init: Vec<Option<RelaxedR1CSAccumulator<E>>>,
    nivc_state_init: NIVCIO<E::Scalar>,
    nivc_witnesses: &[NIVCWitness<E>],
  ) -> (
    Vec<Option<RelaxedR1CSAccumulator<E>>>,
    NIVCIO<E::Scalar>,
    Vec<NIVCProof<E>>,
  ) {
    let num_iters = nivc_witnesses.len();

    let mut fold_proofs = Vec::with_capacity(num_iters);

    let (accs_next, nivc_state_next) = nivc_witnesses.iter().fold(
      (accs_init, nivc_state_init),
      |(accs_curr, nivc_state_curr), witness| {
        let NIVCWitness { io, proof } = witness;

        // assert_eq!(nivc_state_curr, input);

        let pc = nivc_state_curr.pc;

        let (accs_next, proof) = RelaxedR1CSAccumulator::nifs_fold_many(
          &pk.ck,
          &pk.ro_consts,
          &pk.nivc[pc].shape,
          &pk.nivc[pc].pp,
          accs_curr,
          pc,
          proof,
        );

        let nifs_state_next = output.clone();

        fold_proofs.push(NIVCProof {
          input,
          output,
          proof,
        });

        (accs_next, nifs_state_next)
      },
    );
    (accs_next, nivc_state_next, fold_proofs)
  }

  // /// Create a proof for the circuit verifying the current state transition.
  // fn prove_transition<CS: ConstraintSystem<E::Scalar> + NovaWitness<E>>(
  //   pk: &ProvingKey<E>,
  //   cs: CS,
  // ) -> R1CSProof<E> {
  //   let (instance, witness) = cs
  //     .r1cs_instance_and_witness(&pk.shape, &pk.ck)
  //     .map_err(|_e| NovaError::UnSat)
  //     .expect("Nova error unsat");
  //   let instance = R1CSInstance {
  //     W: instance.comm_W,
  //     X: instance.X,
  //   };
  //   let witness = R1CSWitness { W: witness.W };
  //
  //   R1CSProof { instance, witness }
  // }
}
