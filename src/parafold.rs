use ff::PrimeField;
use itertools::chain;

use crate::r1cs::R1CSShape;
use crate::traits::{Engine, ROConstants};
use crate::{Commitment, CommitmentKey};

mod circuit;
mod prover;

pub struct ProvingKey<E: Engine> {
  /// Commitment Key
  ck: CommitmentKey<E>,
  /// Random oracle constants used for hashing io of the self verification circuit.
  ro_consts: ROConstants<E>,

  /// Public Parameter digest
  pp: E::Scalar,
  /// Shape of the self verification circuit
  shape: R1CSShape<E>,
  /// Proving keys for each NIVC [StepCircuit]s
  nivc: Vec<IVCProvingKey<E>>,
}

pub struct IVCProvingKey<E: Engine> {
  pp: E::Scalar,
  shape: R1CSShape<E>,
}

#[derive(Clone)]
pub struct R1CSInstance<E: Engine> {
  W: Commitment<E>,
  X: Vec<E::Scalar>,
}

pub struct R1CSWitness<E: Engine> {
  W: Vec<E::Scalar>,
}

pub struct R1CSProof<E: Engine> {
  instance: R1CSInstance<E>,
  witness: R1CSWitness<E>,
}

#[derive(Clone)]
pub struct RelaxedR1CSInstance<E: Engine> {
  W: Commitment<E>,
  X: Vec<E::Scalar>,
  u: E::Scalar,
  E: Commitment<E>,
}

impl<E: Engine> RelaxedR1CSInstance<E> {
  pub(crate) fn default(_shape: &R1CSShape<E>) -> Self {
    todo!()
  }
}

pub struct RelaxedR1CSWitness<E: Engine> {
  W: Vec<E::Scalar>,
  E: Vec<E::Scalar>,
}

impl<E: Engine> RelaxedR1CSWitness<E> {
  pub fn default(_shape: &R1CSShape<E>) -> Self {
    todo!()
  }
}

pub struct RelaxedR1CSAccumulator<E: Engine> {
  instance: RelaxedR1CSInstance<E>,
  witness: RelaxedR1CSWitness<E>,
}

#[derive(Clone)]
pub struct NIFSProof<E: Engine> {
  T: Commitment<E>,
}

#[derive(Clone)]
pub struct FoldProof<E: Engine> {
  instance: R1CSInstance<E>,
  proof: NIFSProof<E>,
  // TODO: add CycleFold proof
}

#[derive(Clone)]
pub struct NIVCState<F: PrimeField> {
  pc: usize,
  z: Vec<F>,
}

#[derive(Clone)]
pub struct NIVCProof<E: Engine> {
  input: NIVCState<E::Scalar>,
  output: NIVCState<E::Scalar>,
  proof: FoldProof<E>,
}

pub struct NIVCWitness<E: Engine> {
  input: NIVCState<E::Scalar>,
  output: NIVCState<E::Scalar>,
  proof: R1CSProof<E>,
}

impl<E: Engine> RelaxedR1CSAccumulator<E> {
  fn default(shape: &R1CSShape<E>) -> Self {
    let witness = RelaxedR1CSWitness::default(shape);
    let instance = RelaxedR1CSInstance::default(shape);
    Self { instance, witness }
  }

  /// Fold the proof for the previous state transition, producing an accumulator for the current state,
  /// and a proof to be consumed by the verifier.
  pub fn nifs_fold(
    _ck: &CommitmentKey<E>,
    _ro_consts: &ROConstants<E>,
    _shape: &R1CSShape<E>,
    _pp: &E::Scalar,
    _acc_curr: Self,
    _circuit_proof: R1CSProof<E>,
  ) -> (Self, FoldProof<E>) {
    todo!()
    //
    // let SelfProof {
    //   instance: proof_witness_commitment_curr,
    //   witness: proof_witness_curr,
    // } = proof_curr;
    // let RelaxedR1CSAccumulator {
    //   instance: acc_instance_curr,
    //   witness: acc_witness_curr,
    // } = acc_curr;
    //
    // let proof_instance_curr = R1CSInstance {
    //   comm_W: proof_witness_commitment_curr,
    //   X: vec![hash_prev, hash_curr],
    // };
    //
    // let (fold_proof_T, (acc_instance_next, acc_witness_next)) = NIFS::prove(
    //   &pk.ck,
    //   &pk.ro_consts,
    //   &pk.pp,
    //   &pk.shape,
    //   &acc_instance_curr,
    //   &acc_witness_curr,
    //   &proof_instance_curr,
    //   &proof_witness_curr,
    // )
    //     .unwrap();
    //
    // let fold_proof = FoldProof {
    //   witness: proof_witness_commitment_curr,
    //   proof: Commitment::<E>::decompress(&fold_proof_T.comm_T).unwrap(),
    // };
    //
    // let acc_next = RelaxedR1CSAccumulator {
    //   instance: acc_instance_next,
    //   witness: acc_witness_next,
    // };
    //
    // (acc_next, fold_proof)
  }

  pub fn nifs_fold_many(
    _ck: &CommitmentKey<E>,
    _ro_consts: &ROConstants<E>,
    _shape: &R1CSShape<E>,
    _pp: &E::Scalar,
    _accs_curr: Vec<Option<Self>>,
    _index: usize,
    _circuit_proof: R1CSProof<E>,
  ) -> (Vec<Option<Self>>, FoldProof<E>) {
    // fn fold_nivc(
    //   pk: &ProvingKey<E>,
    //   state_curr: NIVCState<E::Scalar>,
    //   mut accs: Vec<Option<RelaxedR1CSAccumulator<E>>>,
    //   proof: NIVCProof<E>,
    // ) -> (
    //   Vec<Option<RelaxedR1CSAccumulator<E>>>,
    //   NIVCState<E::Scalar>,
    //   FoldProof<E>,
    // ) {
    //   // Unpack the witness of the circuit computing
    //   //   `(pc_next, z_next) = F_{pc_curr}(z_curr)`
    //   let NIVCProof {
    //     input,
    //     output,
    //     proof,
    //   } = proof;
    //   // let NIVCProof {
    //   //   output: state_next,
    //   //   witness: proof_witness_next,
    //   //   instance: proof_witness_commitment_next,
    //   // } = proof;
    //
    //   // Get the `io = {pc_curr, z_curr, pc_next, z_next}`, and the proving key for `F_{pc_curr}`
    //
    //   let pc_curr = state_curr.pc;
    //   let pk_curr = &pk.nivc[pc_curr];
    //
    //   // Convert witness commitment and io into Nova instance
    //   let proof_instance_next = R1CSInstance {
    //     comm_W: proof_witness_commitment_next,
    //     X: NIVCState::io_vec(state_curr, state_next.clone()),
    //   };
    //
    //   // Load the existing accumulator for `pc_curr`, or load a default one.
    //   let acc_curr =
    //     accs[pc_curr].get_or_insert_with(|| RelaxedR1CSAccumulator::default(&pk_curr.shape));
    //
    //   let RelaxedR1CSAccumulator {
    //     instance: acc_instance_curr,
    //     witness: acc_witness_curr,
    //   } = acc_curr;
    //
    //   // Fold the proof for io into `acc_curr`, along with a folding proof for the verifier.
    //   let (fold_proof_T, (acc_instance_next, acc_witness_next)) = NIFS::prove(
    //     &pk.ck,
    //     &pk.ro_consts,
    //     &pk_curr.pp,
    //     &pk_curr.shape,
    //     &acc_instance_curr,
    //     &acc_witness_curr,
    //     &proof_instance_next,
    //     &proof_witness_next,
    //   )
    //   .unwrap();
    //
    //   // Update the accumulator at the index of the folded NIVC circuit
    //   accs[pc_curr] = Some(RelaxedR1CSAccumulator {
    //     instance: acc_instance_next,
    //     witness: acc_witness_next,
    //   });
    //
    //   let fold_proof_next = FoldProof {
    //     witness: proof_witness_commitment_next,
    //     proof: Commitment::<E>::decompress(&fold_proof_T.comm_T).unwrap(),
    //   };
    //
    //   // Return the output state, and a folding proof of the folding
    //   (accs, state_next, fold_proof_next)
    todo!()
  }
}

impl<F: PrimeField> NIVCState<F> {
  pub fn io_vec(input: Self, output: Self) -> Vec<F> {
    let NIVCState { pc: pc_in, z: z_in } = input;
    let NIVCState {
      pc: pc_out,
      z: z_out,
    } = output;

    chain!(
      [F::from(pc_in as u64)],
      z_in.into_iter(),
      [F::from(pc_out as u64)],
      z_out.into_iter()
    )
    .collect()
  }
}
