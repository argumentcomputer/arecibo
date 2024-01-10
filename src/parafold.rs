use ff::{Field, PrimeField};

use crate::parafold::prover::SelfState;
use crate::r1cs::R1CSShape;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::{Engine, ROConstants, TranscriptEngineTrait};
use crate::CommitmentKey;

mod circuit;
mod nifs;
mod nivc;
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
//
// #[derive(Clone)]
// pub struct NIVCProof<E: Engine> {
//   io: NIVCState<E::Scalar>,
//   proof: FoldProof<E>,
// }
//
// pub struct NIVCWitness<E: Engine> {
//   io: NIVCState<E::Scalar>,
//   proof: R1CSProof<E>,
// }

// struct Prover<E: Engine> {
//   state: SelfState<E>,
//
//   transcript: E::TE,
//   scalar_mul_instances: Vec<ScalarMulInstance<E>>,
// }
//
// impl<E: Engine> Prover<E> {
//
//   /// Given
//   pub fn new(pk: &ProvingKey<E>, state: SelfState<E>, proof: &R1CSProof<E>) -> Self {
//     let mut transcript = E::TE::new(b"fold");
//
//
//   }
//
//   ///
//   // pub fn new_merge(state_L: SelfState<E>, state_R: SelfState<E>, proof_L: &R1CSProof<E>, proof_R: &R1CSProof<E>) -> Self {
//   //
//   // }
// }
