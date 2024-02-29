mod circuit;
#[allow(dead_code)]
mod cycle_fold;
#[allow(dead_code)]
mod nifs;
#[allow(dead_code)]
mod nivc;
#[allow(dead_code)]
mod prover;
#[allow(dead_code)]
mod transcript;

// pub struct ProvingKey<E: Engine> {
//   /// Commitment Key
//   ck: CommitmentKey<E>,
//   /// Random oracle constants used for hashing io of the self verification circuit.
//   ro_consts: ROConstants<E>,

//   /// Public Parameter digest
//   pp: E::Scalar,
//   /// Shape of the self verification circuit
//   shape: R1CSShape<E>,
//   /// Proving keys for each NIVC [StepCircuit]s
//   nivc: Vec<IVCProvingKey<E>>,
// }

// pub struct IVCProvingKey<E: Engine> {
//   pp: E::Scalar,
//   shape: R1CSShape<E>,
// }
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
