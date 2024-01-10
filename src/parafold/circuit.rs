use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};

use crate::gadgets::r1cs::AllocatedRelaxedR1CSInstance;
use crate::parafold::circuit::nivc::AllocatedNIVCIO;
use crate::parafold::circuit::scalar_mul::AllocatedScalarMulInstance;
use crate::parafold::circuit::transcript::AllocatedTranscript;
use crate::parafold::{NIVCProof, ProvingKey};
use crate::traits::{Engine, ROConstantsCircuit};

mod nifs;
mod nivc;
mod scalar_mul;
mod transcript;

struct AllocatedRecursionState<E: Engine> {
  self_acc: AllocatedRelaxedR1CSInstance<E>,
  nivc_acc: Vec<AllocatedRelaxedR1CSInstance<E>>,
  nivc_state: AllocatedNIVCIO<E>,
}

impl<E: Engine> AllocatedRecursionState<E> {}

/// Given the state transition over the io
///   `self_state = (vk_self, vk_nivc, self_acc, nivc_acc, nivc_io)`
/// self_io = {self_state_curr, self_state_next}
pub struct StateTransitionCircuit<E: Engine> {
  ro_consts: ROConstantsCircuit<E>,

  pp_self: AllocatedNum<E::Scalar>,
  pp_nivc: Vec<AllocatedNum<E::Scalar>>,

  state: AllocatedRecursionState<E>,

  scalar_mul_instances: Vec<AllocatedScalarMulInstance<E>>,

  transcript: AllocatedTranscript<E::Scalar>,
  // vec of cycle fold proofs to be verified in a batch
}

impl<E: Engine> StateTransitionCircuit<E> {
  pub fn new<CS>(
    mut cs: CS,
    pk: &ProvingKey<E>,
    self_acc_prev: RelaxedR1CSInstance<E>,
    nivc_acc_curr: impl IntoIterator<Item = Option<RelaxedR1CSInstance<E>>>,
    nivc_state: NIVCState<E::Scalar>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let ro_consts = ROConstantsCircuit::<E>::default();

    let pp_self = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pp_self"), || pk.pp);
    let pp_nivc = pk
      .nivc
      .iter()
      .enumerate()
      .map(|(i, pk_nivc)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc pp_nivc[{i}]")), || {
          pk_nivc.pp
        })
      })
      .collect::<Vec<_>>();

    let self_acc_prev = AllocatedRelaxedR1CSInstance::alloc_infallible(
      cs.namespace(|| "alloc self_acc_prev"),
      || self_acc_prev,
    );

    let nivc_acc_curr = nivc_acc_curr
      .into_iter()
      .enumerate()
      .map(|(i, nivc_acc)| {
        AllocatedRelaxedR1CSInstance::alloc_infallible(
          cs.namespace(|| format!("alloc nivc_acc_prev[{i}]")),
          || nivc_acc.unwrap_or(RelaxedR1CSInstance::default(&pk.nivc[i].shape)),
        )
      })
      .collect::<Vec<_>>();

    let nivc_state =
      AllocatedNIVCIO::alloc_infallible(cs.namespace(|| "alloc nivc_state"), || nivc_state);

    Ok(Self {
      ro_consts,
      pp_self,
      pp_nivc,
      self_acc: self_acc_prev,
      nivc_acc: nivc_acc_curr,
      nivc_state,
      scalar_mul_instances: vec![],
      transcript: AllocatedTranscript::new()?,
    })
  }

  pub(crate) fn fold_self<CS>(
    mut self,
    mut cs: CS,
    self_fold_proof_curr: FoldProof<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let X = &self_fold_proof_curr.instance.X;

    assert_eq!(X.len(), 2);

    let self_io_hash_curr: AllocatedNum<E::Scalar> = Self::io_hash(
      cs.namespace(|| "self_io_hash_curr"),
      &self.ro_consts,
      &self.pp_self,
      &self.pp_nivc,
      &self.self_acc, // self_acc_prev
      &self.nivc_acc, // self_acc_curr
      &self.nivc_state,
    )?;

    // TODO: Replace with constraint
    assert_eq!(X[1], self_io_hash_curr.get_value().unwrap());

    // If self_fold_proof_curr.X[1] = 0, then we are in the base case
    // assert
    // self_acc = default
    // nivc_acc = 0
    // nivc_state_init = nivc_state_curr

    self_io_hash_curr.inputize(cs.namespace(|| "inputize self_io_hash_curr"))?;

    let self_fold_proof_curr =
      AllocatedFoldProof::alloc_infallible(cs.namespace(|| "alloc self_fold_proof_curr"), || {
        self_fold_proof_curr
      });

    let (self_acc_curr, scalar_mul_instances) = self.self_acc.nifs_fold(
      cs.namespace(|| "fold self_acc_prev"),
      self_fold_proof_curr,
      &mut self.transcript,
    )?;

    self.self_acc = self_acc_curr;
    self.scalar_mul_instances.extend(scalar_mul_instances);
    Ok(self)
  }

  pub(crate) fn fold_many_nivc<CS>(
    mut cs: CS,
    accs_curr: Vec<AllocatedRelaxedR1CSInstance<E>>,
    state_curr: AllocatedNIVCIO<E>,
    proofs: Vec<FoldProof<E>>,
    transcript: &mut AllocatedTranscript<E>,
  ) -> Result<(Vec<AllocatedRelaxedR1CSInstance<E>>, AllocatedNIVCIO<E>), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let num_scalar_mul_instances = 2 * proofs.len();

    let (accs_next, state_next) = proofs.into_iter().enumerate().try_fold(
      (
        accs_curr,
        state_curr,
        Vec::with_capacity(num_scalar_mul_instances),
      ),
      |(accs_curr, state_curr, scalar_mul_instances), (i, proof)| {
        let NIVCProof {
          io: state,
          proof: fold_proof,
        } = proof;

        // Absorb
        let fold_proof = AllocatedFoldProof::alloc_infallible(
          cs.namespace(|| format!("alloc fold_proof[{i}]")),
          || fold_proof,
        );
        let state = AllocatedNIVCIO::alloc_infallible(
          cs.namespace(|| format!("alloc state[{i}]")),
          || state,
        );

        transcript.absorb(cs.namespace(|| format!("absorb state[{i}]")), &state)?;
        transcript.absorb(
          cs.namespace(|| format!("absorb fold_proof[{i}]")),
          &fold_proof,
        )?;

        // sanity check that we are folding the right io
        // assert_eq(nivc_state_curr.get_value(), input)

        // is_zk = (nivc_state_curr == nivc_state_next)
        // if this is true, then skip io check, and allow for a random E

        let pc_curr = input.pc;

        let _io = AllocatedNIVCIO::io_vec(nivc_state_curr.clone(), nivc_state_next.clone());

        // TODO: Enforce io == fold_proof_next.instance.X

        AllocatedRelaxedR1CSInstance::nifs_fold_many(
          cs.namespace(|| format!("fold_many {i}")),
          accs_curr,
          0,
          AllocatedFoldProof {},
          &mut AllocatedTranscript {},
        )?;

        // TODO: Add conditional selection logic
        let nivc_acc_next = AllocatedRelaxedR1CSInstance::nifs_fold_many(
          cs.namespace(|| format!("fold nivc_proof[{i}]")),
          nivc_acc_curr,
          pc_curr,
          &self.pp_nivc,
          &self.ro_consts,
          fold_proof_next,
        )?;

        Ok::<_, SynthesisError>((nivc_acc_next, nivc_state_next))
      },
    )?;

    // given all verifier outputs, apply the reduction to each step
    self.nivc_acc = nivc_acc_next;
    self.nivc_state_curr = nivc_state_next;
    Ok(self)
  }

  pub(crate) fn finalize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let self_io_hash_next: AllocatedNum<E::Scalar> = Self::io_hash(
      cs.namespace(|| "self_io_hash_next"),
      &self.ro_consts,
      &self.pp_self,
      &self.pp_nivc,
      &self.self_acc, // self_acc_curr
      &self.nivc_acc, // self_acc_next
      &self.nivc_state,
    )?;

    self_io_hash_next.inputize(cs.namespace(|| "inputize self_io_hash_curr"))
  }

  fn io_hash<CS>(
    /*mut*/ _cs: CS,
    _ro_consts: &ROConstantsCircuit<E>,
    _pp_self: &AllocatedNum<E::Scalar>,
    _pp_nivc: &[AllocatedNum<E::Scalar>],
    _self_acc: &AllocatedRelaxedR1CSInstance<E>,
    _nivc_acc: &[AllocatedRelaxedR1CSInstance<E>],
    _nivc_state: &AllocatedNIVCIO<E::Scalar>,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    todo!()
  }
}
