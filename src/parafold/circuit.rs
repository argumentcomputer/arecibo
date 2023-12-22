use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use itertools::chain;

use crate::parafold::{
  FoldProof, NIVCProof, NIVCState, ProvingKey, R1CSInstance, RelaxedR1CSInstance,
};
use crate::traits::{Engine, ROConstantsCircuit};
use crate::Commitment;

// TODO: This represents a non-native point
struct AllocatedCommitment<E: Engine> {
  x: AllocatedNum<E::Scalar>,
  y: AllocatedNum<E::Scalar>,
}

impl<E: Engine> AllocatedCommitment<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, _commitment: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> Commitment<E>,
  {
    let x = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc x"), || E::Scalar::ZERO);
    let y = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc y"), || E::Scalar::ZERO);
    Self { x, y }
  }
}

#[derive(Clone)]
struct AllocatedNIVCState<F: PrimeField> {
  pc: AllocatedNum<F>,
  z: Vec<AllocatedNum<F>>,
}

impl<F: PrimeField> AllocatedNIVCState<F> {
  pub fn alloc_infallible<CS, N>(mut cs: CS, state: N) -> Self
  where
    CS: ConstraintSystem<F>,
    N: FnOnce() -> NIVCState<F>,
  {
    let NIVCState { pc, z } = state();
    let pc = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc"), || F::from(pc as u64));
    let z = z
      .into_iter()
      .enumerate()
      .map(|(i, z)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z[{i}]")), || z))
      .collect();

    Self { pc, z }
  }

  pub fn io_vec(input: Self, output: Self) -> Vec<AllocatedNum<F>> {
    let AllocatedNIVCState { pc: pc_in, z: z_in } = input;
    let AllocatedNIVCState {
      pc: pc_out,
      z: z_out,
    } = output;

    chain!([pc_in], z_in.into_iter(), [pc_out], z_out.into_iter()).collect()
  }
}

struct AllocatedFoldProof<E: Engine> {
  instance: AllocatedR1CSInstance<E>,
  proof: AllocatedCommitment<E>,
}

impl<E: Engine> AllocatedFoldProof<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, fold_proof: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> FoldProof<E>,
  {
    let FoldProof { instance, proof } = fold_proof();
    let instance =
      AllocatedR1CSInstance::alloc_infallible(cs.namespace(|| "alloc instance"), || instance);
    let proof = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc proof"), || proof.T);
    Self { instance, proof }
  }
}

struct AllocatedR1CSInstance<E: Engine> {
  W: AllocatedCommitment<E>,
  X: Vec<AllocatedNum<E::Scalar>>,
}

impl<E: Engine> AllocatedR1CSInstance<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, instance: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> R1CSInstance<E>,
  {
    let R1CSInstance { W, X } = instance();
    let W = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let X = X
      .into_iter()
      .enumerate()
      .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
      .collect();

    Self { W, X }
  }
}

struct AllocatedRelaxedR1CSInstance<E: Engine> {
  W: AllocatedCommitment<E>,
  E: AllocatedCommitment<E>,
  u: AllocatedNum<E::Scalar>,
  X: Vec<AllocatedNum<E::Scalar>>,
}

impl<E: Engine> AllocatedRelaxedR1CSInstance<E> {
  pub fn alloc_infallible<CS, F>(mut cs: CS, instance: F) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
    F: FnOnce() -> RelaxedR1CSInstance<E>,
  {
    let RelaxedR1CSInstance { W, X, u, E } = instance();
    let W = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    let X = X
      .into_iter()
      .enumerate()
      .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
      .collect();
    let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || u);
    let E = AllocatedCommitment::alloc_infallible(cs.namespace(|| "alloc E"), || E);

    Self { W, X, u, E }
  }

  pub fn nifs_fold<CS>(
    mut _cs: CS,
    acc_curr: Self,
    _pp: &AllocatedNum<E::Scalar>,
    _ro_consts: &ROConstantsCircuit<E>,
    _proof: AllocatedFoldProof<E>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Ok(acc_curr)
  }

  pub fn nifs_fold_many<CS>(
    mut _cs: CS,
    accs_curr: Vec<Self>,
    _index: usize,
    _pp: &[AllocatedNum<E::Scalar>],
    _ro_consts: &ROConstantsCircuit<E>,
    _proof: AllocatedFoldProof<E>,
  ) -> Result<Vec<Self>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Ok(accs_curr)
  }
}

/// Given the state transition over the io
///   `self_state = (vk_self, vk_nivc, self_acc, nivc_acc, nivc_io)`
/// self_io = {self_state_curr, self_state_next}
pub struct StateTransitionCircuit<E: Engine> {
  ro_consts: ROConstantsCircuit<E>,

  pp_self: AllocatedNum<E::Scalar>,
  pp_nivc: Vec<AllocatedNum<E::Scalar>>,

  self_acc: AllocatedRelaxedR1CSInstance<E>,
  nivc_acc: Vec<AllocatedRelaxedR1CSInstance<E>>,

  nivc_state_init: AllocatedNIVCState<E::Scalar>,
  nivc_state_curr: AllocatedNIVCState<E::Scalar>,
}

impl<E: Engine> StateTransitionCircuit<E> {
  pub fn new<CS>(
    mut cs: CS,
    pk: &ProvingKey<E>,
    self_acc_prev: RelaxedR1CSInstance<E>,
    nivc_acc_curr: impl IntoIterator<Item = Option<RelaxedR1CSInstance<E>>>,
    nivc_state_init: NIVCState<E::Scalar>,
    nivc_state_curr: NIVCState<E::Scalar>,
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

    let nivc_state_init =
      AllocatedNIVCState::alloc_infallible(cs.namespace(|| "alloc nivc_state_init"), || {
        nivc_state_init
      });
    let nivc_state_curr =
      AllocatedNIVCState::alloc_infallible(cs.namespace(|| "alloc nivc_state_curr"), || {
        nivc_state_curr
      });

    Ok(Self {
      ro_consts,
      pp_self,
      pp_nivc,
      self_acc: self_acc_prev,
      nivc_acc: nivc_acc_curr,
      nivc_state_init,
      nivc_state_curr,
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
      &self.nivc_state_init,
      &self.nivc_state_curr,
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

    let self_acc_curr = AllocatedRelaxedR1CSInstance::nifs_fold(
      cs.namespace(|| "fold self_acc_prev"),
      self.self_acc,
      &self.pp_self,
      &self.ro_consts,
      self_fold_proof_curr,
    )?;

    self.self_acc = self_acc_curr;
    Ok(self)
  }

  pub(crate) fn fold_many_nivc<CS>(
    mut self,
    mut cs: CS,
    proofs: impl IntoIterator<Item = NIVCProof<E>>,
  ) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let (nivc_acc_next, nivc_state_next) = proofs.into_iter().enumerate().try_fold(
      (self.nivc_acc, self.nivc_state_curr),
      |(nivc_acc_curr, nivc_state_curr), (i, proof)| {
        let NIVCProof {
          input,
          output,
          proof,
        } = proof;

        // sanity check that we are folding the right io
        // assert_eq(nivc_state_curr.get_value(), input)

        let nivc_state_next = AllocatedNIVCState::alloc_infallible(
          cs.namespace(|| format!("alloc nivc_state[{i}]")),
          || output,
        );
        let fold_proof_next = AllocatedFoldProof::alloc_infallible(
          cs.namespace(|| format!("alloc fold_proof[{i}]")),
          || proof,
        );

        // is_zk = (nivc_state_curr == nivc_state_next)
        // if this is true, then skip io check, and allow for a random E

        let pc_curr = input.pc;

        let _io = AllocatedNIVCState::io_vec(nivc_state_curr.clone(), nivc_state_next.clone());

        // TODO: Enforce io == fold_proof_next.instance.X

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
      &self.nivc_state_init,
      &self.nivc_state_curr,
    )?;

    self_io_hash_next.inputize(cs.namespace(|| "inputize self_io_hash_curr"))
  }
  fn io_hash<CS>(
    mut _cs: CS,
    _ro_consts: &ROConstantsCircuit<E>,
    _pp_self: &AllocatedNum<E::Scalar>,
    _pp_nivc: &[AllocatedNum<E::Scalar>],
    _self_acc: &AllocatedRelaxedR1CSInstance<E>,
    _nivc_acc: &[AllocatedRelaxedR1CSInstance<E>],
    _nivc_state_curr: &AllocatedNIVCState<E::Scalar>,
    _nivc_state_next: &AllocatedNIVCState<E::Scalar>,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    todo!()
  }
}
