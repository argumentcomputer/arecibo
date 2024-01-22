use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::parafold::ecc::AllocatedPoint;
use crate::parafold::nifs_secondary::prover::SecondaryRelaxedR1CSInstance;
use crate::parafold::nifs_secondary::{
  AllocatedSecondaryFoldProof, AllocatedSecondaryMergeProof, AllocatedSecondaryRelaxedR1CSInstance,
};
use crate::parafold::nifs_secondary::{SecondaryFoldProof, SecondaryMergeProof};
use crate::traits::commitment::CommitmentTrait;
use crate::traits::Engine;

impl<E1: Engine, E2: Engine> AllocatedSecondaryRelaxedR1CSInstance<E1, E2> {
  pub fn alloc_infallible<CS, FI>(/*mut*/ _cs: CS, _instance: FI) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FI: FnOnce() -> SecondaryRelaxedR1CSInstance<E2>,
  {
    // Both u, X need to be allocated as BigInt
    todo!()
    // let SecondaryRelaxedR1CSInstance { u, X, W, E } = instance();
    // let u = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc u"), || u);
    // let X = X
    //   .into_iter()
    //   .enumerate()
    //   .map(|(i, X)| AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc X[{i}]")), || X))
    //   .collect();
    // let W = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc W"), || W);
    // let E = AllocatedHashedCommitment::alloc_infallible(cs.namespace(|| "alloc E"), || E);
    //
    // Self {
    //   u: BigNat::alloc_from_nat(),
    //   X: vec![],
    //   W: (),
    //   E: (),
    // }
  }

  pub fn to_native(&self) -> Result<SecondaryRelaxedR1CSInstance<E2>, SynthesisError> {
    todo!()
    // let u = self
    //   .u
    //   .get_value()
    //   .ok_or(SynthesisError::AssignmentMissing)?;
    // let X = self
    //   .X
    //   .iter()
    //   .map(|x| x.get_value().ok_or(SynthesisError::AssignmentMissing))
    //   .collect::<Result<Vec<_>, _>>()?;
    // let W = self.W.to_native()?;
    // let E = self.W.to_native()?;
    //
    // Ok(RelaxedR1CSInstance { u, X, W, E })
  }
}

impl<E1, E2> AllocatedSecondaryFoldProof<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FP>(mut cs: CS, fold_proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> SecondaryFoldProof<E2>,
  {
    let SecondaryFoldProof { W, T } = fold_proof();
    let W = AllocatedPoint::alloc(cs.namespace(|| "alloc W"), Some(W.to_coordinates())).unwrap();
    let T = AllocatedPoint::alloc(cs.namespace(|| "alloc T"), Some(T.to_coordinates())).unwrap();

    Self { W, T }
  }
}

impl<E1, E2> AllocatedSecondaryMergeProof<E1, E2>
where
  E1: Engine,
  E2: Engine<Base = E1::Scalar>,
{
  pub fn alloc_infallible<CS, FP>(mut cs: CS, merge_proof: FP) -> Self
  where
    CS: ConstraintSystem<E1::Scalar>,
    FP: FnOnce() -> SecondaryMergeProof<E2>,
  {
    let SecondaryMergeProof { T } = merge_proof();
    let T = AllocatedPoint::alloc(cs.namespace(|| "alloc T"), Some(T.to_coordinates())).unwrap();

    Self { T }
  }
}
