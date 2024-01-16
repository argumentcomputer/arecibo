use crate::traits::{Engine, ROConstantsCircuit};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::Field;

pub struct AllocatedTranscript<E: Engine> {
  ro_consts: ROConstantsCircuit<E>,
  hash_prev: Option<AllocatedNum<E::Scalar>>,
}

impl<E: Engine> AllocatedTranscript<E> {
  pub fn new<CS>() -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Ok(Self {
      ro_consts: ROConstantsCircuit::<E>::default(),
      hash_prev: None,
    })
  }
  pub fn absorb<CS, T>(&mut self, /*mut*/ _cs: CS, _element: &T) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // TODO
    Ok(())
  }

  pub fn squeeze<CS>(&mut self, mut cs: CS) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // TODO
    Ok(AllocatedNum::alloc_infallible(
      cs.namespace(|| "alloc challenge"),
      || E::Scalar::ONE,
    ))
  }
}
