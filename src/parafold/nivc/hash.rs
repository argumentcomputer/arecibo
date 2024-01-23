use crate::traits::{Engine, ROConstants, ROConstantsCircuit};
use bellpepper_core::num::AllocatedNum;

pub struct NIVCHasher<E: Engine> {
  ro_consts: ROConstants<E>,
  pp: E::Scalar,
  arity: usize,
}

pub struct AllocatedNIVCHasher<E: Engine> {
  ro_consts: ROConstantsCircuit<E>,
  pp: AllocatedNum<E::Scalar>,
  arity: usize,
}

impl<E: Engine> NIVCHasher<E> {
  pub fn new(ro_consts: ROConstantsCircuit<E>, pp: AllocatedNum<E::Scalar>, arity: usize) -> Self {
    Self {
      ro_consts,
      pp,
      arity,
    }
  }
}

impl<E: Engine> AllocatedNIVCHasher<E> {}
