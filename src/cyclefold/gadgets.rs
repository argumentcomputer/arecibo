use super::nova_circuit::FoldingData;

use crate::{
  gadgets::{
    ecc::AllocatedPoint,
    r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
  },
  traits::Engine,
};

use bellpepper_core::{ConstraintSystem, SynthesisError};
pub struct AllocatedFoldingData<E: Engine> {
  U: AllocatedRelaxedR1CSInstance<E>,
  u: AllocatedR1CSInstance<E>,
  T: AllocatedPoint<E>,
}

impl<E: Engine> AllocatedFoldingData<E> {
  pub fn alloc<CS: ConstraintSystem<<E as Engine>::Base>>(
    mut cs: CS,
    inst: Option<&FoldingData<E>>,
  ) -> Result<Self, SynthesisError> {
    todo!()
  }

  pub fn absorb_in_ro(&self, ro: &mut E::ROCircuit) {
    todo!()
  }
}

pub mod emulated {
  use std::marker::PhantomData;

  use super::*;
  use crate::gadgets::nonnative::bignat::BigNat;

  pub struct AllocatedPoint<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    x: BigNat<E1::Base>,
    y: BigNat<E1::Base>,
    is_infinity: BigNat<E1::Base>,
    _p: PhantomData<E2>,
  }

  impl<E1, E2> AllocatedPoint<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    pub fn alloc<CS>(
      mut cs: CS,
      coords: Option<(E2::Base, E2::Base, bool)>,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }

    pub fn absorb_in_ro(&self, ro: &mut E1::ROCircuit) {
      todo!()
    }

    pub fn check_on_curve<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }
  }

  pub struct AllocatedFoldingData<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    U_W: AllocatedPoint<E1, E2>,
    U_E: AllocatedPoint<E1, E2>,
    U_u: BigNat<E1::Base>,
    U_X0: BigNat<E1::Base>,
    U_X1: BigNat<E1::Base>,
    u_W: AllocatedPoint<E1, E2>,
    u_x0: BigNat<E1::Base>,
    u_x1: BigNat<E1::Base>,
    T: AllocatedPoint<E1, E2>,
    _p: PhantomData<E2>,
  }

  impl<E1, E2> AllocatedFoldingData<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    pub fn alloc<CS>(mut cs: CS, inst: Option<&FoldingData<E2>>) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }

    pub fn absorb_in_ro(&self, ro: &mut E1::ROCircuit) {
      todo!()
    }
  }
}
