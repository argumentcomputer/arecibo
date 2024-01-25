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
  pub U: AllocatedRelaxedR1CSInstance<E>,
  pub u: AllocatedR1CSInstance<E>,
  pub T: AllocatedPoint<E>,
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
  use super::*;

  use std::marker::PhantomData;

  use crate::gadgets::nonnative::bignat::BigNat;
  use crate::traits::ROConstantsCircuit;
  use crate::RelaxedR1CSInstance;

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

    pub fn absorb_in_ro<CS>(&self, cs: CS, ro: &mut E1::ROCircuit)
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }

    pub fn check_on_curve<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }
  }

  pub struct AllocatedRelaxedR1CSInstance<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    W: AllocatedPoint<E1, E2>,
    E: AllocatedPoint<E1, E2>,
    u: BigNat<E1::Base>,
    x0: BigNat<E1::Base>,
    x1: BigNat<E1::Base>,
    pub _p: PhantomData<E2>,
  }

  impl<E1, E2> AllocatedRelaxedR1CSInstance<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    pub fn alloc<CS>(
      mut cs: CS,
      inst: Option<&RelaxedR1CSInstance<E2>>,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }

    pub fn fold_with_r1cs<CS: ConstraintSystem<<E1 as Engine>::Base>>(
      &self,
      mut cs: CS,
      W_new: AllocatedPoint<E1, E2>,
      E_new: AllocatedPoint<E1, E2>,
      x0: BigNat<E1::Base>,
      x1: BigNat<E1::Base>,
      ro_consts: ROConstantsCircuit<E1>,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
      todo!()
    }

    pub fn absorb_in_ro<CS>(&self, cs: CS, ro: &mut E1::ROCircuit)
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
    pub U: AllocatedRelaxedR1CSInstance<E1, E2>,
    pub u_W: AllocatedPoint<E1, E2>,
    pub u_x0: BigNat<E1::Base>,
    pub u_x1: BigNat<E1::Base>,
    pub T: AllocatedPoint<E1, E2>,
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

    pub fn absorb_in_ro<CS>(&self, cs: CS, ro: &mut E1::ROCircuit)
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }
  }
}
