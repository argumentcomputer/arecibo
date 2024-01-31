use super::nova_circuit::FoldingData;

use crate::{
  gadgets::{
    ecc::AllocatedPoint,
    r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
  },
  traits::{commitment::CommitmentTrait, Engine, ROCircuitTrait},
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
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    let U = AllocatedRelaxedR1CSInstance::alloc(
      cs.namespace(|| "U"),
      inst.map(|x| &x.U),
      limb_width,
      n_limbs,
    )?;

    let u = AllocatedR1CSInstance::alloc(cs.namespace(|| "U"), inst.map(|x| &x.u))?;

    let T = AllocatedPoint::alloc(cs.namespace(|| "T"), inst.map(|x| x.T.to_coordinates()))?;
    T.check_on_curve(cs.namespace(|| "T on curve"))?;

    Ok(Self { U, u, T })
  }

  pub fn absorb_in_ro<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
    ro: &mut E::ROCircuit,
  ) -> Result<(), SynthesisError> {
    self.U.absorb_in_ro(cs.namespace(|| "absorb U"), ro)?;
    self.u.absorb_in_ro(ro);
    ro.absorb(&self.T.x);
    ro.absorb(&self.T.y);
    ro.absorb(&self.T.is_infinity);
    Ok(())
  }
}

pub mod emulated {
  use bellpepper_core::boolean::Boolean;

  use super::*;

  use std::marker::PhantomData;

  use crate::gadgets::nonnative::bignat::BigNat;
  use crate::traits::ROConstantsCircuit;
  use crate::RelaxedR1CSInstance;

  #[derive(Clone)]
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

    pub fn absorb_in_ro<CS>(&self, cs: CS, ro: &mut E1::ROCircuit) -> Result<(), SynthesisError>
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
      x0: &BigNat<E1::Base>,
      x1: &BigNat<E1::Base>,
      ro_consts: ROConstantsCircuit<E1>,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
      todo!()
    }

    pub fn absorb_in_ro<CS>(&self, cs: CS, ro: &mut E1::ROCircuit) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }

    pub fn conditionally_select<CS: ConstraintSystem<<E1 as Engine>::Base>>(
      &self,
      cs: CS,
      other: &Self,
      condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
      todo!()
    }

    pub fn default<CS: ConstraintSystem<<E1 as Engine>::Base>>(
      mut cs: CS,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
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

    pub fn absorb_in_ro<CS>(&self, cs: CS, ro: &mut E1::ROCircuit) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      todo!()
    }
  }
}
