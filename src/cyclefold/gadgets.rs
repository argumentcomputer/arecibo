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
  use bellpepper::gadgets::Assignment;
  use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
  };

  use super::*;

  use std::marker::PhantomData;

  use crate::{
    constants::{NUM_CHALLENGE_BITS, NUM_FE_FOR_RO},
    gadgets::{
      nonnative::{bignat::BigNat, util::f_to_nat},
      utils::{alloc_bignat_constant, alloc_scalar_as_base, le_bits_to_num, scalar_as_base},
    },
    traits::{Group, ROConstantsCircuit},
    RelaxedR1CSInstance,
  };

  use ff::Field;

  #[derive(Clone)]
  pub struct AllocatedPoint<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    x: BigNat<E1::Base>,
    y: BigNat<E1::Base>,
    is_infinity: AllocatedNum<E1::Base>,
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
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      let x = BigNat::alloc_from_nat(
        cs.namespace(|| "x"),
        || {
          Ok(f_to_nat(
            &coords.ok_or(SynthesisError::AssignmentMissing)?.0,
          ))
        },
        limb_width,
        n_limbs,
      )?;

      let y = BigNat::alloc_from_nat(
        cs.namespace(|| "y"),
        || {
          Ok(f_to_nat(
            &coords.ok_or(SynthesisError::AssignmentMissing)?.1,
          ))
        },
        limb_width,
        n_limbs,
      )?;

      let is_infinity = AllocatedNum::alloc(cs.namespace(|| "is_infinity"), || {
        Ok(if coords.map_or(true, |c| c.2) {
          E1::Base::ONE
        } else {
          E1::Base::ZERO
        })
      })?;
      cs.enforce(
        || "is_infinity is bit",
        |lc| lc + is_infinity.get_variable(),
        |lc| lc + CS::one() - is_infinity.get_variable(),
        |lc| lc,
      );
      Ok(Self { x, y, is_infinity })
    }

    pub fn absorb_in_ro<CS>(&self, mut cs: CS, ro: &mut E1::ROCircuit) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      let x_bn = self
        .x
        .as_limbs()
        .iter()
        .enumerate()
        .map(|(i, limb)| {
          limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of X_r[0] to num")))
        })
        .collect::<Result<Vec<AllocatedNum<E1::Base>>, _>>()?;

      for limb in x_bn {
        ro.absorb(&limb)
      }

      let y_bn = self
        .y
        .as_limbs()
        .iter()
        .enumerate()
        .map(|(i, limb)| {
          limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of X_r[0] to num")))
        })
        .collect::<Result<Vec<AllocatedNum<E1::Base>>, _>>()?;

      for limb in y_bn {
        ro.absorb(&limb)
      }

      ro.absorb(&self.is_infinity);

      Ok(())
    }

    pub fn check_on_curve<CS>(
      &self,
      mut cs: CS,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      let m_bn = alloc_bignat_constant(
        cs.namespace(|| "alloc m"),
        &E1::GE::group_params().3,
        limb_width,
        n_limbs,
      )?;

      let A_bn = alloc_bignat_constant(
        cs.namespace(|| "alloc A"),
        &f_to_nat(&E1::GE::group_params().0),
        limb_width,
        n_limbs,
      )?;

      let B_bn = alloc_bignat_constant(
        cs.namespace(|| "alloc B"),
        &f_to_nat(&E1::GE::group_params().1),
        limb_width,
        n_limbs,
      )?;

      let (_, A_x) = A_bn.mult_mod(cs.namespace(|| "A_x"), &self.x, &m_bn)?;

      let (_, x_sq) = self.x.mult_mod(cs.namespace(|| "x_sq"), &self.x, &m_bn)?;
      let (_, x_cu) = self.x.mult_mod(cs.namespace(|| "x_cu"), &x_sq, &m_bn)?;

      let rhs = x_cu.add(&A_x)?.add(&B_bn)?;

      let (_, y_sq) = self.y.mult_mod(cs.namespace(|| "y_sq"), &self.y, &m_bn)?;

      let always_equal = AllocatedBit::alloc(
        cs.namespace(|| "always_equal = 1 - is_infinity"),
        self
          .is_infinity
          .get_value()
          .map(|is_infinity| is_infinity == E1::Base::ONE),
      )?;

      cs.enforce(
        || "always_equal = 1 - is_infinity",
        |lc| lc,
        |lc| lc,
        |lc| lc + always_equal.get_variable() - CS::one() + self.is_infinity.get_variable(),
      );

      y_sq.equal_when_carried_regroup(cs.namespace(|| "y_sq = rhs"), &rhs, &always_equal)?;

      Ok(())
    }
  }

  pub struct AllocatedRelaxedR1CSInstance<E1, E2>
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    comm_W: AllocatedPoint<E1, E2>,
    comm_E: AllocatedPoint<E1, E2>,
    u: AllocatedNum<E1::Base>,
    x0: AllocatedNum<E1::Base>,
    x1: AllocatedNum<E1::Base>,
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
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E1 as Engine>::Base>,
    {
      let comm_W = AllocatedPoint::alloc(
        cs.namespace(|| "allocate comm_W"),
        inst.map(|x| x.comm_W.to_coordinates()),
        limb_width,
        n_limbs,
      )?;

      let comm_E = AllocatedPoint::alloc(
        cs.namespace(|| "allocate comm_E"),
        inst.map(|x| x.comm_E.to_coordinates()),
        limb_width,
        n_limbs,
      )?;

      let u = AllocatedNum::alloc(cs.namespace(|| "allocate u"), || {
        inst.map_or(Ok(E1::Base::ZERO), |inst| Ok(inst.u))
      })?;

      let x0 = AllocatedNum::alloc(cs.namespace(|| "allocate x0"), || {
        inst.map_or(Ok(E1::Base::ZERO), |inst| Ok(inst.X[0]))
      })?;

      let x1 = AllocatedNum::alloc(cs.namespace(|| "allocate x1"), || {
        inst.map_or(Ok(E1::Base::ZERO), |inst| Ok(inst.X[1]))
      })?;

      Ok(Self {
        comm_W,
        comm_E,
        u,
        x0,
        x1,
        _p: PhantomData,
      })
    }

    pub fn fold_with_r1cs<CS: ConstraintSystem<<E1 as Engine>::Base>>(
      &self,
      mut cs: CS,
      pp_digest: &AllocatedNum<E1::Base>,
      W_new: AllocatedPoint<E1, E2>,
      E_new: AllocatedPoint<E1, E2>,
      u_W: &AllocatedPoint<E1, E2>,
      u_x0: &AllocatedNum<E1::Base>,
      u_x1: &AllocatedNum<E1::Base>,
      comm_T: &AllocatedPoint<E1, E2>,
      ro_consts: ROConstantsCircuit<E1>,
    ) -> Result<Self, SynthesisError> {
      let mut ro = E1::ROCircuit::new(ro_consts, NUM_FE_FOR_RO);

      ro.absorb(pp_digest);

      // Absorb u
      // Absorb the witness
      u_W.absorb_in_ro(cs.namespace(|| "absorb u_W"), &mut ro)?;
      // Absorb public IO
      ro.absorb(u_x0);
      ro.absorb(u_x1);

      // Absorb comm_T
      comm_T.absorb_in_ro(cs.namespace(|| "absorb comm_T"), &mut ro)?;

      let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
      let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;

      let u_fold = AllocatedNum::alloc(cs.namespace(|| "u"), || {
        Ok(*self.u.get_value().get()? + r.get_value().get()?)
      })?;
      cs.enforce(
        || "u_fold = u + r",
        |lc| lc,
        |lc| lc,
        |lc| lc + u_fold.get_variable() - self.u.get_variable() - r.get_variable(),
      );

      let x0_fold = AllocatedNum::alloc(cs.namespace(|| "x0"), || {
        Ok(*self.x0.get_value().get()? + *r.get_value().get()? * *u_x0.get_value().get()?)
      })?;
      cs.enforce(
        || "x0_fold = x0 + r * u_x0",
        |lc| lc + r.get_variable(),
        |lc| lc + u_x0.get_variable(),
        |lc| lc + x0_fold.get_variable() - self.x0.get_variable(),
      );

      let x1_fold = AllocatedNum::alloc(cs.namespace(|| "x1"), || {
        Ok(*self.x1.get_value().get()? + *r.get_value().get()? * *u_x1.get_value().get()?)
      })?;
      cs.enforce(
        || "x1_fold = x1 + r * u_x1",
        |lc| lc + r.get_variable(),
        |lc| lc + u_x1.get_variable(),
        |lc| lc + x1_fold.get_variable() - self.x1.get_variable(),
      );

      Ok(Self {
        comm_W: W_new,
        comm_E: E_new,
        u: u_fold,
        x0: x0_fold,
        x1: x1_fold,
        _p: PhantomData,
      })
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
    pub u_x0: AllocatedNum<E1::Base>,
    pub u_x1: AllocatedNum<E1::Base>,
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
