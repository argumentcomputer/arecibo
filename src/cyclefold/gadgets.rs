use super::nova_circuit::FoldingData;

use crate::{
  gadgets::{
    ecc::AllocatedPoint,
    r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
  },
  traits::{commitment::CommitmentTrait, Engine, ROCircuitTrait},
};

use bellpepper_core::{ConstraintSystem, SynthesisError};
pub struct AllocatedFoldingData<E: Engine, const N: usize> {
  pub U: AllocatedRelaxedR1CSInstance<E, N>,
  pub u: AllocatedR1CSInstance<E, N>,
  pub T: AllocatedPoint<E::GE>,
}

impl<E: Engine, const N: usize> AllocatedFoldingData<E, N> {
  pub fn alloc<CS: ConstraintSystem<<E as Engine>::Base>>(
    mut cs: CS,
    inst: Option<&FoldingData<E>>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    let U = AllocatedRelaxedR1CSInstance::alloc(
      cs.namespace(|| "u"),
      inst.map(|x| &x.U),
      limb_width,
      n_limbs,
    )?;

    let u = AllocatedR1CSInstance::alloc(cs.namespace(|| "U"), inst.map(|x| &x.u))?;

    let T = AllocatedPoint::alloc(cs.namespace(|| "T"), inst.map(|x| x.T.to_coordinates()))?;
    T.check_on_curve(cs.namespace(|| "T on curve"))?;

    Ok(Self { U, u, T })
  }

  // TODO: Delete if not needed, or uncomment if this saves time
  // pub fn absorb_in_ro<CS: ConstraintSystem<<E as Engine>::Base>>(
  //   &self,
  //   mut cs: CS,
  //   ro: &mut E::ROCircuit,
  // ) -> Result<(), SynthesisError> {
  //   self.U.absorb_in_ro(cs.namespace(|| "absorb U"), ro)?;
  //   self.u.absorb_in_ro(ro);
  //   ro.absorb(&self.T.x);
  //   ro.absorb(&self.T.y);
  //   ro.absorb(&self.T.is_infinity);
  //   Ok(())
  // }
}

pub mod emulated {
  use bellpepper::gadgets::Assignment;
  use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
  };

  use super::*;

  use crate::{
    constants::{NUM_CHALLENGE_BITS, NUM_FE_IN_EMULATED_POINT},
    gadgets::{
      nonnative::{bignat::BigNat, util::f_to_nat},
      utils::{
        alloc_zero, conditionally_select, conditionally_select_allocated_bit,
        conditionally_select_bignat, le_bits_to_num,
      },
    },
    traits::{Group, ROConstantsCircuit},
    RelaxedR1CSInstance,
  };

  use ff::Field;

  pub struct EmulatedCurveParams<G>
  where
    G: Group,
  {
    pub A: BigNat<G::Base>,
    pub B: BigNat<G::Base>,
    pub m: BigNat<G::Base>,
  }

  impl<G: Group> EmulatedCurveParams<G> {
    #[allow(unused)]
    pub fn alloc<CS>(
      mut cs: CS,
      params: Option<&(G::Scalar, G::Scalar, G::Scalar)>,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<G::Base>,
    {
      let A = BigNat::alloc_from_nat(
        cs.namespace(|| "allocate A"),
        || {
          Ok(f_to_nat(
            &params.ok_or(SynthesisError::AssignmentMissing)?.0,
          ))
        },
        limb_width,
        n_limbs,
      )?;

      let B = BigNat::alloc_from_nat(
        cs.namespace(|| "allocate B"),
        || {
          Ok(f_to_nat(
            &params.ok_or(SynthesisError::AssignmentMissing)?.1,
          ))
        },
        limb_width,
        n_limbs,
      )?;

      let m = BigNat::alloc_from_nat(
        cs.namespace(|| "allocate m"),
        || {
          Ok(f_to_nat(
            &params.ok_or(SynthesisError::AssignmentMissing)?.2,
          ))
        },
        limb_width,
        n_limbs,
      )?;

      Ok(Self { A, B, m })
    }
  }

  #[derive(Clone)]
  pub struct AllocatedEmulPoint<G>
  where
    G: Group,
  {
    pub x: BigNat<G::Base>,
    pub y: BigNat<G::Base>,
    pub is_infinity: AllocatedBit,
  }

  impl<G> AllocatedEmulPoint<G>
  where
    G: Group,
  {
    pub fn alloc<CS>(
      mut cs: CS,
      coords: Option<(G::Scalar, G::Scalar, bool)>,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<G as Group>::Base>,
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

      let is_infinity = AllocatedBit::alloc(
        cs.namespace(|| "alloc is_infinity"),
        coords.map(|(_, _, is_infinity)| is_infinity),
      )?;

      Ok(Self { x, y, is_infinity })
    }

    pub fn absorb_in_ro<CS>(
      &self,
      mut cs: CS,
      ro: &mut impl ROCircuitTrait<G::Base>,
    ) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<G::Base>,
    {
      let x_bn = self
        .x
        .as_limbs()
        .iter()
        .enumerate()
        .map(|(i, limb)| {
          limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of x to num")))
        })
        .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

      for limb in x_bn {
        ro.absorb(&limb)
      }

      let y_bn = self
        .y
        .as_limbs()
        .iter()
        .enumerate()
        .map(|(i, limb)| {
          limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of y to num")))
        })
        .collect::<Result<Vec<AllocatedNum<G::Base>>, _>>()?;

      for limb in y_bn {
        ro.absorb(&limb)
      }

      let is_infinity_num: AllocatedNum<G::Base> =
        AllocatedNum::alloc(cs.namespace(|| "is_infinity"), || {
          self
            .is_infinity
            .get_value()
            .map_or(Err(SynthesisError::AssignmentMissing), |bit| {
              if bit {
                Ok(G::Base::ONE)
              } else {
                Ok(G::Base::ZERO)
              }
            })
        })?;

      cs.enforce(
        || "constrain num equals bit",
        |lc| lc,
        |lc| lc,
        |lc| lc + is_infinity_num.get_variable() - self.is_infinity.get_variable(),
      );

      ro.absorb(&is_infinity_num);

      Ok(())
    }

    #[allow(unused)]
    pub fn check_on_curve<CS>(
      &self,
      mut cs: CS,
      curve_params: &EmulatedCurveParams<G>,
      _limb_width: usize,
      _n_limbs: usize,
    ) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<G::Base>,
    {
      let (m_bn, A_bn, B_bn) = (
        curve_params.m.clone(),
        curve_params.A.clone(),
        curve_params.B.clone(),
      );

      let (_, A_x) = A_bn.mult_mod(cs.namespace(|| "A_x"), &self.x, &m_bn)?;

      let (_, x_sq) = self.x.mult_mod(cs.namespace(|| "x_sq"), &self.x, &m_bn)?;
      let (_, x_cu) = self.x.mult_mod(cs.namespace(|| "x_cu"), &x_sq, &m_bn)?;

      let rhs = x_cu.add(&A_x)?.add(&B_bn)?;

      let (_, y_sq) = self.y.mult_mod(cs.namespace(|| "y_sq"), &self.y, &m_bn)?;

      let always_equal = self.is_infinity.clone();

      y_sq.equal_when_carried_regroup(cs.namespace(|| "y_sq = rhs"), &rhs, &always_equal)?;

      Ok(())
    }

    fn conditionally_select<CS: ConstraintSystem<G::Base>>(
      &self,
      mut cs: CS,
      other: &Self,
      condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
      let x = conditionally_select_bignat(
        cs.namespace(|| "x = cond ? self.x : other.x"),
        &self.x,
        &other.x,
        condition,
      )?;

      let y = conditionally_select_bignat(
        cs.namespace(|| "y = cond ? self.y : other.y"),
        &self.y,
        &other.y,
        condition,
      )?;

      let is_infinity = conditionally_select_allocated_bit(
        cs.namespace(|| "is_infinity = cond ? self.is_infinity : other.is_infinity"),
        &self.is_infinity,
        &other.is_infinity,
        condition,
      )?;

      Ok(Self { x, y, is_infinity })
    }

    pub fn default<CS: ConstraintSystem<G::Base>>(
      mut cs: CS,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
      let x = BigNat::alloc_from_nat(
        cs.namespace(|| "allocate x_default = 0"),
        || Ok(f_to_nat(&G::Scalar::ZERO)),
        limb_width,
        n_limbs,
      )?;

      let y = BigNat::alloc_from_nat(
        cs.namespace(|| "allocate y_default = 0"),
        || Ok(f_to_nat(&G::Scalar::ZERO)),
        limb_width,
        n_limbs,
      )?;

      let is_infinity = AllocatedBit::alloc(cs.namespace(|| "allocate is_infinity"), Some(true))?;

      Ok(Self { x, y, is_infinity })
    }
  }

  pub struct AllocatedEmulRelaxedR1CSInstance<E: Engine> {
    comm_W: AllocatedEmulPoint<E::GE>,
    comm_E: AllocatedEmulPoint<E::GE>,
    u: AllocatedNum<E::Base>,
    x0: AllocatedNum<E::Base>,
    x1: AllocatedNum<E::Base>,
  }

  impl<E> AllocatedEmulRelaxedR1CSInstance<E>
  where
    E: Engine,
  {
    pub fn alloc<CS, E2: Engine<Base = E::Scalar, Scalar = E::Base>>(
      mut cs: CS,
      inst: Option<&RelaxedR1CSInstance<E2>>,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E as Engine>::Base>,
    {
      let comm_W = AllocatedEmulPoint::alloc(
        cs.namespace(|| "allocate comm_W"),
        inst.map(|x| x.comm_W.to_coordinates()),
        limb_width,
        n_limbs,
      )?;

      let comm_E = AllocatedEmulPoint::alloc(
        cs.namespace(|| "allocate comm_E"),
        inst.map(|x| x.comm_E.to_coordinates()),
        limb_width,
        n_limbs,
      )?;

      let u = AllocatedNum::alloc(cs.namespace(|| "allocate u"), || {
        inst.map_or(Ok(E::Base::ZERO), |inst| Ok(inst.u))
      })?;

      let x0 = AllocatedNum::alloc(cs.namespace(|| "allocate x0"), || {
        inst.map_or(Ok(E::Base::ZERO), |inst| Ok(inst.X[0]))
      })?;

      let x1 = AllocatedNum::alloc(cs.namespace(|| "allocate x1"), || {
        inst.map_or(Ok(E::Base::ZERO), |inst| Ok(inst.X[1]))
      })?;

      Ok(Self {
        comm_W,
        comm_E,
        u,
        x0,
        x1,
      })
    }

    pub fn fold_with_r1cs<CS: ConstraintSystem<<E as Engine>::Base>>(
      &self,
      mut cs: CS,
      pp_digest: &AllocatedNum<E::Base>,
      W_new: AllocatedEmulPoint<E::GE>,
      E_new: AllocatedEmulPoint<E::GE>,
      u_W: &AllocatedEmulPoint<E::GE>,
      u_x0: &AllocatedNum<E::Base>,
      u_x1: &AllocatedNum<E::Base>,
      comm_T: &AllocatedEmulPoint<E::GE>,
      ro_consts: ROConstantsCircuit<E>,
    ) -> Result<Self, SynthesisError> {
      let mut ro = E::ROCircuit::new(
        ro_consts,
        1 + NUM_FE_IN_EMULATED_POINT + 2 + NUM_FE_IN_EMULATED_POINT, // pp_digest + u.W + u.x + comm_T
      );
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
      })
    }

    pub fn absorb_in_ro<CS>(
      &self,
      mut cs: CS,
      ro: &mut impl ROCircuitTrait<E::Base>,
    ) -> Result<(), SynthesisError>
    where
      CS: ConstraintSystem<<E as Engine>::Base>,
    {
      self
        .comm_E
        .absorb_in_ro(cs.namespace(|| "absorb comm_E"), ro)?;
      self
        .comm_W
        .absorb_in_ro(cs.namespace(|| "absorb comm_W"), ro)?;

      ro.absorb(&self.u);
      ro.absorb(&self.x0);
      ro.absorb(&self.x1);

      Ok(())
    }

    pub fn conditionally_select<CS: ConstraintSystem<<E as Engine>::Base>>(
      &self,
      mut cs: CS,
      other: &Self,
      condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
      let comm_W = self.comm_W.conditionally_select(
        cs.namespace(|| "comm_W = cond ? self.comm_W : other.comm_W"),
        &other.comm_W,
        condition,
      )?;

      let comm_E = self.comm_E.conditionally_select(
        cs.namespace(|| "comm_E = cond? self.comm_E : other.comm_E"),
        &other.comm_E,
        condition,
      )?;

      let u = conditionally_select(
        cs.namespace(|| "u = cond ? self.u : other.u"),
        &self.u,
        &other.u,
        condition,
      )?;

      let x0 = conditionally_select(
        cs.namespace(|| "x0 = cond ? self.x0 : other.x0"),
        &self.x0,
        &other.x0,
        condition,
      )?;

      let x1 = conditionally_select(
        cs.namespace(|| "x1 = cond ? self.x1 : other.x1"),
        &self.x1,
        &other.x1,
        condition,
      )?;

      Ok(Self {
        comm_W,
        comm_E,
        u,
        x0,
        x1,
      })
    }

    pub fn default<CS: ConstraintSystem<<E as Engine>::Base>>(
      mut cs: CS,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError> {
      let comm_W =
        AllocatedEmulPoint::default(cs.namespace(|| "default comm_W"), limb_width, n_limbs)?;
      let comm_E = comm_W.clone();

      let u = alloc_zero(cs.namespace(|| "u = 0"));

      let x0 = u.clone();
      let x1 = u.clone();

      Ok(Self {
        comm_W,
        comm_E,
        u,
        x0,
        x1,
      })
    }
  }
  pub struct AllocatedFoldingData<E: Engine> {
    pub U: AllocatedEmulRelaxedR1CSInstance<E>,
    pub u_W: AllocatedEmulPoint<E::GE>,
    pub u_x0: AllocatedNum<E::Base>,
    pub u_x1: AllocatedNum<E::Base>,
    pub T: AllocatedEmulPoint<E::GE>,
  }

  impl<E: Engine> AllocatedFoldingData<E> {
    pub fn alloc<CS, E2: Engine<Base = E::Scalar, Scalar = E::Base>>(
      mut cs: CS,
      inst: Option<&FoldingData<E2>>,
      limb_width: usize,
      n_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E as Engine>::Base>,
    {
      let U = AllocatedEmulRelaxedR1CSInstance::alloc(
        cs.namespace(|| "allocate U"),
        inst.map(|x| &x.U),
        limb_width,
        n_limbs,
      )?;

      let u_W = AllocatedEmulPoint::alloc(
        cs.namespace(|| "allocate u_W"),
        inst.map(|x| x.u.comm_W.to_coordinates()),
        limb_width,
        n_limbs,
      )?;

      let u_x0 = AllocatedNum::alloc(cs.namespace(|| "allocate u_x0"), || {
        inst.map_or(Ok(E::Base::ZERO), |inst| Ok(inst.u.X[0]))
      })?;

      let u_x1 = AllocatedNum::alloc(cs.namespace(|| "allocate u_x1"), || {
        inst.map_or(Ok(E::Base::ZERO), |inst| Ok(inst.u.X[1]))
      })?;

      let T = AllocatedEmulPoint::alloc(
        cs.namespace(|| "allocate T"),
        inst.map(|x| x.T.to_coordinates()),
        limb_width,
        n_limbs,
      )?;

      Ok(Self {
        U,
        u_W,
        u_x0,
        u_x1,
        T,
      })
    }

    // TODO: Delete if not needed
    // pub fn absorb_in_ro<CS>(&self, mut cs: CS, ro: &mut E1::ROCircuit) -> Result<(), SynthesisError>
    // where
    //   CS: ConstraintSystem<<E1 as Engine>::Base>,
    // {
    //   self.U.absorb_in_ro(cs.namespace(|| "absorb U"), ro)?;
    //   self.u_W.absorb_in_ro(cs.namespace(|| "absorb u_W"), ro)?;
    //   ro.absorb(&self.u_x0);
    //   ro.absorb(&self.u_x1);
    //   self.T.absorb_in_ro(cs.namespace(|| "absorb T"), ro)?;
    //   Ok(())
    // }
  }
}
