//! This module defines many of the gadgets needed in the primary folding circuit

use super::util::FoldingData;

use crate::{
  constants::{BN_N_LIMBS, NIO_CYCLE_FOLD, NUM_CHALLENGE_BITS},
  gadgets::{
    alloc_bignat_constant, f_to_nat, le_bits_to_num, AllocatedPoint, AllocatedRelaxedR1CSInstance,
    BigNat, Num,
  },
  r1cs::R1CSInstance,
  traits::{commitment::CommitmentTrait, Engine, Group, ROCircuitTrait, ROConstantsCircuit},
};

use bellpepper::gadgets::Assignment;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::Field;
use itertools::Itertools;

// An allocated version of the R1CS instance obtained from a single cyclefold invocation
pub struct AllocatedCycleFoldInstance<E: Engine> {
  W: AllocatedPoint<E::GE>,
  X: [BigNat<E::Base>; NIO_CYCLE_FOLD],
}

impl<E: Engine> AllocatedCycleFoldInstance<E> {
  pub fn alloc<CS: ConstraintSystem<E::Base>>(
    mut cs: CS,
    inst: Option<&R1CSInstance<E>>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    let W = AllocatedPoint::alloc(
      cs.namespace(|| "allocate W"),
      inst.map(|u| u.comm_W.to_coordinates()),
    )?;
    W.check_on_curve(cs.namespace(|| "check W on curve"))?;

    if let Some(inst) = inst {
      if inst.X.len() != NIO_CYCLE_FOLD {
        return Err(SynthesisError::IncompatibleLengthVector(String::from(
          "R1CS instance has wrong arity",
        )));
      }
    }

    let X: [BigNat<E::Base>; NIO_CYCLE_FOLD] = (0..NIO_CYCLE_FOLD)
      .map(|idx| {
        BigNat::alloc_from_nat(
          cs.namespace(|| format!("allocating IO {idx}")),
          || Ok(f_to_nat(inst.map_or(&E::Scalar::ZERO, |inst| &inst.X[idx]))),
          limb_width,
          n_limbs,
        )
      })
      .collect::<Result<Vec<_>, _>>()?
      .try_into()
      .map_err(|err: Vec<_>| {
        SynthesisError::IncompatibleLengthVector(format!("{} != {NIO_CYCLE_FOLD}", err.len()))
      })?;

    Ok(Self { W, X })
  }

  pub fn absorb_in_ro<CS>(
    &self,
    mut cs: CS,
    ro: &mut impl ROCircuitTrait<E::Base>,
  ) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Base>,
  {
    ro.absorb(&self.W.x);
    ro.absorb(&self.W.y);
    ro.absorb(&self.W.is_infinity);
    self
      .X
      .iter()
      .enumerate()
      .try_for_each(|(io_idx, x)| -> Result<(), SynthesisError> {
        x.as_limbs().iter().enumerate().try_for_each(
          |(limb_idx, limb)| -> Result<(), SynthesisError> {
            ro.absorb(&limb.as_allocated_num(
              cs.namespace(|| format!("convert limb {limb_idx} of X[{io_idx}] to num")),
            )?);
            Ok(())
          },
        )
      })?;

    Ok(())
  }
}

/// An circuit allocated version of the `FoldingData` coming from a CycleFold invocation.
pub struct AllocatedCycleFoldData<E: Engine> {
  pub U: AllocatedRelaxedR1CSInstance<E, NIO_CYCLE_FOLD>,
  pub u: AllocatedCycleFoldInstance<E>,
  pub T: AllocatedPoint<E::GE>,
}

impl<E: Engine> AllocatedCycleFoldData<E> {
  pub fn alloc<CS: ConstraintSystem<E::Base>>(
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

    let u = AllocatedCycleFoldInstance::alloc(
      cs.namespace(|| "u"),
      inst.map(|x| &x.u),
      limb_width,
      n_limbs,
    )?;

    let T = AllocatedPoint::alloc(cs.namespace(|| "T"), inst.map(|x| x.T.to_coordinates()))?;
    T.check_on_curve(cs.namespace(|| "T on curve"))?;

    Ok(Self { U, u, T })
  }

  /// The NIFS verifier which folds the CycleFold instance into a running relaxed R1CS instance.
  pub fn apply_fold<CS>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<E::Base>,
    ro_consts: ROConstantsCircuit<E>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<AllocatedRelaxedR1CSInstance<E, NIO_CYCLE_FOLD>, SynthesisError>
  where
    CS: ConstraintSystem<E::Base>,
  {
    // Compute r:
    let mut ro = E::ROCircuit::new(
      ro_consts,
      1 + (3 + 3 + 1 + NIO_CYCLE_FOLD * BN_N_LIMBS) + (3 + NIO_CYCLE_FOLD * BN_N_LIMBS) + 3, // digest + (U) + (u) + T
    );
    ro.absorb(params);

    self.U.absorb_in_ro(
      cs.namespace(|| "absorb cyclefold running instance"),
      &mut ro,
    )?;
    // running instance `U` does not need to absorbed since u.X[0] = Hash(params, U, i, z0, zi)
    self
      .u
      .absorb_in_ro(cs.namespace(|| "absorb cyclefold instance"), &mut ro)?;

    ro.absorb(&self.T.x);
    ro.absorb(&self.T.y);
    ro.absorb(&self.T.is_infinity);
    let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
    let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;

    // W_fold = self.W + r * u.W
    let rW = self.u.W.scalar_mul(cs.namespace(|| "r * u.W"), &r_bits)?;
    let W_fold = self.U.W.add(cs.namespace(|| "self.W + r * u.W"), &rW)?;

    // E_fold = self.E + r * T
    let rT = self.T.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
    let E_fold = self.U.E.add(cs.namespace(|| "self.E + r * T"), &rT)?;

    // u_fold = u_r + r
    let u_fold = AllocatedNum::alloc(cs.namespace(|| "u_fold"), || {
      Ok(*self.U.u.get_value().get()? + r.get_value().get()?)
    })?;
    cs.enforce(
      || "Check u_fold",
      |lc| lc,
      |lc| lc,
      |lc| lc + u_fold.get_variable() - self.U.u.get_variable() - r.get_variable(),
    );

    // Fold the IO:
    // Analyze r into limbs
    let r_bn = BigNat::from_num(
      cs.namespace(|| "allocate r_bn"),
      &Num::from(r),
      limb_width,
      n_limbs,
    )?;

    // Allocate the order of the non-native field as a constant
    let m_bn = alloc_bignat_constant(
      cs.namespace(|| "alloc m"),
      &E::GE::group_params().2,
      limb_width,
      n_limbs,
    )?;

    let mut X_fold = vec![];

    // Calculate the
    for (idx, (X, x)) in self.U.X.iter().zip_eq(self.u.X.iter()).enumerate() {
      let (_, r) = x.mult_mod(cs.namespace(|| format!("r*u.X[{idx}]")), &r_bn, &m_bn)?;
      let r_new = X.add(&r)?;
      let X_i_fold = r_new.red_mod(cs.namespace(|| format!("reduce folded X[{idx}]")), &m_bn)?;
      X_fold.push(X_i_fold);
    }

    let X_fold = X_fold.try_into().map_err(|err: Vec<_>| {
      SynthesisError::IncompatibleLengthVector(format!("{} != {NIO_CYCLE_FOLD}", err.len()))
    })?;

    Ok(AllocatedRelaxedR1CSInstance {
      W: W_fold,
      E: E_fold,
      u: u_fold,
      X: X_fold,
    })
  }
}

pub mod emulated {
  use bellpepper::gadgets::{boolean_utils::conditionally_select, Assignment};
  use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
  };

  use crate::{
    constants::{NUM_CHALLENGE_BITS, NUM_FE_IN_EMULATED_POINT},
    gadgets::{
      alloc_bignat_constant, alloc_zero, conditionally_select_allocated_bit,
      conditionally_select_bignat, f_to_nat, le_bits_to_num, BigNat,
    },
    traits::{commitment::CommitmentTrait, Engine, Group, ROCircuitTrait, ROConstantsCircuit},
    RelaxedR1CSInstance,
  };

  use super::FoldingData;

  use ff::Field;

  /// An allocated version of a curve point from the non-native curve
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
            &coords.map_or(<G::Scalar as Field>::ZERO, |val| val.0),
          ))
        },
        limb_width,
        n_limbs,
      )?;

      let y = BigNat::alloc_from_nat(
        cs.namespace(|| "y"),
        || {
          Ok(f_to_nat(
            &coords.map_or(<G::Scalar as Field>::ZERO, |val| val.1),
          ))
        },
        limb_width,
        n_limbs,
      )?;

      let is_infinity = AllocatedBit::alloc(
        cs.namespace(|| "alloc is_infinity"),
        coords.map_or(Some(true), |(_, _, is_infinity)| Some(is_infinity)),
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
      let x = alloc_bignat_constant(
        cs.namespace(|| "allocate x_default = 0"),
        &f_to_nat(&G::Base::ZERO),
        limb_width,
        n_limbs,
      )?;
      let y = alloc_bignat_constant(
        cs.namespace(|| "allocate y_default = 0"),
        &f_to_nat(&G::Base::ZERO),
        limb_width,
        n_limbs,
      )?;

      let is_infinity = AllocatedBit::alloc(cs.namespace(|| "allocate is_infinity"), Some(true))?;
      cs.enforce(
        || "is_infinity = 1",
        |lc| lc,
        |lc| lc,
        |lc| lc + CS::one() - is_infinity.get_variable(),
      );

      Ok(Self { x, y, is_infinity })
    }
  }

  /// A non-native circuit version of a `RelaxedR1CSInstance`. This is used for the in-circuit
  /// representation of the primary running instance
  pub struct AllocatedEmulRelaxedR1CSInstance<E: Engine> {
    pub comm_W: AllocatedEmulPoint<E::GE>,
    pub comm_E: AllocatedEmulPoint<E::GE>,
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

    /// Performs a folding of a primary R1CS instance (`u_W`, `u_x0`, `u_x1`) into a running
    /// `AllocatedEmulRelaxedR1CSInstance`
    /// As the curve operations are performed in the CycleFold circuit and provided to the primary
    /// circuit as non-deterministic advice, this folding simply sets those values as the new witness
    /// and error vector commitments.
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

      let u_fold = self.u.add(cs.namespace(|| "u_fold = u + r"), &r)?;
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
        .comm_W
        .absorb_in_ro(cs.namespace(|| "absorb comm_W"), ro)?;
      self
        .comm_E
        .absorb_in_ro(cs.namespace(|| "absorb comm_E"), ro)?;

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

  /// The in-circuit representation of the primary folding data.
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
  }
}
