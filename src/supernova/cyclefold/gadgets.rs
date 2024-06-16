pub mod emulated {
  use bellpepper_core::boolean::Boolean;
  use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};

  use crate::supernova::utils::get_from_vec_alloc_emul_relaxed_r1cs;
  use crate::traits::commitment::CommitmentTrait;
  use crate::{
    cyclefold::gadgets::emulated::{AllocatedEmulPoint, AllocatedEmulRelaxedR1CSInstance},
    supernova::cyclefold::util::SuperNovaFoldingData,
    traits::Engine,
  };
  use ff::Field;

  /// The in-circuit representation of the primary folding data.
  pub struct SuperNovaAllocatedFoldingData<E: Engine> {
    pub U: Vec<AllocatedEmulRelaxedR1CSInstance<E>>,
    pub u_W: AllocatedEmulPoint<E::GE>,
    pub u_x0: AllocatedNum<E::Base>,
    pub u_x1: AllocatedNum<E::Base>,
    pub T: AllocatedEmulPoint<E::GE>,
  }

  impl<E: Engine> SuperNovaAllocatedFoldingData<E> {
    pub fn alloc<CS, E2: Engine<Base = E::Scalar, Scalar = E::Base>>(
      mut cs: CS,
      inst: Option<&SuperNovaFoldingData<E2>>,
      limb_width: usize,
      n_limbs: usize,
      num_augmented_circuits: usize,
    ) -> Result<Self, SynthesisError>
    where
      CS: ConstraintSystem<<E as Engine>::Base>,
    {
      let U = (0..num_augmented_circuits)
        .map(|i| {
          AllocatedEmulRelaxedR1CSInstance::alloc(
            cs.namespace(|| format!("Allocate U {:?}", i)),
            inst.and_then(|inst| inst.U[i].as_ref()),
            limb_width,
            n_limbs,
          )
        })
        .collect::<Result<Vec<AllocatedEmulRelaxedR1CSInstance<E>>, _>>()?;

      let u_W = AllocatedEmulPoint::alloc(
        cs.namespace(|| "allocate u_W"),
        inst.map(|inst| &inst.u).map(|u| u.comm_W.to_coordinates()),
        limb_width,
        n_limbs,
      )?;

      let u_x0 = AllocatedNum::alloc(cs.namespace(|| "allocate u_x0"), || {
        inst
          .map(|inst| &inst.u)
          .map_or(Ok(E::Base::ZERO), |u| Ok(u.X[0]))
      })?;

      let u_x1 = AllocatedNum::alloc(cs.namespace(|| "allocate u_x1"), || {
        inst
          .map(|inst| &inst.u)
          .map_or(Ok(E::Base::ZERO), |u| Ok(u.X[1]))
      })?;

      let T = AllocatedEmulPoint::alloc(
        cs.namespace(|| "allocate T"),
        inst.map(|inst| inst.T).as_ref().map(|t| t.to_coordinates()),
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

  impl<E: Engine> SuperNovaAllocatedFoldingData<E> {
    pub fn U_to_fold<CS>(
      &self,
      mut cs: CS,
      last_augmented_circuit_selector: &[Boolean],
    ) -> Result<AllocatedEmulRelaxedR1CSInstance<E>, SynthesisError>
    where
      CS: ConstraintSystem<<E as Engine>::Base>,
    {
      get_from_vec_alloc_emul_relaxed_r1cs(
        cs.namespace(|| "U to fold"),
        &self.U,
        last_augmented_circuit_selector,
      )
    }
  }
}
