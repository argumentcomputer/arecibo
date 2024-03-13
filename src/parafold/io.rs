use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::AllocatedNum;
use ff::Field;
use itertools::{enumerate, zip_eq};

use crate::parafold::hash::{AllocatedHasher, AllocatedHashWriter, Hasher, HashWriter};
use crate::parafold::NIVCIO;
use crate::supernova::EnforcingStepCircuit;
use crate::traits::CurveCycleEquipped;

/// The input and output of a NIVC computation over one or more steps.
#[derive(Debug, Clone)]
pub struct AllocatedNIVCIO<E: CurveCycleEquipped> {
  pc_in: AllocatedNum<E::Scalar>,
  z_in: Vec<AllocatedNum<E::Scalar>>,
  pc_out: AllocatedNum<E::Scalar>,
  z_out: Vec<AllocatedNum<E::Scalar>>,
}

impl<E: CurveCycleEquipped> AllocatedNIVCIO<E> {
  pub fn alloc<CS>(mut cs: CS, state: NIVCIO<E>) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let pc_in = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_in"), || state.pc_in);
    let z_in = enumerate(state.z_in)
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || z)
      })
      .collect();
    let pc_out = AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc_out"), || state.pc_out);
    let z_out = enumerate(state.z_out)
      .map(|(i, z)| {
        AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_out[{i}]")), || z)
      })
      .collect();

    Self {
      pc_in,
      z_in,
      pc_out,
      z_out,
    }
  }

  pub fn update<CS, SF>(&mut self, mut cs: CS, step_circuit: &SF) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    SF: EnforcingStepCircuit<E::Scalar>,
  {
    // Run the step circuit
    let cs_step = &mut cs.namespace(|| "synthesize");

    let (pc_curr, z_curr) = (Some(&self.pc_out), self.z_out.as_slice());

    let (pc_next, z_next) = step_circuit.enforcing_synthesize(cs_step, pc_curr, z_curr)?;

    self.pc_out = pc_next.ok_or(SynthesisError::AssignmentMissing)?;
    self.z_out = z_next.to_vec();
    Ok(())
  }

  pub fn merge<CS>(mut cs: CS, io_L: Self, io_R: Self) -> Self
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    // io_L.pc_out = io_R.pc_in
    cs.enforce(
      || "io_L.pc_out = io_R.pc_in",
      |lc| lc,
      |lc| lc,
      |lc| lc + io_L.pc_out.get_variable() - io_R.pc_in.get_variable(),
    );

    // io_L.z_out = io_R.z_in
    zip_eq(&io_L.z_out, &io_R.z_in)
      .enumerate()
      .for_each(|(i, (z_L_i, z_R_i))| {
        cs.enforce(
          || format!("io_L.z_out[{i}] = io_R.z_in[{i}]"),
          |lc| lc,
          |lc| lc,
          |lc| lc + z_L_i.get_variable() - z_R_i.get_variable(),
        );
      });
    Self {
      pc_in: io_L.pc_in,
      z_in: io_L.z_in,
      pc_out: io_R.pc_out,
      z_out: io_R.z_out,
    }
  }

  pub fn enforce_trivial<CS>(&self, mut cs: CS, is_trivial: &Boolean)
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    let is_trivial = is_trivial.lc(CS::one(), E::Scalar::ONE);

    // (is_trivial) * (z_in - z_out) = 0
    zip_eq(&self.z_in, &self.z_out)
      .enumerate()
      .for_each(|(i, (z_in_i, z_out_i))| {
        cs.enforce(
          || format!("(is_trivial) * (z_in[{i}] - z_out[{i}]) = 0"),
          |_| is_trivial.clone(),
          |lc| lc + z_in_i.get_variable() - z_out_i.get_variable(),
          |lc| lc,
        );
      });

    // (is_trivial) * (pc_in - pc_out) = 0
    cs.enforce(
      || "(is_trivial) * (pc_in - pc_out) = 0",
      |_| is_trivial,
      |lc| lc + self.pc_in.get_variable() - self.pc_out.get_variable(),
      |lc| lc,
    );
  }

  /// Attempt to extract the native representation.
  pub fn get_value(&self) -> Option<NIVCIO<E>> {
    let pc_in = self.pc_in.get_value()?;
    let z_in = self
      .z_in
      .iter()
      .map(|z| z.get_value())
      .collect::<Option<Vec<_>>>()?;
    let pc_out = self.pc_out.get_value()?;
    let z_out = self
      .z_out
      .iter()
      .map(|z| z.get_value())
      .collect::<Option<Vec<_>>>()?;
    Some(NIVCIO {
      pc_in,
      z_in,
      pc_out,
      z_out,
    })
  }
}

impl<E: CurveCycleEquipped> NIVCIO<E> {
  pub fn new(pc_init: usize, z_init: Vec<E::Scalar>) -> Self {
    Self {
      pc_in: E::Scalar::from(pc_init as u64),
      z_in: z_init.clone(),
      pc_out: E::Scalar::from(pc_init as u64),
      z_out: z_init,
    }
  }

  pub fn dummy(arity: usize) -> Self {
    Self {
      pc_in: Default::default(),
      z_in: vec![Default::default(); arity],
      pc_out: Default::default(),
      z_out: vec![Default::default(); arity],
    }
  }
}

impl<E: CurveCycleEquipped> HashWriter<E> for NIVCIO<E> {
  fn write<H: Hasher<E>>(&self, hasher: &mut H) {
    hasher.absorb_scalar(self.pc_in);
    for z in &self.z_in {
      hasher.absorb_scalar(*z);
    }
    hasher.absorb_scalar(self.pc_out);
    for z in &self.z_out {
      hasher.absorb_scalar(*z);
    }
  }
}

impl<E: CurveCycleEquipped> AllocatedHashWriter<E::Scalar> for AllocatedNIVCIO<E> {
  fn write<H: AllocatedHasher<E::Scalar>>(&self, hasher: &mut H) {
    self.pc_in.write(hasher);
    self.z_in.write(hasher);
    self.pc_in.write(hasher);
    self.z_in.write(hasher);
  }
}
