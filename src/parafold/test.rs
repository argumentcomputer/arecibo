use std::marker::PhantomData;

use bellpepper_core::{ConstraintSystem, SynthesisError};
use bellpepper_core::num::AllocatedNum;
use ff::PrimeField;

use crate::supernova::{NonUniformCircuit, StepCircuit};
use crate::traits::CurveCycleEquipped;

#[derive(Clone, Debug)]
pub struct TrivialCircuit<F: PrimeField> {
  index: usize,
  pc_next: usize,
  _marker: PhantomData<F>,
}

impl<F: PrimeField> StepCircuit<F> for TrivialCircuit<F> {
  fn arity(&self) -> usize {
    1
  }

  fn circuit_index(&self) -> usize {
    self.index
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    _pc: Option<&AllocatedNum<F>>,
    z: &[AllocatedNum<F>],
  ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
    let pc_next =
      AllocatedNum::alloc_infallible(cs.namespace(|| "alloc pc"), || F::from(self.pc_next as u64));

    let z_next = AllocatedNum::alloc(cs.namespace(|| "alloc z_next"), || {
      let z_next = z[0].get_value().unwrap_or_default();
      Ok(z_next + F::ONE)
    })?;
    Ok((Some(pc_next), vec![z_next]))
  }
}

#[derive(Clone, Debug)]
pub struct TrivialNonUniform<E: CurveCycleEquipped> {
  num_circuits: usize,
  _marker: PhantomData<E>,
}

impl<E: CurveCycleEquipped> TrivialNonUniform<E> {
  pub fn new(num_circuits: usize) -> Self {
    Self {
      num_circuits,
      _marker: Default::default(),
    }
  }
}

impl<E: CurveCycleEquipped> NonUniformCircuit<E> for TrivialNonUniform<E> {
  type C1 = TrivialCircuit<E::Scalar>;
  type C2 = TrivialCircuit<E::Base>;

  fn num_circuits(&self) -> usize {
    self.num_circuits
  }

  fn primary_circuit(&self, circuit_index: usize) -> Self::C1 {
    TrivialCircuit {
      index: circuit_index,
      pc_next: (circuit_index + 1) % self.num_circuits,
      _marker: Default::default(),
    }
  }

  fn secondary_circuit(&self) -> Self::C2 {
    TrivialCircuit {
      index: 0,
      pc_next: 0,
      _marker: Default::default(),
    }
  }
}
