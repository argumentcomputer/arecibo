use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::traits::{Engine, ROConstantsCircuit};

pub trait TranscriptRepresentable<F: PrimeField> {
  fn to_field_vec(&self) -> Vec<AllocatedNum<F>>;
}

impl<F: PrimeField> TranscriptRepresentable<F> for AllocatedNum<F> {
  fn to_field_vec(&self) -> Vec<AllocatedNum<F>> {
    vec![self.clone()]
  }
}

pub struct AllocatedTranscript< E1: Engine> {
  ro_consts: ROConstantsCircuit<E1>,
  state: Vec<AllocatedNum<E1::Scalar>>,
}

impl<E1:Engine> AllocatedTranscript<E1>
{
  pub fn new(ro_consts: ROConstantsCircuit<E1>) -> Self {
    Self {
      ro_consts,
      state: vec![],
    }
  }
  pub fn absorb<T>(&mut self, element: &T)
  where
    T: TranscriptRepresentable<E1::Scalar>,
  {
    self.state.extend(element.to_field_vec());
  }

  pub fn squeeze<CS>(&mut self, /*mut*/ _cs: CS) -> Result<AllocatedNum<E1::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    todo!()
    // let mut ro = E::ROCircuit::new(self.ro_consts.clone(), self.state.len());
    // for e in self.state.drain(..) {
    //   ro.absorb(&e);
    // }
    // // FIXME: We only need small challenges when folding secondary circuits
    // let output_bits = ro.squeeze(cs.namespace(|| "squeeze"), 128)?;
    // let output = le_bits_to_num(cs.namespace(|| "bits to num"), &output_bits)?;
    //
    // self.state.extend([output.clone()]);
    // Ok(output)
  }

  pub fn squeeze_bits<CS>(
    &mut self,
    /*mut*/ _cs: CS,
    _num_bits: usize,
  ) -> Result<Vec<AllocatedBit>, SynthesisError>
  where
    CS: ConstraintSystem<E1::Scalar>,
  {
    todo!()
    // let mut ro = E::ROCircuit::new(self.ro_consts.clone(), self.state.len());
    // for e in self.state.drain(..) {
    //   ro.absorb(&e);
    // }
    // // FIXME: We only need small challenges when folding secondary circuits
    // let output_bits = ro.squeeze(cs.namespace(|| "squeeze"), 128)?;
    // let output = le_bits_to_num(cs.namespace(|| "bits to num"), &output_bits)?;
    //
    // self.state.extend([output.clone()]);
    // Ok(output)
  }
}
