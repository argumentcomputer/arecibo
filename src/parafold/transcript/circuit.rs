use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::traits::Engine;

pub trait TranscriptRepresentable<F: PrimeField> {
  fn to_field_vec(&self) -> Vec<AllocatedNum<F>>;
}

impl<F: PrimeField> TranscriptRepresentable<F> for AllocatedNum<F> {
  fn to_field_vec(&self) -> Vec<AllocatedNum<F>> {
    vec![self.clone()]
  }
}

pub struct AllocatedTranscript<E: Engine> {
  // ro_consts: ROConstantsCircuit<E>,
  state: Vec<AllocatedNum<E::Scalar>>,
}

impl<E: Engine> AllocatedTranscript<E> {
  pub fn new<CS>() -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
  {
    Ok(Self {
      // ro_consts: ROConstantsCircuit::<E>::default(),
      state: vec![],
    })
  }
  pub fn absorb<CS, T>(&mut self, /*mut*/ _cs: CS, element: &T) -> Result<(), SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
    T: TranscriptRepresentable<E::Scalar>,
  {
    self.state.extend(element.to_field_vec());
    Ok(())
  }

  pub fn squeeze<CS>(
    &mut self,
    /*mut*/ _cs: CS,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    CS: ConstraintSystem<E::Scalar>,
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
