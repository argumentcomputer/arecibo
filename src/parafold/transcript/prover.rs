use ff::PrimeField;

use crate::traits::Engine;

pub trait TranscriptRepresentable<F: PrimeField> {
  fn to_field_vec(&self) -> Vec<F>;
}

pub struct Transcript<E: Engine> {
  // ro_consts: ROConstants<E>,
  state: Vec<E::Scalar>,
}

impl<F: PrimeField> TranscriptRepresentable<F> for F {
  fn to_field_vec(&self) -> Vec<F> {
    vec![self]
  }
}

impl<E: Engine> Transcript<E> {
  pub fn new() -> Self {
    todo!()
  }
  pub fn absorb<T>(&mut self, element: &T)
  where
    T: TranscriptRepresentable<E::Scalar>,
  {
    self.state.extend(element.to_field_vec().into_iter());
  }

  pub fn squeeze(&mut self) -> E::Scalar {
    todo!()
    // let mut ro = E::RO::new(self.ro_consts.clone(), self.state.len());
    // for e in self.state.drain(..) {
    //   ro.absorb(&e);
    // }
    // // FIXME: We only need small challenges when folding secondary circuits
    // let output = ro.squeeze(128);
    //
    // self.state.extend([output.clone()]);
    // Ok(output)
  }
}
