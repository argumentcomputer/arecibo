use crate::traits::Engine;
use ff::PrimeField;

pub trait TranscriptRepresentable<F: PrimeField> {
  // With Rust 1.75 we can return impl Iterator<Item = F>
  fn to_field_vec(&self) -> Vec<F>;
}

pub struct Transcript<E1: Engine> {
  // ro_consts: ROConstants<E>,
  state: Vec<E1::Scalar>,
}

impl<F: PrimeField> TranscriptRepresentable<F> for F {
  fn to_field_vec(&self) -> Vec<F> {
    vec![*self]
  }
}

impl<E1: Engine> Transcript<E1> {
  pub fn new() -> Self {
    todo!()
  }
  pub fn absorb<T>(&mut self, element: &T)
  where
    T: TranscriptRepresentable<E1::Scalar>,
  {
    self.state.extend(element.to_field_vec().into_iter());
  }

  pub fn squeeze(&mut self) -> E1::Scalar {
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
  pub fn squeeze_bits(&mut self, _num_bits: usize) -> E1::Scalar {
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
