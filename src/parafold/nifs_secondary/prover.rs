use crate::provider::pedersen::Commitment;
use crate::traits::Engine;

#[derive(Debug, Clone)]
pub struct SecondaryRelaxedR1CS<E2: Engine> {
  instance: SecondaryRelaxedR1CSInstance<E2>,
  W: Vec<E2::Scalar>,
  E: Vec<E2::Scalar>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SecondaryRelaxedR1CSInstance<E2: Engine> {
  pub u: E2::Scalar,
  pub X: Vec<E2::Scalar>,
  pub W: Commitment<E2>,
  pub E: Commitment<E2>,
}
