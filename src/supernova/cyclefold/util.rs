use serde::{Deserialize, Serialize};

use crate::{
  r1cs::{R1CSInstance, RelaxedR1CSInstance},
  traits::Engine,
  Commitment,
};

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SuperNovaFoldingData<E: Engine> {
  pub U: Vec<Option<RelaxedR1CSInstance<E>>>,
  pub u: R1CSInstance<E>,
  pub T: Commitment<E>,
}

impl<E: Engine> SuperNovaFoldingData<E> {
  pub fn new(U: Vec<Option<RelaxedR1CSInstance<E>>>, u: R1CSInstance<E>, T: Commitment<E>) -> Self {
    Self { U, u, T }
  }
}
