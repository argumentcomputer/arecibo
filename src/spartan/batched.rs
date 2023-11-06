//! TODO: Doc

use std::marker::PhantomData;

use serde::{Deserialize, Serialize};

use crate::traits::{
  evaluation::EvaluationEngineTrait,
  snark::{BatchedRelaxedR1CSSNARKTrait, DigestHelperTrait},
  Group,
};

use super::snark::RelaxedR1CSSNARK;

/// TODO: Doc
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<G: Group, EE: EvaluationEngineTrait<G>> {
  _p: PhantomData<(G, EE)>,
}

/// TODO: Doc
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifierKey<G: Group, EE: EvaluationEngineTrait<G>> {
  _p: PhantomData<(G, EE)>,
}

impl<G: Group, EE: EvaluationEngineTrait<G>> DigestHelperTrait<G> for VerifierKey<G, EE> {
  fn digest(&self) -> <G as Group>::Scalar {
    todo!()
  }
}

impl<G: Group, EE: EvaluationEngineTrait<G>> BatchedRelaxedR1CSSNARKTrait<G>
  for RelaxedR1CSSNARK<G, EE>
{
  type ProverKey = ProverKey<G, EE>;

  type VerifierKey = VerifierKey<G, EE>;

  fn setup(
    ck: &crate::CommitmentKey<G>,
    S: &[crate::r1cs::R1CSShape<G>],
  ) -> Result<(Self::ProverKey, Self::VerifierKey), crate::errors::NovaError> {
    todo!()
  }

  fn prove(
    ck: &crate::CommitmentKey<G>,
    pk: &Self::ProverKey,
    S: &[crate::r1cs::R1CSShape<G>],
    U: &[crate::r1cs::RelaxedR1CSInstance<G>],
    W: &[crate::r1cs::RelaxedR1CSWitness<G>],
  ) -> Result<Self, crate::errors::NovaError> {
    todo!()
  }

  fn verify(
    &self,
    vk: &Self::VerifierKey,
    U: &[crate::r1cs::RelaxedR1CSInstance<G>],
  ) -> Result<(), crate::errors::NovaError> {
    todo!()
  }
}
