//! Commitment engine for KZG commitments
//!

use std::marker::PhantomData;

use group::{prime::PrimeCurveAffine, Curve};
use pairing::Engine;
use rand::rngs::StdRng;
use rand_core::SeedableRng;
use serde::{Deserialize, Serialize};

use crate::traits::{
  commitment::{CommitmentEngineTrait, Len},
  Engine as NovaEngine, Group,
};

use crate::provider::{
  non_hiding_kzg::{UVKZGCommitment, UVUniversalKZGParam},
  pedersen::Commitment,
  traits::DlogGroup,
};

/// Provides a commitment engine
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KZGCommitmentEngine<E: Engine> {
  _p: PhantomData<E>,
}

impl<E: Engine, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> CommitmentEngineTrait<NE>
  for KZGCommitmentEngine<E>
where
  E::G1: DlogGroup<PreprocessedGroupElement = E::G1Affine, Scalar = E::Fr>,
  E::G1Affine: Serialize + for<'de> Deserialize<'de>,
  E::G2Affine: Serialize + for<'de> Deserialize<'de>,
{
  type CommitmentKey = UVUniversalKZGParam<E>;
  type Commitment = Commitment<NE>;

  fn setup(label: &'static [u8], n: usize) -> Self::CommitmentKey {
    // TODO: this is just for testing, replace by grabbing from a real setup for production
    let label_bytes: [u8; 32] = label[..32].try_into().unwrap();
    let rng = &mut StdRng::from_seed(label_bytes);
    UVUniversalKZGParam::gen_srs_for_testing(rng, n)
  }

  fn commit(ck: &Self::CommitmentKey, v: &[<E::G1 as Group>::Scalar]) -> Self::Commitment {
    assert!(ck.length() >= v.len());
    Commitment {
      comm: E::G1::vartime_multiscalar_mul(v, &ck.powers_of_g[..v.len()]),
    }
  }
}

impl<E: Engine, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> From<Commitment<NE>>
  for UVKZGCommitment<E>
where
  E::G1: Group,
{
  fn from(c: Commitment<NE>) -> Self {
    UVKZGCommitment(c.comm.to_affine())
  }
}

impl<E: Engine, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> From<UVKZGCommitment<E>>
  for Commitment<NE>
where
  E::G1: Group,
{
  fn from(c: UVKZGCommitment<E>) -> Self {
    Commitment {
      comm: c.0.to_curve(),
    }
  }
}
