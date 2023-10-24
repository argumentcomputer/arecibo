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
  Group,
};

use super::{
  non_hiding_kzg::{UVKZGCommitment, UVUniversalKZGParam},
  pedersen::Commitment,
};

/// Provides a commitment engine
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KZGCommitmentEngine<E: Engine> {
  _p: PhantomData<E>,
}

impl<E: Engine> CommitmentEngineTrait<E::G1> for KZGCommitmentEngine<E>
where
  E::G1: Group<PreprocessedGroupElement = E::G1Affine>,
  E::G1Affine: Serialize + for<'de> Deserialize<'de>,
  E::G2Affine: Serialize + for<'de> Deserialize<'de>,
{
  type CommitmentKey = UVUniversalKZGParam<E>;
  type Commitment = Commitment<E::G1>;

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

impl<E: Engine> From<Commitment<E::G1>> for UVKZGCommitment<E>
where
  E::G1: Group,
{
  fn from(c: Commitment<E::G1>) -> Self {
    UVKZGCommitment(c.comm.to_affine())
  }
}

impl<E: Engine> From<UVKZGCommitment<E>> for Commitment<E::G1>
where
  E::G1: Group,
{
  fn from(c: UVKZGCommitment<E>) -> Self {
    Commitment {
      comm: c.0.to_curve(),
    }
  }
}
