//! Commitment engine for KZG commitments
//!

use std::marker::PhantomData;

use ff::PrimeFieldBits;
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
  non_hiding_kzg::{UVKZGCommitment, UniversalKZGParam},
  pedersen::Commitment,
  traits::DlogGroup,
};

use super::traits::{FixedBaseMSM, VariableBaseMSM};

/// Provides a commitment engine
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KZGCommitmentEngine<E> {
  _p: PhantomData<E>,
}

impl<E: Engine, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> CommitmentEngineTrait<NE>
  for KZGCommitmentEngine<E>
where
  E::G1: DlogGroup<ScalarExt = E::Fr, AffineExt = E::G1Affine> + VariableBaseMSM + FixedBaseMSM,
  E::G1Affine: Serialize + for<'de> Deserialize<'de>,
  E::G2Affine: Serialize + for<'de> Deserialize<'de>,
  E::Fr: PrimeFieldBits, // TODO due to use of gen_srs_for_testing, make optional
{
  type CommitmentKey = UniversalKZGParam<E>;
  type Commitment = Commitment<NE>;
  type MSMContext<'a> = <E::G1 as FixedBaseMSM>::MSMContext<'a>;

  fn setup(label: &'static [u8], n: usize) -> Self::CommitmentKey {
    // TODO: this is just for testing, replace by grabbing from a real setup for production
    let mut bytes = [0u8; 32];
    let len = label.len().min(32);
    bytes[..len].copy_from_slice(&label[..len]);
    let rng = &mut StdRng::from_seed(bytes);
    UniversalKZGParam::gen_srs_for_testing(rng, n.next_power_of_two())
  }

  fn commit(ck: &Self::CommitmentKey, v: &[<E::G1 as Group>::Scalar]) -> Self::Commitment {
    assert!(ck.length() >= v.len());
    Commitment {
      comm: E::G1::vartime_multiscalar_mul(v, &ck.powers_of_g[..v.len()]),
    }
  }

  fn into_context(ck: &Self::CommitmentKey) -> Self::MSMContext<'_> {
    <E::G1 as FixedBaseMSM>::init_context(&ck.powers_of_g)
  }

  fn commit_fixed(
    context: &Self::MSMContext<'_>,
    v: &[<NE as NovaEngine>::Scalar],
  ) -> Self::Commitment {
    Commitment {
      comm: E::G1::fixed_multiscalar_mul(v, context),
    }
  }
}

impl<E: Engine, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> From<Commitment<NE>>
  for UVKZGCommitment<E>
where
  E::G1: Group,
{
  fn from(c: Commitment<NE>) -> Self {
    Self(c.comm.to_affine())
  }
}

impl<E: Engine, NE: NovaEngine<GE = E::G1, Scalar = E::Fr>> From<UVKZGCommitment<E>>
  for Commitment<NE>
where
  E::G1: Group,
{
  fn from(c: UVKZGCommitment<E>) -> Self {
    Self {
      comm: c.0.to_curve(),
    }
  }
}
