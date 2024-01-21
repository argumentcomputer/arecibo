//! This module implements the Hyrax polynomial commitment scheme
use crate::{
  errors::NovaError,
  provider::ipa_pc::{InnerProductArgument, InnerProductInstance, InnerProductWitness},
  provider::pedersen::{
    Commitment as PedersenCommitment, CommitmentEngine as PedersenCommitmentEngine,
    CommitmentEngineExtTrait, CommitmentKey as PedersenCommitmentKey,
    CompressedCommitment as PedersenCompressedCommitment,
  },
  provider::traits::DlogGroup,
  spartan::polys::{eq::EqPolynomial, multilinear::MultilinearPolynomial},
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentTrait, Len},
    evaluation::EvaluationEngineTrait,
    AbsorbInROTrait, Engine, TranscriptEngineTrait, TranscriptReprTrait,
  },
  Commitment, CommitmentKey,
};
use abomonation_derive::Abomonation;
use core::ops::{Add, AddAssign, Mul, MulAssign};
use itertools::{
  EitherOrBoth::{Both, Left, Right},
  Itertools,
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

/// A type that holds commitment generators for Hyrax commitments
#[derive(Clone, Debug, Serialize, Deserialize, Abomonation, PartialEq, Eq)]
#[abomonation_omit_bounds]
#[serde(bound = "")]
pub struct HyraxCommitmentKey<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  ck: PedersenCommitmentKey<E>,
}

impl<E> Len for HyraxCommitmentKey<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  fn length(&self) -> usize {
    self.ck.length()
  }
}

/// Structure that holds commitments
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_omit_bounds]
pub struct HyraxCommitment<E: Engine> {
  comm: Vec<PedersenCommitment<E>>,
  is_default: bool,
}

/// Structure that holds compressed commitments
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct HyraxCompressedCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  comm: Vec<PedersenCompressedCommitment<E>>,
  is_default: bool,
}

impl<E: Engine> Default for HyraxCommitment<E> {
  fn default() -> Self {
    Self {
      comm: vec![],
      is_default: true,
    }
  }
}

impl<E> AbsorbInROTrait<E> for HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  fn absorb_in_ro(&self, _ro: &mut <E as Engine>::RO) {
    todo!()
  }
}

impl<E> CommitmentTrait<E> for HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  type CompressedCommitment = HyraxCompressedCommitment<E>;

  fn compress(&self) -> Self::CompressedCommitment {
    HyraxCompressedCommitment {
      comm: self.comm.iter().map(|c| c.compress()).collect::<Vec<_>>(),
      is_default: self.is_default,
    }
  }

  fn decompress(c: &Self::CompressedCommitment) -> Result<Self, NovaError> {
    let comm = c
      .comm
      .iter()
      .map(|c| <PedersenCommitment<E> as CommitmentTrait<E>>::decompress(c))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self {
      comm,
      is_default: c.is_default,
    })
  }

  fn to_coordinates(
    &self,
  ) -> (
    <E as Engine>::Base,
    <E as Engine>::Base,
    bool,
  ) {
    todo!()
  }
}

impl<E> MulAssign<E::Scalar> for HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  fn mul_assign(&mut self, scalar: E::Scalar) {
    let result = (self as &Self)
      .comm
      .iter()
      .map(|c| c * &scalar)
      .collect();
    *self = Self {
      comm: result,
      is_default: self.is_default,
    };
  }
}

impl<'a, 'b, E> Mul<&'b E::Scalar> for &'a HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  type Output = HyraxCommitment<E>;
  fn mul(self, scalar: &'b E::Scalar) -> HyraxCommitment<E> {
    let result = self.comm.iter().map(|c| c * scalar).collect();
    HyraxCommitment {
      comm: result,
      is_default: self.is_default,
    }
  }
}

impl<E> Mul<E::Scalar> for HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  type Output = Self;

  fn mul(self, scalar: E::Scalar) -> Self {
    let result = self.comm.iter().map(|c| c * &scalar).collect();
    Self {
      comm: result,
      is_default: self.is_default,
    }
  }
}

impl<'b, E> AddAssign<&'b Self> for HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  fn add_assign(&mut self, other: &'b Self) {
    if self.is_default {
      *self = other.clone();
    } else if other.is_default {
      return;
    } else {
      let result = (self as &Self)
        .comm
        .iter()
        .zip_longest(other.comm.iter())
        .map(|x| match x {
          Both(a, b) => a + b,
          Left(a) => *a,
          Right(b) => *b,
        })
        .collect();
      *self = Self {
        comm: result,
        is_default: self.is_default,
      };
    }
  }
}

impl<'a, 'b, E> Add<&'b HyraxCommitment<E>> for &'a HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  type Output = HyraxCommitment<E>;
  fn add(self, other: &'b HyraxCommitment<E>) -> HyraxCommitment<E> {
    if self.is_default {
      other.clone()
    } else if other.is_default {
      self.clone()
    } else {
      let result = self
        .comm
        .iter()
        .zip_longest(other.comm.iter())
        .map(|x| match x {
          Both(a, b) => a + b,
          Left(a) => *a,
          Right(b) => *b,
        })
        .collect();
      HyraxCommitment {
        comm: result,
        is_default: self.is_default,
      }
    }
  }
}

macro_rules! define_add_variants {
  (LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
    impl<'b, E> Add<&'b $rhs> for $lhs
    where
      E: Engine,
      E::GE: DlogGroup<ScalarExt = E::Scalar>,
    {
      type Output = $out;
      fn add(self, rhs: &'b $rhs) -> $out {
        &self + rhs
      }
    }

    impl<'a, E> Add<$rhs> for &'a $lhs
    where
      E: Engine,
      E::GE: DlogGroup<ScalarExt = E::Scalar>,
    {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        self + &rhs
      }
    }

    impl<E> Add<$rhs> for $lhs
    where
      E: Engine,
      E::GE: DlogGroup<ScalarExt = E::Scalar>,
    {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        &self + &rhs
      }
    }
  };
}

macro_rules! define_add_assign_variants {
  (LHS = $lhs:ty, RHS = $rhs:ty) => {
    impl<E> AddAssign<$rhs> for $lhs
    where
      E: Engine,
      E::GE: DlogGroup<ScalarExt = E::Scalar>,
    {
      fn add_assign(&mut self, rhs: $rhs) {
        *self += &rhs;
      }
    }
  };
}

define_add_assign_variants!(LHS = HyraxCommitment<E>, RHS = HyraxCommitment<E>);
define_add_variants!(LHS = HyraxCommitment<E>, RHS = HyraxCommitment<E>, Output = HyraxCommitment<E>);

/// Provides a commitment engine
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HyraxCommitmentEngine<E: Engine> {
  _p: PhantomData<E>,
}

impl<E> CommitmentEngineTrait<E> for HyraxCommitmentEngine<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  type CommitmentKey = HyraxCommitmentKey<E>;
  type Commitment = HyraxCommitment<E>;

  /// Derives generators for Hyrax PC, where num_vars is the number of variables in multilinear poly
  fn setup(label: &'static [u8], n: usize) -> Self::CommitmentKey {
    let num_vars = u64::try_from(n.next_power_of_two()).unwrap().ilog2() as usize;
    let (_left, right) = EqPolynomial::<E::Scalar>::compute_factored_lens(num_vars);
    let ck = PedersenCommitmentEngine::setup(label, (2usize).pow(right as u32));
    HyraxCommitmentKey { ck }
  }

  fn commit(ck: &Self::CommitmentKey, v: &[E::Scalar]) -> Self::Commitment {
    let poly = MultilinearPolynomial::new(v.to_vec());
    let n = poly.len();
    let ell = poly.get_num_vars();
    assert_eq!(n, (2usize).pow(ell as u32));

    let (left_num_vars, right_num_vars) = EqPolynomial::<E::Scalar>::compute_factored_lens(ell);
    let L_size = (2usize).pow(left_num_vars as u32);
    let R_size = (2usize).pow(right_num_vars as u32);
    assert_eq!(L_size * R_size, n);

    let comm = (0..L_size)
      .collect::<Vec<usize>>()
      .into_par_iter()
      .map(|i| {
        PedersenCommitmentEngine::commit(&ck.ck, &poly.evaluations()[R_size * i..R_size * (i + 1)])
      })
      .collect();

    HyraxCommitment {
      comm,
      is_default: false,
    }
  }
}

impl<E> TranscriptReprTrait<E::GE> for HyraxCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  fn to_transcript_bytes(&self) -> Vec<u8> {
    let mut v = Vec::new();

    v.extend_from_slice(b"hyrax_commitment_begin");

    for c in &self.comm {
      v.extend_from_slice(&c.to_transcript_bytes());
    }

    v.extend_from_slice(b"hyrax_commitment_end");

    v
  }
}

impl<E> TranscriptReprTrait<E::GE> for HyraxCompressedCommitment<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  fn to_transcript_bytes(&self) -> Vec<u8> {
    let mut v = Vec::new();
    v.append(&mut b"poly_commitment_begin".to_vec());

    for c in &self.comm {
      v.append(&mut c.to_transcript_bytes());
    }

    v.append(&mut b"poly_commitment_end".to_vec());
    v
  }
}

/// Provides an implementation of the hyrax key
#[derive(Clone, Debug, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_omit_bounds]
pub struct HyraxProverKey<E: Engine> {
  ck_s: CommitmentKey<E>,
}

/// Provides an implementation of the hyrax key
#[derive(Clone, Debug, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_omit_bounds]
pub struct HyraxVerifierKey<E: Engine> {
  ck_v: CommitmentKey<E>,
  ck_s: CommitmentKey<E>,
}

/// Provides an implementation of a polynomial evaluation argument
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct HyraxEvaluationArgument<E>
where
  E: Engine,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
{
  ipa: InnerProductArgument<E>,
}

/// Provides an implementation of a polynomial evaluation engine using Hyrax PC
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct HyraxEvaluationEngine<E: Engine> {
  _p: PhantomData<E>,
}

impl<E> EvaluationEngineTrait<E> for HyraxEvaluationEngine<E>
where
  E: Engine<CE = HyraxCommitmentEngine<E>>,
  E::GE: DlogGroup<ScalarExt = E::Scalar>,
  // CommitmentKey<E>: CommitmentKeyExtTrait<E>,
{
  type ProverKey = HyraxProverKey<E>;
  type VerifierKey = HyraxVerifierKey<E>;
  type EvaluationArgument = HyraxEvaluationArgument<E>;

  fn setup(
    ck: &<<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey,
  ) -> (Self::ProverKey, Self::VerifierKey) {
    let pk = HyraxProverKey::<E> {
      ck_s: E::CE::setup(b"hyrax", 1),
    };
    let vk = HyraxVerifierKey::<E> {
      ck_v: ck.clone(),
      ck_s: E::CE::setup(b"hyrax", 1),
    };
    (pk, vk)
  }

  fn prove(
    ck: &CommitmentKey<E>,
    pk: &Self::ProverKey,
    transcript: &mut E::TE,
    comm: &Commitment<E>,
    poly: &[E::Scalar],
    point: &[E::Scalar],
    eval: &E::Scalar,
  ) -> Result<Self::EvaluationArgument, NovaError> {
    transcript.absorb(b"poly_com", comm);

    let poly_m = MultilinearPolynomial::<E::Scalar>::new(poly.to_vec());

    // assert vectors are of the right size
    assert_eq!(poly_m.get_num_vars(), point.len());

    let (left_num_vars, right_num_vars) =
      EqPolynomial::<E::Scalar>::compute_factored_lens(point.len());
    let L_size = (2usize).pow(left_num_vars as u32);
    let R_size = (2usize).pow(right_num_vars as u32);

    // compute the L and R vectors (these depend only on the public challenge point so they are public)
    let eq = EqPolynomial::new(point.to_vec());
    let (L, R) = eq.compute_factored_evals();

    assert_eq!(L.len(), L_size);
    assert_eq!(R.len(), R_size);

    // compute the vector underneath L*Z
    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = poly_m.bind(&L);

    // Commit to LZ
    let com_LZ = PedersenCommitmentEngine::commit(&ck.ck, &LZ);

    // a dot product argument (IPA) of size R_size
    let ipa_instance = InnerProductInstance::<E>::new(&com_LZ, &R, eval);
    let ipa_witness = InnerProductWitness::<E>::new(&LZ);
    let ipa = InnerProductArgument::<E>::prove(
      &ck.ck,
      &pk.ck_s.ck,
      &ipa_instance,
      &ipa_witness,
      transcript,
    )?;

    Ok(HyraxEvaluationArgument { ipa })
  }

  fn verify(
    vk: &Self::VerifierKey,
    transcript: &mut E::TE,
    comm: &Commitment<E>,
    point: &[E::Scalar],
    eval: &E::Scalar,
    arg: &Self::EvaluationArgument,
  ) -> Result<(), NovaError> {
    transcript.absorb(b"poly_com", comm);

    // compute L and R
    let eq = EqPolynomial::new(point.to_vec());
    let (L, R) = eq.compute_factored_evals();

    // compute a weighted sum of commitments and L
    let ck = PedersenCommitmentEngine::reinterpret_commitments_as_ck(&comm.comm);

    let com_LZ = PedersenCommitmentEngine::commit(&ck, &L); // computes MSM of commitment and L

    let ipa_instance = InnerProductInstance::<E>::new(&com_LZ, &R, eval);

    arg
      .ipa
      .verify(&vk.ck_v.ck, &vk.ck_s.ck, R.len(), &ipa_instance, transcript)
  }
}
