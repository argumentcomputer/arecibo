//! This module defines nizk proofs
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use crate::errors::NovaError;
use crate::traits::{
  commitment::{CommitmentTrait, ZKCommitmentEngineTrait, Len},
  TranscriptEngineTrait,
};
use crate::{Commitment, CommitmentKey, CompressedCommitment, provider::Bn256EngineZKPedersen};
use ff::Field;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use crate::Engine;

/// KnowledgeProof
#[derive(Debug, Serialize, Deserialize)]
pub struct KnowledgeProof {
  alpha: CompressedCommitment<Bn256EngineZKPedersen>,
  z1: <Bn256EngineZKPedersen as Engine>::Scalar,
  z2: <Bn256EngineZKPedersen as Engine>::Scalar,
}

/// EqualityProof
#[derive(Debug, Serialize, Deserialize)]
pub struct EqualityProof {
  /// alpha
  pub alpha: CompressedCommitment<Bn256EngineZKPedersen>,
  /// z
  pub z: <Bn256EngineZKPedersen as Engine>::Scalar,
}

/// ProductProof
#[derive(Debug, Serialize, Deserialize)]
pub struct ProductProof {
  alpha: CompressedCommitment<Bn256EngineZKPedersen>,
  beta: CompressedCommitment<Bn256EngineZKPedersen>,
  delta: CompressedCommitment<Bn256EngineZKPedersen>,
  z: [<Bn256EngineZKPedersen as Engine>::Scalar; 5],
}

/// DocProductProof
#[derive(Debug, Serialize, Deserialize)]
pub struct DotProductProof {
  delta: CompressedCommitment<Bn256EngineZKPedersen>,
  beta: CompressedCommitment<Bn256EngineZKPedersen>,
  z: Vec<<Bn256EngineZKPedersen as Engine>::Scalar>,
  z_delta: <Bn256EngineZKPedersen as Engine>::Scalar,
  z_beta: <Bn256EngineZKPedersen as Engine>::Scalar,
}

/// KnowledgeProof
impl KnowledgeProof {
  /// protocol name
  pub fn protocol_name() -> &'static [u8] {
    b"knowledge proof"
  }

  /// prove
  pub fn prove(
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>,
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    x: &<Bn256EngineZKPedersen as Engine>::Scalar,
    r: &<Bn256EngineZKPedersen as Engine>::Scalar,
  ) -> Result<(KnowledgeProof, CompressedCommitment<Bn256EngineZKPedersen>), NovaError> {
    transcript.dom_sep(Self::protocol_name());

    // produce two random scalars
    let t1 = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let t2 = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let C = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[*x], r).compress();
    transcript.absorb(b"C", &C);

    let alpha = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[t1], &t2).compress();
    transcript.absorb(b"alpha", &alpha);

    let c = transcript.squeeze(b"c")?;

    let z1 = *x * c + t1;
    let z2 = *r * c + t2;

    Ok((Self { alpha, z1, z2 }, C))
  }

  /// verify
  pub fn verify(
    &self,
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>,
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    C: &CompressedCommitment<Bn256EngineZKPedersen>,
  ) -> Result<(), NovaError> {
    transcript.dom_sep(Self::protocol_name());
    transcript.absorb(b"C", C);
    transcript.absorb(b"alpha", &self.alpha);

    let c = transcript.squeeze(b"c")?;

    let lhs = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[self.z1], &self.z2).compress();
    let rhs = (Commitment::<Bn256EngineZKPedersen>::decompress(C)? * c
      + Commitment::<Bn256EngineZKPedersen>::decompress(&self.alpha)?)
    .compress();

    if lhs == rhs {
      Ok(())
    } else {
      Err(NovaError::InvalidZkKnowledgeProof)
    }
  }
}

/// EqualityProof
impl EqualityProof {
  /// protocol name
  pub fn protocol_name() -> &'static [u8] {
    b"equality proof"
  }

  /// prove
  pub fn prove(
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>,
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    v1: &<Bn256EngineZKPedersen as Engine>::Scalar,
    s1: &<Bn256EngineZKPedersen as Engine>::Scalar,
    v2: &<Bn256EngineZKPedersen as Engine>::Scalar,
    s2: &<Bn256EngineZKPedersen as Engine>::Scalar,
  ) -> Result<(EqualityProof, CompressedCommitment<Bn256EngineZKPedersen>, CompressedCommitment<Bn256EngineZKPedersen>), NovaError> {
    transcript.dom_sep(Self::protocol_name());

    // produce a random scalar
    let r = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let C1 = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[*v1], s1).compress();
    transcript.absorb(b"C1", &C1);

    let C2 = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[*v2], s2).compress();
    transcript.absorb(b"C2", &C2);

    let alpha = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      ck_n,
      &[<Bn256EngineZKPedersen as Engine>::Scalar::ZERO],
      &r,
    )
    .compress(); // h^r
    transcript.absorb(b"alpha", &alpha);

    let c = transcript.squeeze(b"c")?;

    let z = c * (*s1 - *s2) + r;

    Ok((Self { alpha, z }, C1, C2))
  }

  /// verify
  pub fn verify(
    &self,
    gens_n: &CommitmentKey<Bn256EngineZKPedersen>,
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    C1: &CompressedCommitment<Bn256EngineZKPedersen>,
    C2: &CompressedCommitment<Bn256EngineZKPedersen>,
  ) -> Result<(), NovaError> {
    transcript.dom_sep(Self::protocol_name());
    transcript.absorb(b"C1", C1);
    transcript.absorb(b"C2", C2);
    transcript.absorb(b"alpha", &self.alpha);

    let c = transcript.squeeze(b"c")?;

    let rhs = {
      let C = Commitment::<Bn256EngineZKPedersen>::decompress(C1)?
        - Commitment::<Bn256EngineZKPedersen>::decompress(C2)?;
      (C * c + Commitment::<Bn256EngineZKPedersen>::decompress(&self.alpha)?).compress()
    };

    let lhs = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(
      gens_n,
      &[<Bn256EngineZKPedersen as Engine>::Scalar::ZERO],
      &self.z,
    )
    .compress(); // h^z

    if lhs == rhs {
      Ok(())
    } else {
      Err(NovaError::InvalidZkEqualityProof)
    }
  }
}

/// DotProductProof
impl DotProductProof {
  /// protocol name
  pub fn protocol_name() -> &'static [u8] {
    b"dot product proof"
  }

  /// compute dot product
  pub fn compute_dotproduct(a: &[<Bn256EngineZKPedersen as Engine>::Scalar], b: &[<Bn256EngineZKPedersen as Engine>::Scalar]) -> <Bn256EngineZKPedersen as Engine>::Scalar {
    assert_eq!(a.len(), b.len());
    let mut result = <Bn256EngineZKPedersen as Engine>::Scalar::ZERO;

    for i in 0..a.len() {
      result += a[i] * b[i];
    }

    result
  }

  /// prove
  pub fn prove(
    ck_1: &CommitmentKey<Bn256EngineZKPedersen>, // generator of size 1
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>, // generators of size n
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    x_vec: &[<Bn256EngineZKPedersen as Engine>::Scalar],
    blind_x: &<Bn256EngineZKPedersen as Engine>::Scalar,
    a_vec: &[<Bn256EngineZKPedersen as Engine>::Scalar],
    y: &<Bn256EngineZKPedersen as Engine>::Scalar,
    blind_y: &<Bn256EngineZKPedersen as Engine>::Scalar,
  ) -> Result<(Self, CompressedCommitment<Bn256EngineZKPedersen>, CompressedCommitment<Bn256EngineZKPedersen>), NovaError> {
    transcript.dom_sep(Self::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(ck_n.length(), a_vec.len());
    assert_eq!(ck_1.length(), 1);

    // produce randomness for the proofs
    let d_vec = (0..n)
      .map(|_i| <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng))
      .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>();

    let r_delta = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let r_beta = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let Cx = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, x_vec, blind_x).compress();
    transcript.absorb(b"Cx", &Cx);

    let Cy = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[*y], blind_y).compress();
    transcript.absorb(b"Cy", &Cy);

    transcript.absorb(b"a", &a_vec);

    let delta = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &d_vec, &r_delta).compress();
    transcript.absorb(b"delta", &delta);

    let dotproduct_a_d = DotProductProof::compute_dotproduct(a_vec, &d_vec);

    let beta = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[dotproduct_a_d], &r_beta).compress();
    transcript.absorb(b"beta", &beta);

    let c = transcript.squeeze(b"c")?;

    let z = (0..d_vec.len())
      .map(|i| c * x_vec[i] + d_vec[i])
      .collect::<Vec<<Bn256EngineZKPedersen as Engine>::Scalar>>();

    let z_delta = c * blind_x + r_delta;
    let z_beta = c * blind_y + r_beta;

    Ok((
      DotProductProof {
        delta,
        beta,
        z,
        z_delta,
        z_beta,
      },
      Cx,
      Cy,
    ))
  }

  /// verify
  pub fn verify(
    &self,
    ck_1: &CommitmentKey<Bn256EngineZKPedersen>, // generator of size 1
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>, // generator of size n
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    a_vec: &[<Bn256EngineZKPedersen as Engine>::Scalar],
    Cx: &CompressedCommitment<Bn256EngineZKPedersen>,
    Cy: &CompressedCommitment<Bn256EngineZKPedersen>,
  ) -> Result<(), NovaError> {
    assert_eq!(ck_n.length(), a_vec.len());
    assert_eq!(ck_1.length(), 1);

    transcript.dom_sep(Self::protocol_name());

    transcript.absorb(b"Cx", Cx);
    transcript.absorb(b"Cy", Cy);
    transcript.absorb(b"a", &a_vec);
    transcript.absorb(b"delta", &self.delta);
    transcript.absorb(b"beta", &self.beta);

    let c = transcript.squeeze(b"c")?;

    let mut result = Commitment::<Bn256EngineZKPedersen>::decompress(Cx)? * c
      + Commitment::<Bn256EngineZKPedersen>::decompress(&self.delta)?
      == <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &self.z, &self.z_delta);

    let dotproduct_z_a = DotProductProof::compute_dotproduct(&self.z, a_vec);
    result &= Commitment::<Bn256EngineZKPedersen>::decompress(Cy)? * c + Commitment::<Bn256EngineZKPedersen>::decompress(&self.beta)?
      == <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_1, &[dotproduct_z_a], &self.z_beta);

    if result {
      Ok(())
    } else {
      Err(NovaError::InvalidZkDotProductProof)
    }
  }
}
