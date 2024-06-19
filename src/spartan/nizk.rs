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

/// product proof
impl ProductProof {
  /// protocol name
  pub fn protocol_name() -> &'static [u8] {
    b"product proof"
  }

  /// prove
  pub fn prove(
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>,
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    x: &<Bn256EngineZKPedersen as Engine>::Scalar,
    rX: &<Bn256EngineZKPedersen as Engine>::Scalar,
    y: &<Bn256EngineZKPedersen as Engine>::Scalar,
    rY: &<Bn256EngineZKPedersen as Engine>::Scalar,
    z: &<Bn256EngineZKPedersen as Engine>::Scalar,
    rZ: &<Bn256EngineZKPedersen as Engine>::Scalar,
  ) -> Result<
    (
      ProductProof,
      CompressedCommitment<Bn256EngineZKPedersen>,
      CompressedCommitment<Bn256EngineZKPedersen>,
      CompressedCommitment<Bn256EngineZKPedersen>,
    ),
    NovaError,
  > {
    transcript.dom_sep(Self::protocol_name());

    // produce 5 random scalars
    let b1 = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let b2 = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let b3 = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let b4 = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);
    let b5 = <Bn256EngineZKPedersen as Engine>::Scalar::random(&mut OsRng);

    let X = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[*x], rX).compress();
    transcript.absorb(b"X", &X);

    let Y = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[*y], rY).compress();
    transcript.absorb(b"Y", &Y);

    let Z = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[*z], rZ).compress();
    transcript.absorb(b"Z", &Z);

    let alpha = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[b1], &b2).compress();
    transcript.absorb(b"alpha", &alpha);

    let beta = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[b3], &b4).compress();
    transcript.absorb(b"beta", &beta);

    let delta = {
      let h_to_b5 = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[<Bn256EngineZKPedersen as Engine>::Scalar::ZERO], &b5); // h^b5
      (Commitment::<Bn256EngineZKPedersen>::decompress(&X)? * b3 + h_to_b5).compress() // X^b3*h^b5
    };

    transcript.absorb(b"delta", &delta);

    let c = transcript.squeeze(b"c")?;

    let z1 = b1 + c * *x;
    let z2 = b2 + c * *rX;
    let z3 = b3 + c * *y;
    let z4 = b4 + c * *rY;
    let z5 = b5 + c * (*rZ - *rX * *y);
    let z = [z1, z2, z3, z4, z5];

    Ok((
      Self {
        alpha,
        beta,
        delta,
        z,
      },
      X,
      Y,
      Z,
    ))
  }

  /// check_equality
  fn check_equality(
    P: &CompressedCommitment<Bn256EngineZKPedersen>,
    X: &CompressedCommitment<Bn256EngineZKPedersen>,
    c: &<Bn256EngineZKPedersen as Engine>::Scalar,
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>,
    z1: &<Bn256EngineZKPedersen as Engine>::Scalar,
    z2: &<Bn256EngineZKPedersen as Engine>::Scalar,
  ) -> Result<bool, NovaError> {
    let lhs = (Commitment::<Bn256EngineZKPedersen>::decompress(P)? + Commitment::<Bn256EngineZKPedersen>::decompress(X)? * *c).compress();
    let rhs = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[*z1], z2).compress();

    Ok(lhs == rhs)
  }

  /// verify
  pub fn verify(
    &self,
    ck_n: &CommitmentKey<Bn256EngineZKPedersen>,
    transcript: &mut <Bn256EngineZKPedersen as Engine>::TE,
    X: &CompressedCommitment<Bn256EngineZKPedersen>,
    Y: &CompressedCommitment<Bn256EngineZKPedersen>,
    Z: &CompressedCommitment<Bn256EngineZKPedersen>,
  ) -> Result<(), NovaError> {
    transcript.dom_sep(Self::protocol_name());

    transcript.absorb(b"X", X);
    transcript.absorb(b"Y", Y);
    transcript.absorb(b"Z", Z);
    transcript.absorb(b"alpha", &self.alpha);
    transcript.absorb(b"beta", &self.beta);
    transcript.absorb(b"delta", &self.delta);

    let z1 = self.z[0];
    let z2 = self.z[1];
    let z3 = self.z[2];
    let z4 = self.z[3];
    let z5 = self.z[4];

    let c = transcript.squeeze(b"c")?;

    let res = ProductProof::check_equality(&self.alpha, X, &c, ck_n, &z1, &z2)?
      && ProductProof::check_equality(&self.beta, Y, &c, ck_n, &z3, &z4)?;

    let res2 = {
      let lhs = (Commitment::<Bn256EngineZKPedersen>::decompress(&self.delta)? + Commitment::<Bn256EngineZKPedersen>::decompress(Z)? * c)
        .compress();

      let h_to_z5 = <Bn256EngineZKPedersen as Engine>::CE::zkcommit(ck_n, &[<Bn256EngineZKPedersen as Engine>::Scalar::ZERO], &z5); // h^z5
      let rhs = (Commitment::<Bn256EngineZKPedersen>::decompress(X)? * z3 + h_to_z5).compress(); // X^z3*h^z5
      lhs == rhs
    };

    if res && res2 {
      Ok(())
    } else {
      Err(NovaError::InvalidZkProductProof)
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
