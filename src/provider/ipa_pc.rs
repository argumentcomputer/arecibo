//! This module implements `EvaluationEngine` using an IPA-based polynomial commitment scheme
use crate::{
  digest::SimpleDigestible,
  errors::{NovaError, PCSError},
  provider::{pedersen::CommitmentKeyExtTrait, traits::DlogGroup},
  spartan::polys::eq::EqPolynomial,
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentTrait},
    evaluation::EvaluationEngineTrait,
    Engine, TranscriptEngineTrait, TranscriptReprTrait,
  },
  zip_with, Commitment, CommitmentKey, CompressedCommitment, CE,
};
use core::iter;
use ff::Field;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;
use std::sync::Arc;

/// Provides an implementation of the prover key
#[derive(Debug)]
pub struct ProverKey<E: Engine> {
  ck_s: CommitmentKey<E>,
}

/// Provides an implementation of the verifier key
#[derive(Debug, Serialize)]
#[serde(bound = "")]
pub struct VerifierKey<E: Engine> {
  ck_v: Arc<CommitmentKey<E>>,
  ck_s: CommitmentKey<E>,
}

impl<E: Engine> SimpleDigestible for VerifierKey<E> {}

/// Provides an implementation of a polynomial evaluation engine using IPA
#[derive(Clone, Debug)]
pub struct EvaluationEngine<E> {
  _p: PhantomData<E>,
}

impl<E> EvaluationEngineTrait<E> for EvaluationEngine<E>
where
  E: Engine,
  E::GE: DlogGroup,
  CommitmentKey<E>: CommitmentKeyExtTrait<E>,
{
  type ProverKey = ProverKey<E>;
  type VerifierKey = VerifierKey<E>;
  type EvaluationArgument = InnerProductArgument<E>;

  fn setup(
    ck: Arc<<<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey>,
  ) -> (Self::ProverKey, Self::VerifierKey) {
    let ck_c = E::CE::setup(b"ipa", 1);

    let pk = ProverKey { ck_s: ck_c.clone() };
    let vk = VerifierKey {
      ck_v: ck.clone(),
      ck_s: ck_c,
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
    let u = InnerProductInstance::new(comm, &EqPolynomial::evals_from_points(point), eval);
    let w = InnerProductWitness::new(poly);

    InnerProductArgument::prove(ck.clone(), pk.ck_s.clone(), &u, &w, transcript)
  }

  /// A method to verify purported evaluations of a batch of polynomials
  fn verify(
    vk: &Self::VerifierKey,
    transcript: &mut E::TE,
    comm: &Commitment<E>,
    point: &[E::Scalar],
    eval: &E::Scalar,
    arg: &Self::EvaluationArgument,
  ) -> Result<(), NovaError> {
    let u = InnerProductInstance::new(comm, &EqPolynomial::evals_from_points(point), eval);

    arg.verify(&vk.ck_v, vk.ck_s.clone(), 1 << point.len(), &u, transcript)?;

    Ok(())
  }
}

fn inner_product<T: Field + Send + Sync>(a: &[T], b: &[T]) -> T {
  zip_with!(par_iter, (a, b), |x, y| *x * y).sum()
}

/// An inner product instance consists of a commitment to a vector `a` and another vector `b`
/// and the claim that c = <a, b>.
struct InnerProductInstance<E: Engine> {
  comm_a_vec: Commitment<E>,
  b_vec: Vec<E::Scalar>,
  c: E::Scalar,
}

impl<E> InnerProductInstance<E>
where
  E: Engine,
  E::GE: DlogGroup,
{
  fn new(comm_a_vec: &Commitment<E>, b_vec: &[E::Scalar], c: &E::Scalar) -> Self {
    Self {
      comm_a_vec: *comm_a_vec,
      b_vec: b_vec.to_vec(),
      c: *c,
    }
  }
}

impl<E: Engine> TranscriptReprTrait<E::GE> for InnerProductInstance<E> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    // we do not need to include self.b_vec as in our context it is produced from the transcript
    [
      self.comm_a_vec.to_transcript_bytes(),
      self.c.to_transcript_bytes(),
    ]
    .concat()
  }
}

struct InnerProductWitness<E: Engine> {
  a_vec: Vec<E::Scalar>,
}

impl<E: Engine> InnerProductWitness<E> {
  fn new(a_vec: &[E::Scalar]) -> Self {
    Self {
      a_vec: a_vec.to_vec(),
    }
  }
}

/// An inner product argument
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct InnerProductArgument<E: Engine> {
  L_vec: Vec<CompressedCommitment<E>>,
  R_vec: Vec<CompressedCommitment<E>>,
  a_hat: E::Scalar,
}

impl<E> InnerProductArgument<E>
where
  E: Engine,
  E::GE: DlogGroup,
  CommitmentKey<E>: CommitmentKeyExtTrait<E>,
{
  const fn protocol_name() -> &'static [u8] {
    b"IPA"
  }

  fn prove(
    ck: CommitmentKey<E>,
    mut ck_c: CommitmentKey<E>,
    U: &InnerProductInstance<E>,
    W: &InnerProductWitness<E>,
    transcript: &mut E::TE,
  ) -> Result<Self, NovaError> {
    transcript.dom_sep(Self::protocol_name());

    let (ck, _) = ck.split_at(U.b_vec.len());

    if U.b_vec.len() != W.a_vec.len() {
      return Err(NovaError::InvalidInputLength);
    }

    // absorb the instance in the transcript
    transcript.absorb(b"U", U);

    // sample a random base for committing to the inner product
    let r = transcript.squeeze(b"r")?;
    ck_c.scale(&r);

    // a closure that executes a step of the recursive inner product argument
    let prove_inner = |a_vec: &[E::Scalar],
                       b_vec: &[E::Scalar],
                       ck: CommitmentKey<E>,
                       transcript: &mut E::TE|
     -> Result<
      (
        CompressedCommitment<E>,
        CompressedCommitment<E>,
        Vec<E::Scalar>,
        Vec<E::Scalar>,
        CommitmentKey<E>,
      ),
      NovaError,
    > {
      let n = a_vec.len();
      let (ck_L, ck_R) = ck.split_at(n / 2);

      let c_L = inner_product(&a_vec[0..n / 2], &b_vec[n / 2..n]);
      let c_R = inner_product(&a_vec[n / 2..n], &b_vec[0..n / 2]);

      let L = CE::<E>::commit(
        &ck_R.combine(&ck_c),
        &a_vec[0..n / 2]
          .iter()
          .chain(iter::once(&c_L))
          .copied()
          .collect::<Vec<E::Scalar>>(),
      )
      .compress();
      let R = CE::<E>::commit(
        &ck_L.combine(&ck_c),
        &a_vec[n / 2..n]
          .iter()
          .chain(iter::once(&c_R))
          .copied()
          .collect::<Vec<E::Scalar>>(),
      )
      .compress();

      transcript.absorb(b"L", &L);
      transcript.absorb(b"R", &R);

      let r = transcript.squeeze(b"r")?;
      let r_inverse = r.invert().unwrap();

      // fold the left half and the right half
      let a_vec_folded = zip_with!(
        (a_vec[0..n / 2].par_iter(), a_vec[n / 2..n].par_iter()),
        |a_L, a_R| *a_L * r + r_inverse * *a_R
      )
      .collect::<Vec<E::Scalar>>();

      let b_vec_folded = zip_with!(
        (b_vec[0..n / 2].par_iter(), b_vec[n / 2..n].par_iter()),
        |b_L, b_R| *b_L * r_inverse + r * *b_R
      )
      .collect::<Vec<E::Scalar>>();

      let ck_folded = CommitmentKeyExtTrait::fold(&ck_L, &ck_R, &r_inverse, &r);

      Ok((L, R, a_vec_folded, b_vec_folded, ck_folded))
    };

    // two vectors to hold the logarithmic number of group elements
    let mut L_vec: Vec<CompressedCommitment<E>> = Vec::new();
    let mut R_vec: Vec<CompressedCommitment<E>> = Vec::new();

    // we create mutable copies of vectors and generators
    let mut a_vec = W.a_vec.to_vec();
    let mut b_vec = U.b_vec.to_vec();
    let mut ck = ck;
    for _i in 0..usize::try_from(U.b_vec.len().ilog2()).unwrap() {
      let (L, R, a_vec_folded, b_vec_folded, ck_folded) =
        prove_inner(&a_vec, &b_vec, ck, transcript)?;
      L_vec.push(L);
      R_vec.push(R);

      a_vec = a_vec_folded;
      b_vec = b_vec_folded;
      ck = ck_folded;
    }

    Ok(Self {
      L_vec,
      R_vec,
      a_hat: a_vec[0],
    })
  }

  fn verify(
    &self,
    ck: &CommitmentKey<E>,
    mut ck_c: CommitmentKey<E>,
    n: usize,
    U: &InnerProductInstance<E>,
    transcript: &mut E::TE,
  ) -> Result<(), NovaError> {
    let (ck, _) = ck.clone().split_at(U.b_vec.len());

    transcript.dom_sep(Self::protocol_name());
    if U.b_vec.len() != n
      || n != (1 << self.L_vec.len())
      || self.L_vec.len() != self.R_vec.len()
      || self.L_vec.len() >= 32
    {
      return Err(NovaError::InvalidInputLength);
    }

    // absorb the instance in the transcript
    transcript.absorb(b"U", U);

    // sample a random base for committing to the inner product
    let r = transcript.squeeze(b"r")?;
    ck_c.scale(&r);

    let P = U.comm_a_vec + CE::<E>::commit(&ck_c, &[U.c]);

    let batch_invert = |v: &[E::Scalar]| -> Result<Vec<E::Scalar>, NovaError> {
      let mut products = vec![E::Scalar::ZERO; v.len()];
      let mut acc = E::Scalar::ONE;

      for i in 0..v.len() {
        products[i] = acc;
        acc *= v[i];
      }

      // return error if acc is zero
      acc = Option::from(acc.invert()).ok_or(NovaError::InternalError)?;

      // compute the inverse once for all entries
      let mut inv = vec![E::Scalar::ZERO; v.len()];
      for i in (0..v.len()).rev() {
        let tmp = acc * v[i];
        inv[i] = products[i] * acc;
        acc = tmp;
      }

      Ok(inv)
    };

    // compute a vector of public coins using self.L_vec and self.R_vec
    let r = (0..self.L_vec.len())
      .map(|i| {
        transcript.absorb(b"L", &self.L_vec[i]);
        transcript.absorb(b"R", &self.R_vec[i]);
        transcript.squeeze(b"r")
      })
      .collect::<Result<Vec<E::Scalar>, NovaError>>()?;

    // precompute scalars necessary for verification
    let r_square: Vec<E::Scalar> = (0..self.L_vec.len())
      .into_par_iter()
      .map(|i| r[i] * r[i])
      .collect();
    let r_inverse = batch_invert(&r)?;
    let r_inverse_square: Vec<E::Scalar> = (0..self.L_vec.len())
      .into_par_iter()
      .map(|i| r_inverse[i] * r_inverse[i])
      .collect();

    // compute the vector with the tensor structure
    let s = {
      let mut s = vec![E::Scalar::ZERO; n];
      s[0] = {
        let mut v = E::Scalar::ONE;
        for r_inverse_i in r_inverse {
          v *= r_inverse_i;
        }
        v
      };
      for i in 1..n {
        let pos_in_r = (31 - (i as u32).leading_zeros()) as usize;
        s[i] = s[i - (1 << pos_in_r)] * r_square[(self.L_vec.len() - 1) - pos_in_r];
      }
      s
    };

    let ck_hat = {
      let c = CE::<E>::commit(&ck, &s).compress();
      CommitmentKey::<E>::reinterpret_commitments_as_ck(&[c])?
    };

    let b_hat = inner_product(&U.b_vec, &s);

    let P_hat = {
      let ck_folded = {
        let ck_L = CommitmentKey::<E>::reinterpret_commitments_as_ck(&self.L_vec)?;
        let ck_R = CommitmentKey::<E>::reinterpret_commitments_as_ck(&self.R_vec)?;
        let ck_P = CommitmentKey::<E>::reinterpret_commitments_as_ck(&[P.compress()])?;
        ck_L.combine(&ck_R).combine(&ck_P)
      };

      CE::<E>::commit(
        &ck_folded,
        &r_square
          .iter()
          .chain(r_inverse_square.iter())
          .chain(iter::once(&E::Scalar::ONE))
          .copied()
          .collect::<Vec<E::Scalar>>(),
      )
    };

    if P_hat == CE::<E>::commit(&ck_hat.combine(&ck_c), &[self.a_hat, self.a_hat * b_hat]) {
      Ok(())
    } else {
      Err(NovaError::PCSError(PCSError::InvalidPCS))
    }
  }
}

#[cfg(test)]
mod test {
  use crate::provider::ipa_pc::EvaluationEngine;
  use crate::provider::util::test_utils::prove_verify_from_num_vars;
  use crate::provider::GrumpkinEngine;

  use handlebars::Handlebars;
  use serde_json::json;

  static TEMPLATE: &'static str = "
// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.16;
import \"@std/Test.sol\";
import \"src/blocks/grumpkin/Grumpkin.sol\";
import \"src/blocks/EqPolynomial.sol\";
import \"src/Utilities.sol\";
import \"src/blocks/IpaPcs.sol\";

contract IpaTest is Test {
function composeIpaInput() public pure returns (InnerProductArgument.IpaInputGrumpkin memory) {
Grumpkin.GrumpkinAffinePoint[] memory ck_v = new Grumpkin.GrumpkinAffinePoint[]({{ len ck_v }});
{{ #each ck_v }} ck_v[{{ i }}]=Grumpkin.GrumpkinAffinePoint({{ x }}, {{y}});\n {{ /each }}

Grumpkin.GrumpkinAffinePoint[] memory ck_s = new Grumpkin.GrumpkinAffinePoint[]({{ len ck_s }});
{{ #each ck_s }} ck_s[{{ i }}]=Grumpkin.GrumpkinAffinePoint({{ x }}, {{y}});\n {{ /each }}

uint256[] memory point = new uint256[]({{ len point }});
{{ #each point }} point[{{ i }}]={{ val }};\n {{ /each }}

Grumpkin.GrumpkinAffinePoint[] memory L_vec = new Grumpkin.GrumpkinAffinePoint[]({{ len L_vec }});
{{ #each L_vec }} L_vec[{{ i }}]=Grumpkin.GrumpkinAffinePoint({{ x }}, {{y}});\n {{ /each }}

Grumpkin.GrumpkinAffinePoint[] memory R_vec = new Grumpkin.GrumpkinAffinePoint[]({{ len R_vec }});
{{ #each R_vec }} R_vec[{{ i }}]=Grumpkin.GrumpkinAffinePoint({{ x }}, {{y}});\n {{ /each }}

uint256 a_hat = {{ a_hat }};

// InnerProductInstance
Grumpkin.GrumpkinAffinePoint memory commitment = Grumpkin.GrumpkinAffinePoint({{ commitment_x }}, {{ commitment_y }});

uint256 eval = {{ eval }};

return InnerProductArgument.IpaInputGrumpkin(ck_v, ck_s, point, L_vec, R_vec, commitment, eval, a_hat);
}

function testIpaGrumpkinVerification_2_Variables() public {
InnerProductArgument.IpaInputGrumpkin memory input = composeIpaInput();
assertTrue(InnerProductArgument.verifyGrumpkin(input, getTranscript()));
}

function getTranscript() public pure returns (KeccakTranscriptLib.KeccakTranscript memory) {
// b\"TestEval\" in Rust
uint8[] memory label = new uint8[](8);
label[0] = 0x54;
label[1] = 0x65;
label[2] = 0x73;
label[3] = 0x74;
label[4] = 0x45;
label[5] = 0x76;
label[6] = 0x61;
label[7] = 0x6c;

KeccakTranscriptLib.KeccakTranscript memory keccak_transcript = KeccakTranscriptLib.instantiate(label);
return keccak_transcript;
}
}
";

  #[test]
  fn test_ipa_debug() {
    //prove_verify_from_num_vars::<_, EvaluationEngine<GrumpkinEngine>>(2);

    let mut reg = Handlebars::new();
    reg
      .register_template_string("ipa.t.sol", TEMPLATE)
      .expect("can't register template");

    println!(
      "{}",
      reg
        .render(
          "ipa.t.sol",
          &json!(
            {
              "ck_v": [
                {"i": "0", "x": "0x15afa1c1de43e186ee615ee76389d1ca9de572d426869ab062a03f1ba65808a2", "y": "0x28d6d43cb5ba89778111ceaa56cb8bf2c34a5fb6013988513d5798a60846d423"},
                {"i": "1", "x": "0x132126b357d7299c5c18e04cbe13c4206b763dbc56a8d19900270cd0c59f3981", "y": "0x169077205c0ed8e9f2738a9f04d064e17c457a531a93e9ec5131e35d587cd381"},
                {"i": "2", "x": "0x20c9d6e3d55f0142ce09b6d1cd8b86c8eaecf8f204bce4c9b88a75c720e34b74", "y": "0x227f66a87a7649e8a76a2314e14c0c44877e1eca54015d5ecd8b1da08ccbb779"},
                {"i": "3", "x": "0x1300fe5112d72be0b65d1d365f294a136df15671e4f56e2fbf65be2ffec64e4f", "y": "0x0c93e3b91eeead0adf19f228e2a361b3b6055d1b89e699196c6a5550be5824b9"},
              ],
              "ck_s": [
                {"i": "0", "x": "0x2e8facd7beb3da0e505fa1e33ee77b0b19fa1dfc1c5e04537cda07bf56cc248b", "y": "0x11a32df7bf180b18e526371ee2e21bb42ee2d9a7ac875f0816be6effda4e3dfb"},
              ],
              "point": [
                {"i": "0", "val": "0x1fe29a0b699fa3cbc723126c4ad0e4a5f410c5f699f3599e92c4f0e99c1abd97"},
                {"i": "1", "val": "0x0ed4861fc966ff194c23744c2e6f63139211dc3550a28a9c8e0979427ff9c677"},
              ],
              "L_vec": [
                {"i": "0", "x": "0x1aedd46eb53cfded07f7c3710015340b8cb21983fe71d24f0e7d9f5ab4854e2d", "y": "0x06d42154bbf58e193faa5443312aa938c3fc88648f1a0912d890ea1f7edc3ade"},
                {"i": "1", "x": "0x1c95cbc06044e13eca63f164a8d2dbd3bfc7ed470dd244154e2ae5f83592b649", "y": "0x0abde1d3428cfe8b21442f486b010f14042f5d84b54a811d06307104c4755a2c"},
              ],
              "R_vec": [
                {"i": "0", "x": "0x2f1727ea1ac3c3862caa797261db6a9b0714f7d8e65adb97e5f4da457044ccfe", "y": "0x185e59b83d3e903a804f6dcfd68a3e34b5cb9d048aca562e7e89c77b5c7db13e"},
                {"i": "1", "x": "0x08adac48b78bbb3435da3efc7162332b5693f5db927e184c0d1faaeaaf60fdbd", "y": "0x1770ed9ec1f5ed7815a86ec6a5acc1b66d6c89d9bbbb53a2663ce292f7fe48b0"},
              ],
              "a_hat": "0x144237bc694bfa4f625dab1f8bfc854e3e7b9a612027e16bcd840383d088e190",
              "commitment_x": "0x1e7268591a2b38be3ff689fe1eb31600f9161a2163a08ee9842d458ac0bddf05",
              "commitment_y": "0x1f3070c0592c3f0135e1aba5100d43785490023f9536025b119bf9c0f96d5281",
              "eval": "0x2514662a7e8e9a7a4ab7ea7c8e6a3423e7a47fca5105e6f3264d20d88e6d33bf",
            }
          )
        )
        .expect("can't render")
    );
  }

  #[test]
  fn test_multiple_polynomial_size() {
    for num_vars in [4, 5, 6] {
      prove_verify_from_num_vars::<_, EvaluationEngine<GrumpkinEngine>>(num_vars);
    }
  }
}
