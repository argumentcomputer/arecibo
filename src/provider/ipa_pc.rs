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
  use crate::provider::util::solidity_compatibility_utils::{
    ec_points_to_json, field_elements_to_json, generate_pcs_solidity_unit_test_data,
  };
  use crate::provider::util::test_utils::prove_verify_from_num_vars;

  use crate::provider::GrumpkinEngine;
  use group::Curve;

  use crate::provider::pedersen::{CommitmentKey, CommitmentKeyExtTrait};
  use handlebars::Handlebars;
  use serde_json::json;
  use serde_json::{Map, Value};

  static IPA_COMPATIBILITY_UNIT_TESTING_TEMPLATE: &str = "
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

function testIpaGrumpkinVerification_{{ num_vars }}_Variables() public {
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

  // To generate Solidity unit-test:
  // cargo test test_solidity_compatibility_ipa --release -- --ignored --nocapture > ipa.t.sol
  #[test]
  #[ignore]
  fn test_solidity_compatibility_ipa() {
    let num_vars = 2;

    // Secondary part of verification is IPA over Grumpkin
    let (commitment, point, eval, proof, vk) =
      generate_pcs_solidity_unit_test_data::<_, EvaluationEngine<GrumpkinEngine>>(num_vars);

    let num_vars_string = format!("{}", num_vars);
    let eval_string = format!("{:?}", eval);
    let commitment_x_string = format!("{:?}", commitment.comm.to_affine().x);
    let commitment_y_string = format!("{:?}", commitment.comm.to_affine().y);
    let proof_a_hat_string = format!("{:?}", proof.a_hat);

    let r_vec = CommitmentKey::<GrumpkinEngine>::reinterpret_commitments_as_ck(&proof.R_vec)
      .expect("can't reinterpred R_vec");
    let l_vec = CommitmentKey::<GrumpkinEngine>::reinterpret_commitments_as_ck(&proof.L_vec)
      .expect("can't reinterpred L_vec");

    let r_vec_array = ec_points_to_json::<GrumpkinEngine>(&r_vec.ck);
    let l_vec_array = ec_points_to_json::<GrumpkinEngine>(&l_vec.ck);
    let point_array = field_elements_to_json::<GrumpkinEngine>(&point);
    let ckv_array = ec_points_to_json::<GrumpkinEngine>(&vk.ck_v.ck);
    let cks_array = ec_points_to_json::<GrumpkinEngine>(&vk.ck_s.ck);

    let mut map = Map::new();
    map.insert("num_vars".to_string(), Value::String(num_vars_string));
    map.insert("eval".to_string(), Value::String(eval_string));
    map.insert(
      "commitment_x".to_string(),
      Value::String(commitment_x_string),
    );
    map.insert(
      "commitment_y".to_string(),
      Value::String(commitment_y_string),
    );
    map.insert("R_vec".to_string(), Value::Array(r_vec_array));
    map.insert("L_vec".to_string(), Value::Array(l_vec_array));
    map.insert("a_hat".to_string(), Value::String(proof_a_hat_string));
    map.insert("point".to_string(), Value::Array(point_array));
    map.insert("ck_v".to_string(), Value::Array(ckv_array));
    map.insert("ck_s".to_string(), Value::Array(cks_array));

    let mut reg = Handlebars::new();
    reg
      .register_template_string("ipa.t.sol", IPA_COMPATIBILITY_UNIT_TESTING_TEMPLATE)
      .expect("can't register template");

    let solidity_unit_test_source = reg.render("ipa.t.sol", &json!(map)).expect("can't render");
    println!("{}", solidity_unit_test_source);
  }

  #[test]
  fn test_multiple_polynomial_size() {
    for num_vars in [4, 5, 6] {
      prove_verify_from_num_vars::<_, EvaluationEngine<GrumpkinEngine>>(num_vars);
    }
  }
}
