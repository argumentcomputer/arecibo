//! TODO: Doc

use std::marker::PhantomData;

use ff::Field;
use serde::{Deserialize, Serialize};

use super::{
  compute_eval_table_sparse,
  polys::{eq::EqPolynomial, multilinear::MultilinearPolynomial},
};
use crate::errors::NovaError;
use crate::r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::spartan::powers;
use crate::spartan::sumcheck::SumcheckProof;
use crate::traits::{
  evaluation::EvaluationEngineTrait,
  snark::{BatchedRelaxedR1CSSNARKTrait, DigestHelperTrait},
  Group, TranscriptEngineTrait,
};
use crate::CommitmentKey;

use super::snark::RelaxedR1CSSNARK;

/// TODO: Doc
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<G: Group, EE: EvaluationEngineTrait<G>> {
  vk_digest: G::Scalar,
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
    ck: &CommitmentKey<G>,
    S: &[R1CSShape<G>],
  ) -> Result<(Self::ProverKey, Self::VerifierKey), NovaError> {
    todo!()
  }

  fn prove(
    ck: &CommitmentKey<G>,
    pk: &Self::ProverKey,
    S: &[R1CSShape<G>],
    U: &[RelaxedR1CSInstance<G>],
    W: &[RelaxedR1CSWitness<G>],
  ) -> Result<Self, NovaError> {
    let S = S
      .iter()
      .map(|s| {
        let s = s.pad();
        assert!(s.is_regular_shape());
        s
      })
      .collect::<Vec<_>>();

    let W = W.iter().zip(S).map(|(w, s)| w.pad(&s)).collect::<Vec<_>>();

    let mut transcript = G::TE::new(b"BatchedRelaxedR1CSSNARK");

    transcript.absorb(b"vk", &pk.vk_digest);
    U.iter().for_each(|u| {
      transcript.absorb(b"U", u);
    });

    let mut z = W
      .iter()
      .zip(U)
      .map(|(w, u)| [w.W.clone(), vec![u.u], u.X.clone()].concat())
      .collect::<Vec<Vec<_>>>();

    let num_rounds_x = S
      .iter()
      .map(|s| usize::try_from(s.num_cons.ilog2()).unwrap())
      .max()
      .unwrap();

    let num_rounds_y = S
      .iter()
      .map(|s| usize::try_from(s.num_vars.ilog2() + 1).unwrap())
      .max()
      .unwrap();

    let tau = (0..num_rounds_x)
      .map(|_| transcript.squeeze(b"t"))
      .collect::<Result<Vec<_>, NovaError>>()?;

    let mut poly_tau = MultilinearPolynomial::new(EqPolynomial::new(tau).evals());

    let (mut vec_poly_Az, mut vec_poly_Bz, mut vec_poly_Cz, mut vec_poly_uCz_E) = {
      let (vec_poly_Az, vec_poly_Bz, vec_poly_Cz) = S.iter().zip(z).fold(
        (vec![], vec![], vec![]),
        |(mut vec_A, mut vec_B, mut vec_C), (s, z)| {
          let (poly_Az, poly_Bz, poly_Cz) = s.multiply_vec(&z).unwrap();
          vec_A.push(poly_Az);
          vec_B.push(poly_Bz);
          vec_C.push(poly_Cz);
          (vec_A, vec_B, vec_C)
        },
      );

      let vec_poly_uCz_E = S
        .iter()
        .zip(U)
        .zip(W)
        .zip(vec_poly_Cz)
        .map(|(((s, u), w), poly_Cz)| {
          (0..s.num_cons)
            .map(|i| u.u * poly_Cz[i] + w.E[i])
            .collect::<Vec<G::Scalar>>()
        })
        .collect::<Vec<_>>();

      (
        vec_poly_Az
          .iter()
          .map(|poly_Az| MultilinearPolynomial::new(poly_Az.clone()))
          .collect::<Vec<_>>(),
        vec_poly_Bz
          .iter()
          .map(|poly_Bz| MultilinearPolynomial::new(poly_Bz.clone()))
          .collect::<Vec<_>>(),
        vec_poly_Cz
          .iter()
          .map(|poly_Cz| MultilinearPolynomial::new(poly_Cz.clone()))
          .collect::<Vec<_>>(),
        vec_poly_uCz_E
          .iter()
          .map(|poly_uCz_E| MultilinearPolynomial::new(poly_uCz_E.clone()))
          .collect::<Vec<_>>(),
      )
    };

    let comb_func_outer =
      |poly_A_comp: &G::Scalar,
       poly_B_comp: &G::Scalar,
       poly_C_comp: &G::Scalar,
       poly_D_comp: &G::Scalar|
       -> G::Scalar { *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp) };

    // TODO: Figure out what, if anything, I should absorb now to generate this

    let outer_r = transcript.squeeze(b"out_r")?;

    let coeffs = powers::<G>(&outer_r, S.len());

    let (sc_proof_outer, r_x, claim_tau, claims_outer): (
      SumcheckProof<G>,
      Vec<G::Scalar>,
      G::Scalar,
      Vec<_>,
    ) = SumcheckProof::prove_cubic_with_additive_term_batch(
      &G::Scalar::ZERO,
      num_rounds_x,
      &mut poly_tau,
      &mut vec_poly_Az,
      &mut vec_poly_Bz,
      &mut vec_poly_uCz_E,
      &coeffs,
      comb_func_outer,
      &mut transcript,
    )?;

    let (claims_Az, claims_Bz, claims_Cz) = (
      claims_outer[0],
      claims_outer[1],
      vec_poly_Cz
        .iter()
        .map(|poly| poly.evaluate(&r_x))
        .collect::<Vec<_>>(),
    );

    let evals_E = W
      .iter()
      .map(|w| MultilinearPolynomial::new(w.E.clone()).evaluate(&r_x))
      .collect::<Vec<_>>();

    claims_Az
      .into_iter()
      .zip(claims_Bz)
      .zip(claims_Cz)
      .zip(evals_E)
      .for_each(|(((claim_Az, claim_Bz), claim_Cz), eval_E)| {
        transcript.absorb(
          b"claims_outer",
          &[claim_Az, claim_Bz, claim_Cz, eval_E].as_slice(),
        )
      });

    let inner_r = transcript.squeeze(b"in_r")?;

    let inner_r_cube = inner_r * inner_r * inner_r;

    let inner_r_powers = powers::<G>(&inner_r_cube, S.len());

    let claim_inner_joint = inner_r_powers
      .into_iter()
      .zip(claims_Az)
      .zip(claims_Bz)
      .zip(claims_Cz)
      .fold(
        G::Scalar::ZERO,
        |acc, (((r_i, claim_Az), claim_Bz), claim_Cz)| {
          acc + r_i * (claim_Az + inner_r * claim_Bz + inner_r * inner_r * claim_Cz)
        },
      );

    let mut poly_ABCs = {
      let evals_rx = EqPolynomial::new(r_x).evals();

      let (evals_As, evals_Bs, evals_Cs) = S.iter().fold(
        (vec![], vec![], vec![]),
        |(mut acc_A, mut acc_B, mut acc_C), s| {
          let (evals_A, evals_B, evals_C) = compute_eval_table_sparse(s, &evals_rx); // TODO: Truncate
          acc_A.push(evals_A);
          acc_B.push(evals_B);
          acc_C.push(evals_C);
          (acc_A, acc_B, acc_C)
        },
      );

      let inner = |M_evals_As: &[G::Scalar],
                   M_evals_Bs: &[G::Scalar],
                   M_evals_Cs: &[G::Scalar]|
       -> Vec<G::Scalar> {
        M_evals_As
          .into_iter()
          .zip(M_evals_Bs)
          .zip(M_evals_Cs)
          .map(|((eval_A, eval_B), eval_C)| {
            *eval_A + inner_r * *eval_B + inner_r * inner_r * *eval_C
          })
          .collect::<Vec<_>>()
      };

      evals_As
        .iter()
        .zip(evals_Bs)
        .zip(evals_Cs)
        .map(|((eval_A, eval_B), eval_C)| {
          MultilinearPolynomial::new(inner(&eval_A, &eval_B, &eval_C))
        })
        .collect::<Vec<_>>()
    };

    let mut poly_zs = z
      .into_iter()
      .zip(S)
      .map(|(mut z, s)| {
        z.resize(2 * s.num_vars, G::Scalar::ZERO);
        MultilinearPolynomial::new(z)
      })
      .collect::<Vec<_>>();

    let comb_func = |poly_A_comp: &G::Scalar, poly_B_comp: &G::Scalar| -> G::Scalar {
      *poly_A_comp * *poly_B_comp
    };

    let (_sc_proof_inner, _r_y, _claims_inner): (
      SumcheckProof<G>,
      Vec<G::Scalar>,
      (Vec<_>, Vec<_>),
    ) = SumcheckProof::prove_quad_batch(
      &claim_inner_joint,
      num_rounds_y,
      &mut poly_ABCs,
      &mut poly_zs,
      &coeffs,
      comb_func,
      &mut transcript,
    )?;
    todo!()
  }

  fn verify(&self, vk: &Self::VerifierKey, U: &[RelaxedR1CSInstance<G>]) -> Result<(), NovaError> {
    todo!()
  }
}
