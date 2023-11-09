//! TODO: Doc

use std::marker::PhantomData;

use ff::Field;
use serde::{Deserialize, Serialize};

use super::{
  compute_eval_table_sparse,
  math::Math,
  polys::{eq::EqPolynomial, multilinear::MultilinearPolynomial},
  powers,
  snark::batch_eval_prove,
  sumcheck::SumcheckProof,
  PolyEvalInstance, PolyEvalWitness,
};
use crate::errors::NovaError;
use crate::r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::traits::{
  evaluation::EvaluationEngineTrait,
  snark::{BatchedRelaxedR1CSSNARKTrait, DigestHelperTrait},
  Group, TranscriptEngineTrait,
};
use crate::CommitmentKey;

///TODO: Doc
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct BatchedRelaxedR1CSSNARK<G: Group, EE: EvaluationEngineTrait<G>> {
  sc_proof_outer: SumcheckProof<G>,
  claims_outer: (Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>),
  evals_E: Vec<G::Scalar>,
  sc_proof_inner: SumcheckProof<G>,
  evals_W: Vec<G::Scalar>,
  sc_proof_batch: SumcheckProof<G>,
  evals_batch: Vec<G::Scalar>,
  eval_arg: EE::EvaluationArgument,
}

/// TODO: Doc
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<G: Group, EE: EvaluationEngineTrait<G>> {
  pk_ee: EE::ProverKey,
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
  for BatchedRelaxedR1CSSNARK<G, EE>
{
  type ProverKey = ProverKey<G, EE>;

  type VerifierKey = VerifierKey<G, EE>;

  fn setup(
    _ck: &CommitmentKey<G>,
    _S: &[R1CSShape<G>],
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
    // Pad shapes and ensure their sizes are correct
    let S = S
      .iter()
      .map(|s| {
        let s = s.pad();
        if s.is_regular_shape() {
          Ok(s)
        } else {
          Err(NovaError::InternalError)
        }
      })
      .collect::<Result<Vec<_>, _>>()?;

    // Pad (W,E) for each instance
    let W = W
      .iter()
      .zip(S.iter())
      .map(|(w, s)| w.pad(s))
      .collect::<Vec<RelaxedR1CSWitness<G>>>();

    let mut transcript = G::TE::new(b"BatchedRelaxedR1CSSNARK");

    transcript.absorb(b"vk", &pk.vk_digest);
    U.iter().for_each(|u| {
      transcript.absorb(b"U", u);
    });

    let (W_polys, E_polys): (Vec<_>, Vec<_>) = W
      .into_iter()
      .map(|w| {
        (
          MultilinearPolynomial::new(w.W),
          MultilinearPolynomial::new(w.E),
        )
      })
      .unzip();

    // Append public inputs to W: Z = [W, u, X]
    let z = W_polys
      .iter()
      .zip(U.iter())
      .map(|(w, u)| [w.Z.clone(), vec![u.u], u.X.clone()].concat())
      .collect::<Vec<Vec<_>>>();

    let num_rounds_x = S.iter().map(|s| s.num_cons.log_2()).max().unwrap();
    let num_rounds_y = S.iter().map(|s| s.num_vars.log_2() + 1).max().unwrap();

    // Generate tau polynomial corresponding to eq(τ, τ², τ⁴ , …)
    // for a random challenge τ
    let mut poly_tau = {
      let mut tau = transcript.squeeze(b"t")?;

      // The MLE of eq(τ, τ², τ⁴ , …) is a polynomial whose evaluations are
      // (1, τ, τ², τ³, …)
      let tau_vars = (0..num_rounds_x)
        .map(|_| {
          let t = tau;
          tau = tau.square();
          t
        })
        .collect::<Vec<_>>();

      Ok(MultilinearPolynomial::new(
        EqPolynomial::new(tau_vars).evals(),
      ))
    }?;

    // Compute MLEs of Az, Bz, Cz, uCz + E
    let (mut vec_poly_Az, mut vec_poly_Bz, vec_poly_Cz, mut vec_poly_uCz_E) = {
      let (vec_poly_Az, vec_poly_Bz, vec_poly_Cz) = S.iter().zip(z.iter()).fold(
        (vec![], vec![], vec![]),
        |(mut vec_A, mut vec_B, mut vec_C), (s, z)| {
          let (poly_Az, poly_Bz, poly_Cz) = s.multiply_vec(z).unwrap();
          vec_A.push(poly_Az);
          vec_B.push(poly_Bz);
          vec_C.push(poly_Cz);
          (vec_A, vec_B, vec_C)
        },
      );

      let vec_poly_uCz_E = S
        .iter()
        .zip(U.iter())
        .zip(E_polys.iter())
        .zip(vec_poly_Cz.iter())
        .map(|(((s, u), e), poly_Cz)| {
          (0..s.num_cons)
            .map(|i| u.u * poly_Cz[i] + e[i])
            .collect::<Vec<G::Scalar>>()
        })
        .collect::<Vec<_>>();

      (
        vec_poly_Az
          .into_iter()
          .map(MultilinearPolynomial::new)
          .collect::<Vec<_>>(),
        vec_poly_Bz
          .into_iter()
          .map(MultilinearPolynomial::new)
          .collect::<Vec<_>>(),
        vec_poly_Cz
          .into_iter()
          .map(MultilinearPolynomial::new)
          .collect::<Vec<_>>(),
        vec_poly_uCz_E
          .into_iter()
          .map(MultilinearPolynomial::new)
          .collect::<Vec<_>>(),
      )
    };

    let comb_func_outer =
      |poly_A_comp: &G::Scalar,
       poly_B_comp: &G::Scalar,
       poly_C_comp: &G::Scalar,
       poly_D_comp: &G::Scalar|
       -> G::Scalar { *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp) };

    // Sample challenge for random linear-combination of outer claims
    let outer_r = transcript.squeeze(b"out_r")?;
    let coeffs = powers::<G>(&outer_r, S.len());

    // Verify outer sumcheck: Az * Bz * Cz - uCz_E for each instance
    let (sc_proof_outer, r_x, _claim_tau, claims_outer): (
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

    // Extract evaluations of Az, Bz from Sumcheck and E at r_x
    let (claims_Az, claims_Bz, claims_Cz) = (
      claims_outer[0].clone(),
      claims_outer[1].clone(),
      vec_poly_Cz
        .iter()
        .map(|poly| poly.evaluate(&r_x))
        .collect::<Vec<_>>(),
    );

    let evals_E = E_polys
      .iter()
      .map(|e| e.evaluate(&r_x)) // TODO: evaluate without clone
      .collect::<Vec<_>>();

    claims_Az
      .iter()
      .zip(claims_Bz.iter())
      .zip(claims_Cz.iter())
      .zip(evals_E.iter())
      .for_each(|(((&claim_Az, &claim_Bz), &claim_Cz), &eval_E)| {
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
      .zip(claims_Az.iter())
      .zip(claims_Bz.iter())
      .zip(claims_Cz.iter())
      .fold(
        G::Scalar::ZERO,
        |acc, (((r_i, claim_Az), claim_Bz), claim_Cz)| {
          acc + r_i * (*claim_Az + inner_r * claim_Bz + inner_r * inner_r * claim_Cz)
        },
      );

    let mut poly_ABCs = {
      let evals_rx = EqPolynomial::new(r_x.clone()).evals();

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

      let inner = |M_evals_As: Vec<G::Scalar>,
                   M_evals_Bs: Vec<G::Scalar>,
                   M_evals_Cs: Vec<G::Scalar>|
       -> Vec<G::Scalar> {
        M_evals_As
          .into_iter()
          .zip(M_evals_Bs)
          .zip(M_evals_Cs)
          .map(|((eval_A, eval_B), eval_C)| eval_A + inner_r * eval_B + inner_r * inner_r * eval_C)
          .collect::<Vec<_>>()
      };

      evals_As
        .into_iter()
        .zip(evals_Bs)
        .zip(evals_Cs)
        .map(|((eval_A, eval_B), eval_C)| MultilinearPolynomial::new(inner(eval_A, eval_B, eval_C)))
        .collect::<Vec<_>>()
    };

    let mut poly_zs = z
      .into_iter()
      .zip(S.iter())
      .map(|(mut z, s)| {
        z.resize(2 * s.num_vars, G::Scalar::ZERO);
        MultilinearPolynomial::new(z)
      })
      .collect::<Vec<_>>();

    let comb_func = |poly_A_comp: &G::Scalar, poly_B_comp: &G::Scalar| -> G::Scalar {
      *poly_A_comp * *poly_B_comp
    };

    let (sc_proof_inner, r_y, _claims_inner): (SumcheckProof<G>, Vec<G::Scalar>, (Vec<_>, Vec<_>)) =
      SumcheckProof::prove_quad_batch(
        &claim_inner_joint,
        num_rounds_y,
        &mut poly_ABCs,
        &mut poly_zs,
        &coeffs,
        comb_func,
        &mut transcript,
      )?;

    let evals_W = W_polys
      .iter()
      .map(|w| w.evaluate(&r_y[1..]))
      .collect::<Vec<_>>();

    let mut w_vec = Vec::with_capacity(2 * S.len());
    let mut u_vec = Vec::with_capacity(2 * S.len());

    w_vec.extend(
      W_polys
        .into_iter()
        .map(|poly| PolyEvalWitness { p: poly.Z }),
    );
    u_vec.extend(
      evals_W
        .iter()
        .zip(U.iter())
        .map(|(eval, u)| PolyEvalInstance {
          c: u.comm_W,
          x: r_x[1..].to_vec(),
          e: *eval,
        }),
    );

    w_vec.extend(
      E_polys
        .into_iter()
        .map(|poly| PolyEvalWitness { p: poly.Z }),
    );
    u_vec.extend(
      evals_E
        .iter()
        .zip(U.iter())
        .map(|(eval, u)| PolyEvalInstance {
          c: u.comm_W,
          x: r_x[1..].to_vec(),
          e: *eval,
        }),
    );

    let (batched_u, batched_w, sc_proof_batch, claims_batch_left) =
      batch_eval_prove(u_vec, w_vec, &mut transcript)?;

    let eval_arg = EE::prove(
      ck,
      &pk.pk_ee,
      &mut transcript,
      &batched_u.c,
      &batched_w.p,
      &batched_u.x,
      &batched_u.e,
    )?;

    Ok(BatchedRelaxedR1CSSNARK {
      sc_proof_outer,
      claims_outer: (claims_Az, claims_Bz, claims_Cz),
      evals_E,
      sc_proof_inner,
      evals_W,
      sc_proof_batch,
      evals_batch: claims_batch_left,
      eval_arg,
    })
  }

  fn verify(
    &self,
    _vk: &Self::VerifierKey,
    _U: &[RelaxedR1CSInstance<G>],
  ) -> Result<(), NovaError> {
    todo!()
  }
}
