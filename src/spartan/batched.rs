//! This module implements `BatchedRelaxedR1CSSNARKTrait` using Spartan that is generic over the polynomial commitment
//! and evaluation argument (i.e., a PCS) This version of Spartan does not use preprocessing so the verifier keeps the
//! entire description of R1CS matrices. This is essentially optimal for the verifier when using an IPA-based polynomial
//! commitment scheme. This batched implementation batches the outer and inner sumchecks of the Spartan SNARK.

use ff::Field;
use serde::{Deserialize, Serialize};

use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use itertools::Itertools;
use once_cell::sync::OnceCell;
use rayon::prelude::*;

use super::{
  compute_eval_table_sparse,
  math::Math,
  polys::{eq::EqPolynomial, multilinear::MultilinearPolynomial},
  powers,
  snark::batch_eval_prove,
  sumcheck::SumcheckProof,
  PolyEvalInstance, PolyEvalWitness,
};

use crate::{
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness, SparseMatrix},
  spartan::{
    polys::{multilinear::SparsePolynomial, power::PowPolynomial},
    snark::batch_eval_verify,
  },
  traits::{
    evaluation::EvaluationEngineTrait,
    snark::{BatchedRelaxedR1CSSNARKTrait, DigestHelperTrait},
    Group, TranscriptEngineTrait,
  },
  CommitmentKey,
};

/// A succinct proof of knowledge of a witness to a batch of relaxed R1CS instances
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct BatchedRelaxedR1CSSNARK<G: Group, EE: EvaluationEngineTrait<G>> {
  sc_proof_outer: SumcheckProof<G>,
  // Claims ([Azᵢ(τᵢ), ])
  claims_outer: (Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>),
  evals_E: Vec<G::Scalar>,
  sc_proof_inner: SumcheckProof<G>,
  evals_W: Vec<G::Scalar>,
  sc_proof_batch: SumcheckProof<G>,
  evals_batch: Vec<G::Scalar>,
  eval_arg: EE::EvaluationArgument,
}

/// A type that represents the prover's key
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<G: Group, EE: EvaluationEngineTrait<G>> {
  pk_ee: EE::ProverKey,
  vk_digest: G::Scalar,
}

/// A type that represents the verifier's key
#[derive(Clone, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(where <G::Scalar as ff::PrimeField>::Repr: Abomonation)]
pub struct VerifierKey<G: Group, EE: EvaluationEngineTrait<G>> {
  vk_ee: EE::VerifierKey,
  S: Vec<R1CSShape<G>>,
  #[abomonation_skip]
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<G::Scalar>,
}

impl<G: Group, EE: EvaluationEngineTrait<G>> VerifierKey<G, EE> {
  fn new(shapes: Vec<R1CSShape<G>>, vk_ee: EE::VerifierKey) -> Self {
    VerifierKey {
      vk_ee,
      S: shapes,
      digest: OnceCell::new(),
    }
  }
}

impl<G: Group, EE: EvaluationEngineTrait<G>> SimpleDigestible for VerifierKey<G, EE> {}

impl<G: Group, EE: EvaluationEngineTrait<G>> DigestHelperTrait<G> for VerifierKey<G, EE> {
  /// Returns the digest of the verifier's key.
  fn digest(&self) -> G::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc = DigestComputer::<G::Scalar, _>::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure to retrieve digest!")
  }
}

impl<G: Group, EE: EvaluationEngineTrait<G>> BatchedRelaxedR1CSSNARKTrait<G>
  for BatchedRelaxedR1CSSNARK<G, EE>
{
  type ProverKey = ProverKey<G, EE>;

  type VerifierKey = VerifierKey<G, EE>;

  fn setup(
    ck: &CommitmentKey<G>,
    S: &[R1CSShape<G>],
  ) -> Result<(Self::ProverKey, Self::VerifierKey), NovaError> {
    let (pk_ee, vk_ee) = EE::setup(ck);

    let S = S.iter().map(|s| s.pad()).collect();

    let vk = VerifierKey::new(S, vk_ee);

    let pk = ProverKey {
      pk_ee,
      vk_digest: vk.digest(),
    };

    Ok((pk, vk))
  }

  fn prove(
    ck: &CommitmentKey<G>,
    pk: &Self::ProverKey,
    S: &[R1CSShape<G>],
    U: &[RelaxedR1CSInstance<G>],
    W: &[RelaxedR1CSWitness<G>],
  ) -> Result<Self, NovaError> {
    let num_instances = U.len();
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

    let (polys_W, polys_E): (Vec<_>, Vec<_>) = W.into_iter().map(|w| (w.W, w.E)).unzip();

    // Append public inputs to W: Z = [W, u, X]
    let polys_Z = polys_W
      .iter()
      .zip(U.iter())
      .map(|(w, u)| [w.clone(), vec![u.u], u.X.clone()].concat())
      .collect::<Vec<Vec<_>>>();

    let (num_rounds_x, num_rounds_y): (Vec<_>, Vec<_>) = S
      .iter()
      .map(|s| (s.num_cons.log_2(), s.num_vars.log_2() + 1))
      .unzip();
    let num_rounds_x_max = *num_rounds_x.iter().max().unwrap();
    let num_rounds_y_max = *num_rounds_y.iter().max().unwrap();

    // Generate tau polynomial corresponding to eq(τ, τ², τ⁴ , …)
    // for a random challenge τ
    let tau = transcript.squeeze(b"t")?;
    let polys_tau = num_rounds_x
      .iter()
      .map(|&num_rounds_x| PowPolynomial::new(&tau, num_rounds_x).evals())
      .map(MultilinearPolynomial::new)
      .collect::<Vec<_>>();

    // Compute MLEs of Az, Bz, Cz, uCz + E
    let (polys_Az, polys_Bz, polys_Cz): (Vec<_>, Vec<_>, Vec<_>) = S
      .par_iter()
      .zip(polys_Z.par_iter())
      .map(|(s, poly_Z)| {
        let (poly_Az, poly_Bz, poly_Cz) = s.multiply_vec(poly_Z)?;
        Ok((poly_Az, poly_Bz, poly_Cz))
      })
      .collect::<Result<Vec<_>, NovaError>>()?
      .into_iter()
      .multiunzip();

    let polys_uCz_E = U
      .par_iter()
      .zip(polys_E.par_iter())
      .zip(polys_Cz.par_iter())
      .map(|((u, poly_E), poly_Cz)| {
        poly_Cz
          .par_iter()
          .zip(poly_E.par_iter())
          .map(|(cz, e)| u.u * cz + e)
          .collect::<Vec<G::Scalar>>()
      })
      .collect::<Vec<_>>();

    let comb_func_outer =
      |poly_A_comp: &G::Scalar,
       poly_B_comp: &G::Scalar,
       poly_C_comp: &G::Scalar,
       poly_D_comp: &G::Scalar|
       -> G::Scalar { *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp) };

    // Sample challenge for random linear-combination of outer claims
    let outer_r = transcript.squeeze(b"out_r")?;
    let outer_r_powers = powers::<G>(&outer_r, num_instances);

    // Verify outer sumcheck: Az * Bz - uCz_E for each instance
    let (sc_proof_outer, r_x, claims_outer) = SumcheckProof::prove_cubic_with_additive_term_batch(
      &vec![G::Scalar::ZERO; num_instances],
      &num_rounds_x,
      polys_tau,
      polys_Az
        .into_iter()
        .map(MultilinearPolynomial::new)
        .collect(),
      polys_Bz
        .into_iter()
        .map(MultilinearPolynomial::new)
        .collect(),
      polys_uCz_E
        .into_iter()
        .map(MultilinearPolynomial::new)
        .collect(),
      &outer_r_powers,
      comb_func_outer,
      &mut transcript,
    )?;

    let r_x = num_rounds_x
      .iter()
      .map(|&num_rounds| r_x[(num_rounds_x_max - num_rounds)..].to_vec())
      .collect::<Vec<_>>();

    // Extract evaluations of Az, Bz from Sumcheck and Cz, E at r_x
    let (evals_Az_Bz_Cz, evals_E): (Vec<_>, Vec<_>) = claims_outer[1]
      .par_iter()
      .zip(claims_outer[2].par_iter())
      .zip(polys_Cz.par_iter())
      .zip(polys_E.par_iter())
      .zip(r_x.par_iter())
      .map(|((((&eval_Az, &eval_Bz), poly_Cz), poly_E), r_x)| {
        let (eval_Cz, eval_E) = rayon::join(
          || MultilinearPolynomial::evaluate_with(poly_Cz, r_x),
          || MultilinearPolynomial::evaluate_with(poly_E, r_x),
        );
        ((eval_Az, eval_Bz, eval_Cz), eval_E)
      })
      .unzip();

    evals_Az_Bz_Cz.iter().zip(evals_E.iter()).for_each(
      |(&(eval_Az, eval_Bz, eval_Cz), &eval_E)| {
        transcript.absorb(
          b"claims_outer",
          &[eval_Az, eval_Bz, eval_Cz, eval_E].as_slice(),
        )
      },
    );

    let inner_r = transcript.squeeze(b"in_r")?;
    let inner_r_square = inner_r.square();
    let inner_r_cube = inner_r_square * inner_r;
    let inner_r_powers = powers::<G>(&inner_r_cube, num_instances);

    let claims_inner_joint = evals_Az_Bz_Cz
      .iter()
      .map(|(eval_Az, eval_Bz, eval_Cz)| *eval_Az + inner_r * eval_Bz + inner_r_square * eval_Cz)
      .collect::<Vec<_>>();

    let polys_ABCs = {
      let inner = |M_evals_As: Vec<G::Scalar>,
                   M_evals_Bs: Vec<G::Scalar>,
                   M_evals_Cs: Vec<G::Scalar>|
       -> Vec<G::Scalar> {
        M_evals_As
          .into_par_iter()
          .zip(M_evals_Bs.into_par_iter())
          .zip(M_evals_Cs.into_par_iter())
          .map(|((eval_A, eval_B), eval_C)| eval_A + inner_r * eval_B + inner_r_square * eval_C)
          .collect::<Vec<_>>()
      };

      S.par_iter()
        .zip(r_x.par_iter())
        .map(|(s, r_x)| {
          let evals_rx = EqPolynomial::new(r_x.clone()).evals();
          let (eval_A, eval_B, eval_C) = compute_eval_table_sparse(s, &evals_rx);
          MultilinearPolynomial::new(inner(eval_A, eval_B, eval_C))
        })
        .collect::<Vec<_>>()
    };

    let polys_Z = polys_Z
      .into_iter()
      .zip(num_rounds_y.iter())
      .map(|(mut z, &num_rounds_y)| {
        z.resize(1 << num_rounds_y, G::Scalar::ZERO);
        MultilinearPolynomial::new(z)
      })
      .collect::<Vec<_>>();

    let comb_func = |poly_A_comp: &G::Scalar, poly_B_comp: &G::Scalar| -> G::Scalar {
      *poly_A_comp * *poly_B_comp
    };

    let (sc_proof_inner, r_y, _claims_inner): (SumcheckProof<G>, Vec<G::Scalar>, (Vec<_>, Vec<_>)) =
      SumcheckProof::prove_quad_batch(
        &claims_inner_joint,
        &num_rounds_y,
        polys_ABCs,
        polys_Z,
        &inner_r_powers,
        comb_func,
        &mut transcript,
      )?;

    let r_y = num_rounds_y
      .iter()
      .map(|num_rounds| {
        let (_, r_y_hi) = r_y.split_at(num_rounds_y_max - num_rounds);
        r_y_hi
      })
      .collect::<Vec<_>>();

    let evals_W = polys_W
      .par_iter()
      .zip(r_y.par_iter())
      .map(|(poly, r_y)| MultilinearPolynomial::evaluate_with(poly, &r_y[1..]))
      .collect::<Vec<_>>();

    // Create evaluation instances for W(r_y[1..]) and E(r_x)
    let (w_vec, u_vec) = {
      let mut w_vec = Vec::with_capacity(2 * num_instances);
      let mut u_vec = Vec::with_capacity(2 * num_instances);
      w_vec.extend(polys_W.into_iter().map(|poly| PolyEvalWitness { p: poly }));
      u_vec.extend(
        evals_W
          .iter()
          .zip(U.iter())
          .zip(r_y)
          .map(|((&eval, u), r_y)| PolyEvalInstance {
            c: u.comm_W,
            x: r_y[1..].to_vec(),
            e: eval,
          }),
      );

      w_vec.extend(polys_E.into_iter().map(|poly| PolyEvalWitness { p: poly }));
      u_vec.extend(
        evals_E
          .iter()
          .zip(U.iter())
          .zip(r_x)
          .map(|((eval_E, u), r_x)| PolyEvalInstance {
            c: u.comm_E,
            x: r_x,
            e: *eval_E,
          }),
      );
      (w_vec, u_vec)
    };

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

    let (evals_Az, evals_Bz, evals_Cz): (Vec<_>, Vec<_>, Vec<_>) =
      evals_Az_Bz_Cz.into_iter().multiunzip();

    Ok(BatchedRelaxedR1CSSNARK {
      sc_proof_outer,
      claims_outer: (evals_Az, evals_Bz, evals_Cz),
      evals_E,
      sc_proof_inner,
      evals_W,
      sc_proof_batch,
      evals_batch: claims_batch_left,
      eval_arg,
    })
  }

  fn verify(&self, vk: &Self::VerifierKey, U: &[RelaxedR1CSInstance<G>]) -> Result<(), NovaError> {
    let mut transcript = G::TE::new(b"BatchedRelaxedR1CSSNARK");

    transcript.absorb(b"vk", &vk.digest());
    U.iter().for_each(|u| {
      transcript.absorb(b"U", u);
    });

    let num_instances = U.len();

    let (num_rounds_x, num_rounds_y): (Vec<_>, Vec<_>) = vk
      .S
      .iter()
      .map(|s| (s.num_cons.log_2(), s.num_vars.log_2() + 1))
      .unzip();
    let num_rounds_x_max = *num_rounds_x.iter().max().unwrap();
    let num_rounds_y_max = *num_rounds_y.iter().max().unwrap();

    // Define τ polynomials of the appropriate size for each instance
    let polys_tau = {
      let tau = transcript.squeeze(b"t")?;

      num_rounds_x
        .iter()
        .map(|&num_rounds| PowPolynomial::new(&tau, num_rounds))
        .collect::<Vec<_>>()
    };

    // Sample challenge for random linear-combination of outer claims
    let outer_r = transcript.squeeze(b"out_r")?;
    let outer_r_powers = powers::<G>(&outer_r, num_instances);

    let (claim_outer_final, r_x) = self.sc_proof_outer.verify_batch(
      &vec![G::Scalar::ZERO; num_instances],
      &num_rounds_x,
      &outer_r_powers,
      3,
      &mut transcript,
    )?;

    // Collect evaluation point for each instance
    let r_x = num_rounds_x
      .iter()
      .map(|num_rounds| r_x[(num_rounds_x_max - num_rounds)..].to_vec())
      .collect::<Vec<_>>();

    // Extract evaluations into a vector [(Azᵢ, Bzᵢ, Czᵢ, Eᵢ)]
    let ABCE_evals = self
      .evals_E
      .iter()
      .zip(self.claims_outer.0.iter())
      .zip(self.claims_outer.1.iter())
      .zip(self.claims_outer.2.iter())
      .map(|(((&eval_E, &claim_Az), &claim_Bz), &claim_Cz)| (claim_Az, claim_Bz, claim_Cz, eval_E))
      .collect::<Vec<_>>();

    // Add evaluations of Az, Bz, Cz, E to transcript
    ABCE_evals
      .iter()
      .cloned()
      .for_each(|(claim_Az, claim_Bz, claim_Cz, eval_E)| {
        transcript.absorb(
          b"claims_outer",
          &[claim_Az, claim_Bz, claim_Cz, eval_E].as_slice(),
        )
      });

    // Evaluate τ(rₓ) for each instance
    let evals_tau = polys_tau
      .iter()
      .zip(r_x.iter())
      .map(|(poly_tau, r_x)| poly_tau.evaluate(r_x))
      .collect::<Vec<_>>();

    // Compute expected claim τ(rₓ)⋅∑ᵢ rⁱ⋅(Azᵢ⋅Bzᵢ − uᵢ⋅Czᵢ − Eᵢ)
    let claim_outer_final_expected = ABCE_evals
      .iter()
      .zip(U.iter())
      .zip(evals_tau)
      .map(|(((claim_Az, claim_Bz, claim_Cz, eval_E), u), eval_tau)| {
        eval_tau * (*claim_Az * claim_Bz - u.u * claim_Cz - eval_E)
      })
      .zip(outer_r_powers.iter())
      .map(|(eval, r)| eval * r)
      .sum::<G::Scalar>();

    if claim_outer_final != claim_outer_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let inner_r = transcript.squeeze(b"in_r")?;
    let inner_r_square = inner_r.square();
    let inner_r_cube = inner_r_square * inner_r;
    let inner_r_powers = powers::<G>(&inner_r_cube, num_instances);

    // Compute inner claim ∑ᵢ r³ⁱ⋅(Azᵢ + r⋅Bzᵢ + r²⋅Czᵢ)
    let claims_inner = ABCE_evals
      .iter()
      .map(|(claim_Az, claim_Bz, claim_Cz, _)| {
        *claim_Az + inner_r * *claim_Bz + inner_r_square * *claim_Cz
      })
      .collect::<Vec<_>>();

    let (claim_inner_final, r_y) = self.sc_proof_inner.verify_batch(
      &claims_inner,
      &num_rounds_y,
      &inner_r_powers,
      2,
      &mut transcript,
    )?;
    let r_y: Vec<Vec<G::Scalar>> = num_rounds_y
      .iter()
      .map(|num_rounds| r_y[(num_rounds_y_max - num_rounds)..].to_vec())
      .collect();

    // Compute evaluations of Zᵢ = [Wᵢ, uᵢ, Xᵢ] at r_y
    // Zᵢ(r_y) = (1−r_y[0])⋅W(r_y[1..]) + r_y[0]⋅MLE([uᵢ, Xᵢ])(r_y[1..])
    let evals_Z = self
      .evals_W
      .iter()
      .zip(U.iter())
      .zip(r_y.iter())
      .map(|((eval_W, U), r_y)| {
        let eval_X = {
          // constant term
          let mut poly_X = vec![(0, U.u)];
          //remaining inputs
          poly_X.extend(
            U.X
              .iter()
              .enumerate()
              .map(|(i, x_i)| (i + 1, *x_i))
              .collect::<Vec<(usize, G::Scalar)>>(),
          );
          SparsePolynomial::new(r_y.len() - 1, poly_X).evaluate(&r_y[1..])
        };
        (G::Scalar::ONE - r_y[0]) * eval_W + r_y[0] * eval_X
      })
      .collect::<Vec<_>>();

    // compute evaluations of R1CS matrices M(r_x, r_y) = eq(r_y)ᵀ⋅M⋅eq(r_x)
    let multi_evaluate = |M_vec: &[&SparseMatrix<G::Scalar>],
                          r_x: &[G::Scalar],
                          r_y: &[G::Scalar]|
     -> Vec<G::Scalar> {
      let evaluate_with_table =
        |M: &SparseMatrix<G::Scalar>, T_x: &[G::Scalar], T_y: &[G::Scalar]| -> G::Scalar {
          M.indptr
            .par_windows(2)
            .enumerate()
            .map(|(row_idx, ptrs)| {
              M.get_row_unchecked(ptrs.try_into().unwrap())
                .map(|(val, col_idx)| T_x[row_idx] * T_y[*col_idx] * val)
                .sum::<G::Scalar>()
            })
            .sum()
        };

      let (T_x, T_y) = rayon::join(
        || EqPolynomial::new(r_x.to_vec()).evals(),
        || EqPolynomial::new(r_y.to_vec()).evals(),
      );

      M_vec
        .par_iter()
        .map(|&M_vec| evaluate_with_table(M_vec, &T_x, &T_y))
        .collect()
    };

    // Compute inner claim ∑ᵢ r³ⁱ⋅(Aᵢ(r_x, r_y) + r⋅Bᵢ(r_x, r_y) + r²⋅Cᵢ(r_x, r_y))⋅Zᵢ(r_y)
    let claim_inner_final_expected = vk
      .S
      .iter()
      .zip(r_x.iter().zip(r_y.iter()))
      .map(|(S, (r_x, r_y))| {
        let evals = multi_evaluate(&[&S.A, &S.B, &S.C], r_x, r_y);
        evals[0] + inner_r * evals[1] + inner_r_square * evals[2]
      })
      .zip(evals_Z.iter())
      .zip(inner_r_powers.iter())
      .map(|((eval, eval_Z), r_i)| eval * r_i * eval_Z)
      .sum::<G::Scalar>();

    if claim_inner_final != claim_inner_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    // Create evaluation instances for W(r_y[1..]) and E(r_x)
    let u_vec = {
      let mut u_vec = Vec::with_capacity(2 * num_instances);
      u_vec.extend(
        self
          .evals_W
          .iter()
          .zip(U.iter())
          .zip(r_y.iter())
          .map(|((&eval, u), r_y)| PolyEvalInstance {
            c: u.comm_W,
            x: r_y[1..].to_vec(),
            e: eval,
          }),
      );

      u_vec.extend(
        self
          .evals_E
          .iter()
          .zip(U.iter())
          .zip(r_x.iter())
          .map(|((&eval, u), r_x)| PolyEvalInstance {
            c: u.comm_E,
            x: r_x.to_vec(),
            e: eval,
          }),
      );
      u_vec
    };

    let batched_u = batch_eval_verify(
      u_vec,
      &mut transcript,
      &self.sc_proof_batch,
      &self.evals_batch,
    )?;

    // verify
    EE::verify(
      &vk.vk_ee,
      &mut transcript,
      &batched_u.c,
      &batched_u.x,
      &batched_u.e,
      &self.eval_arg,
    )?;

    Ok(())
  }
}
