//! TODO: Doc

use ff::Field;
use serde::{Deserialize, Serialize};

use abomonation::Abomonation;
use abomonation_derive::Abomonation;
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
  spartan::{polys::multilinear::SparsePolynomial, snark::batch_eval_verify},
  traits::{
    evaluation::EvaluationEngineTrait,
    snark::{BatchedRelaxedR1CSSNARKTrait, DigestHelperTrait},
    Group, TranscriptEngineTrait,
  },
  CommitmentKey,
};

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
}

/// TODO: Doc
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

    let (num_vars_x, num_vars_y): (Vec<_>, Vec<_>) = S
      .iter()
      .map(|s| (s.num_cons.log_2(), s.num_vars.log_2() + 1))
      .unzip();
    let num_rounds_x = *num_vars_x.iter().max().unwrap();
    let num_rounds_y = *num_vars_y.iter().max().unwrap();

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
    let outer_r_powers = powers::<G>(&outer_r, S.len());

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
      &outer_r_powers,
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

    let evals_E = E_polys.iter().map(|e| e.evaluate(&r_x)).collect::<Vec<_>>();

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
    let inner_r_square = inner_r.square();
    let inner_r_cube = inner_r_square * inner_r;
    let inner_r_powers = powers::<G>(&inner_r_cube, S.len());

    let claim_inner_joint = inner_r_powers
      .iter()
      .zip(claims_Az.iter())
      .zip(claims_Bz.iter())
      .zip(claims_Cz.iter())
      .fold(
        G::Scalar::ZERO,
        |acc, (((r_i, claim_Az), claim_Bz), claim_Cz)| {
          acc + *r_i * (*claim_Az + inner_r * claim_Bz + inner_r * inner_r * claim_Cz)
        },
      );

    let mut poly_ABCs = {
      let evals_rx = EqPolynomial::new(r_x.clone()).evals();

      let (evals_As, evals_Bs, evals_Cs) = S.iter().fold(
        (vec![], vec![], vec![]),
        |(mut acc_A, mut acc_B, mut acc_C), s| {
          let mut truncated_evals_rx = evals_rx.clone();
          truncated_evals_rx.truncate(s.num_cons);
          let (evals_A, evals_B, evals_C) = compute_eval_table_sparse(s, &truncated_evals_rx); // TODO: Truncate
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
          .map(|((eval_A, eval_B), eval_C)| eval_A + inner_r * eval_B + inner_r_square * eval_C)
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
        &inner_r_powers,
        comb_func,
        &mut transcript,
      )?;

    let evals_W = W_polys
      .iter()
      .map(|w| w.evaluate(&r_y[1..]))
      .collect::<Vec<_>>();

    // Create evaluation instances for W(r_y[1..]) and E(r_x)
    let (w_vec, u_vec) = {
      let mut w_vec = Vec::with_capacity(2 * S.len());
      let mut u_vec = Vec::with_capacity(2 * S.len());
      w_vec.extend(
        W_polys
          .into_iter()
          .map(|poly| PolyEvalWitness { p: poly.Z }),
      );
      u_vec.extend(evals_W.iter().zip(U.iter()).zip(num_vars_y.iter()).map(
        |((&eval, u), &num_vars)| PolyEvalInstance {
          c: u.comm_W,
          x: r_y[1..num_vars].to_vec(),
          e: eval,
        },
      ));

      w_vec.extend(
        E_polys
          .into_iter()
          .map(|poly| PolyEvalWitness { p: poly.Z }),
      );
      u_vec.extend(evals_E.iter().zip(U.iter()).zip(num_vars_x.iter()).map(
        |((&eval, u), &num_vars)| PolyEvalInstance {
          c: u.comm_E,
          x: r_x[..num_vars].to_vec(),
          e: eval,
        },
      ));
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

  fn verify(&self, vk: &Self::VerifierKey, U: &[RelaxedR1CSInstance<G>]) -> Result<(), NovaError> {
    let mut transcript = G::TE::new(b"BatchedRelaxedR1CSSNARK");

    transcript.absorb(b"vk", &vk.digest());
    U.iter().for_each(|u| {
      transcript.absorb(b"U", u);
    });

    let (num_vars_x, num_vars_y): (Vec<_>, Vec<_>) = vk
      .S
      .iter()
      .map(|s| (s.num_cons.log_2(), s.num_vars.log_2() + 1))
      .unzip();
    let num_rounds_x = *num_vars_x.iter().max().unwrap();
    let num_rounds_y = *num_vars_y.iter().max().unwrap();

    let tau_poly = {
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

      Ok(EqPolynomial::new(tau_vars))
    }?;

    // Sample challenge for random linear-combination of outer claims
    let outer_r = transcript.squeeze(b"out_r")?;
    let coeffs = powers::<G>(&outer_r, vk.S.len());

    let (claim_outer_final, r_x) =
      self
        .sc_proof_outer
        .verify(G::Scalar::ZERO, num_rounds_x, 3, &mut transcript)?;

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

    // Evaluate τ(rₓ)
    let tau_eval = tau_poly.evaluate(&r_x);

    // Compute expected claim τ(rₓ)⋅∑ᵢ rⁱ⋅(Azᵢ⋅Bzᵢ − uᵢ⋅Czᵢ − Eᵢ)
    let claim_outer_final_expected = tau_eval
      * ABCE_evals
        .iter()
        .zip(U.iter())
        .map(|((claim_Az, claim_Bz, claim_Cz, eval_E), u)| {
          *claim_Az * claim_Bz - u.u * claim_Cz - eval_E
        })
        .zip(coeffs.iter())
        .map(|(claim, coeff)| claim * coeff)
        .sum::<G::Scalar>();

    if claim_outer_final != claim_outer_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let inner_r = transcript.squeeze(b"in_r")?;
    let inner_r_square = inner_r.square();
    let inner_r_cube = inner_r_square * inner_r;
    let inner_r_powers = powers::<G>(&inner_r_cube, vk.S.len());

    // Compute inner claim ∑ᵢ r³ⁱ⋅(Azᵢ + r⋅Bzᵢ + r²⋅Czᵢ)
    let claim_inner_joint = ABCE_evals
      .iter()
      .map(|(claim_Az, claim_Bz, claim_Cz, _)| {
        *claim_Az + inner_r * *claim_Bz + inner_r_square * *claim_Cz
      })
      .zip(inner_r_powers.iter())
      .fold(G::Scalar::ZERO, |acc, (claim, r_i)| acc + claim * r_i);

    let (claim_inner_final, r_y) =
      self
        .sc_proof_inner
        .verify(claim_inner_joint, num_rounds_y, 2, &mut transcript)?;

    // Compute evaluations of Zᵢ = [Wᵢ, uᵢ, Xᵢ] at r_y
    // Zᵢ(r_y) = (1−r_y[0])⋅W(r_y[1..]) + r_y[0]⋅MLE([uᵢ, Xᵢ])(r_y[1..])
    let evals_Z = self
      .evals_W
      .iter()
      .zip(U.iter())
      .zip(num_vars_y.iter())
      .map(|((eval_W, U), &num_vars)| {
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
          SparsePolynomial::new(num_vars - 1, poly_X).evaluate(&r_y[1..num_vars])
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

      (0..M_vec.len())
        .into_par_iter()
        .map(|i| evaluate_with_table(M_vec[i], &T_x, &T_y))
        .collect()
    };

    // Compute inner claim ∑ᵢ r³ⁱ⋅(Aᵢ(r_x, r_y) + r⋅Bᵢ(r_x, r_y) + r²⋅Cᵢ(r_x, r_y))⋅Zᵢ(r_y)
    let claim_inner_final_expected = vk
      .S
      .iter()
      .zip(num_vars_x.iter().zip(num_vars_y.iter()))
      .map(|(S, (&vars_x, &vars_y))| {
        let evals = multi_evaluate(&[&S.A, &S.B, &S.C], &r_x[..vars_x], &r_y[..vars_y]);
        evals[0] + inner_r * evals[1] + inner_r_square * evals[2]
      })
      .zip(evals_Z.iter())
      .zip(inner_r_powers.iter())
      .fold(G::Scalar::ZERO, |acc, ((eval, r_i), eval_Z)| {
        acc + eval * r_i * eval_Z
      });

    if claim_inner_final != claim_inner_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    // Create evaluation instances for W(r_y[1..]) and E(r_x)
    let u_vec = {
      let mut u_vec = Vec::with_capacity(2 * vk.S.len());
      u_vec.extend(
        self
          .evals_W
          .iter()
          .zip(U.iter())
          .zip(num_vars_y.iter())
          .map(|((&eval, u), &num_vars)| PolyEvalInstance {
            c: u.comm_W,
            x: r_y[1..num_vars].to_vec(),
            e: eval,
          }),
      );

      u_vec.extend(
        self
          .evals_E
          .iter()
          .zip(U.iter())
          .zip(num_vars_x.iter())
          .map(|((&eval, u), &num_vars)| PolyEvalInstance {
            c: u.comm_E,
            x: r_x[..num_vars].to_vec(),
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
