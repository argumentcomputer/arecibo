//! batched pp snark
//!
//!

use crate::{
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
  spartan::{
    math::Math,
    polys::{
      eq::EqPolynomial,
      identity::IdentityPolynomial,
      multilinear::MultilinearPolynomial,
      multilinear::SparsePolynomial,
      power::PowPolynomial,
      univariate::{CompressedUniPoly, UniPoly},
    },
    powers,
    ppsnark::{
      InnerSumcheckInstance, MemorySumcheckInstance, OuterSumcheckInstance,
      R1CSShapeSparkCommitment, R1CSShapeSparkRepr, SumcheckEngine,
    },
    sumcheck::SumcheckProof,
    PolyEvalInstance, PolyEvalWitness,
  },
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentTrait, Len},
    evaluation::EvaluationEngineTrait,
    snark::{BatchedRelaxedR1CSSNARKTrait, DigestHelperTrait},
    Group, TranscriptEngineTrait,
  },
  Commitment, CommitmentKey, CompressedCommitment,
};
use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use ff::{Field, PrimeField};
use itertools::MultiUnzip;
use once_cell::sync::*;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// A type that represents the prover's key
#[derive(Clone, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(where < G::Scalar as PrimeField >::Repr: Abomonation)]
pub struct ProverKey<G: Group, EE: EvaluationEngineTrait<G>> {
  pk_ee: EE::ProverKey,
  S_repr: Vec<R1CSShapeSparkRepr<G>>,
  S_comm: Vec<R1CSShapeSparkCommitment<G>>,
  #[abomonate_with(< G::Scalar as PrimeField >::Repr)]
  vk_digest: G::Scalar, // digest of verifier's key
}

/// A type that represents the verifier's key
#[derive(Clone, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(where < G::Scalar as PrimeField >::Repr: Abomonation)]
pub struct VerifierKey<G: Group, EE: EvaluationEngineTrait<G>> {
  vk_ee: EE::VerifierKey,
  S_comm: Vec<R1CSShapeSparkCommitment<G>>,
  num_vars: Vec<usize>,
  #[abomonation_skip]
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<G::Scalar>,
}
impl<G: Group, EE: EvaluationEngineTrait<G>> VerifierKey<G, EE> {
  fn new(
    num_vars: Vec<usize>,
    S_comm: Vec<R1CSShapeSparkCommitment<G>>,
    vk_ee: EE::VerifierKey,
  ) -> Self {
    VerifierKey {
      num_vars,
      S_comm,
      vk_ee,
      digest: Default::default(),
    }
  }
}
impl<G: Group, EE: EvaluationEngineTrait<G>> SimpleDigestible for VerifierKey<G, EE> {}

impl<G: Group, EE: EvaluationEngineTrait<G>> DigestHelperTrait<G> for VerifierKey<G, EE> {
  /// Returns the digest of the verifier's key
  fn digest(&self) -> G::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc = DigestComputer::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure to retrieve digest!")
  }
}

/// A succinct proof of knowledge of a witness to a relaxed R1CS instance
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct BatchedRelaxedR1CSSNARK<G: Group, EE: EvaluationEngineTrait<G>> {
  // commitment to oracles: the first three are for Az, Bz, Cz,
  // and the last two are for memory reads
  comms_Az_Bz_Cz: Vec<[CompressedCommitment<G>; 3]>,
  comms_L_row_col: Vec<[CompressedCommitment<G>; 2]>,
  // commitments to aid the memory checks
  // [t_plus_r_inv_row, w_plus_r_inv_row, t_plus_r_inv_col, w_plus_r_inv_col]
  comms_mem_oracles: Vec<[CompressedCommitment<G>; 4]>,

  // claims about Az, Bz, and Cz polynomials
  evals_Az_Bz_Cz_at_tau: Vec<[G::Scalar; 3]>,

  // sum-check
  sc: SumcheckProof<G>,

  // claims from the end of sum-check
  evals_Az_Bz_Cz_W_E: Vec<[G::Scalar; 5]>,
  evals_L_row_col: Vec<[G::Scalar; 2]>,
  // [t_plus_r_inv_row, w_plus_r_inv_row, t_plus_r_inv_col, w_plus_r_inv_col]
  evals_mem_oracle: Vec<[G::Scalar; 4]>,
  // [val_A, val_B, val_C, row, col, ts_row, ts_col]
  evals_mem_preprocessed: Vec<[G::Scalar; 7]>,

  // a PCS evaluation argument
  eval_arg: EE::EvaluationArgument,
}

impl<G: Group, EE: EvaluationEngineTrait<G>> BatchedRelaxedR1CSSNARKTrait<G>
  for BatchedRelaxedR1CSSNARK<G, EE>
where
  <G::Scalar as PrimeField>::Repr: Abomonation,
{
  type ProverKey = ProverKey<G, EE>;
  type VerifierKey = VerifierKey<G, EE>;

  // TODO: Replace with ck_floor
  fn commitment_key_floor() -> Box<dyn for<'a> Fn(&'a R1CSShape<G>) -> usize> {
    Box::new(|shape: &R1CSShape<G>| -> usize {
      // the commitment key should be large enough to commit to the R1CS matrices
      std::cmp::max(
        shape.A.len() + shape.B.len() + shape.C.len(),
        std::cmp::max(shape.num_cons, 2 * shape.num_vars),
      )
    })
  }

  fn setup(
    ck: &CommitmentKey<G>,
    S: &[R1CSShape<G>],
  ) -> Result<(Self::ProverKey, Self::VerifierKey), NovaError> {
    for s in S.iter() {
      // check the provided commitment key meets minimal requirements
      if ck.length() < Self::commitment_key_floor()(s) {
        // return Err(NovaError::InvalidCommitmentKeyLength);
        return Err(NovaError::InternalError);
      }
    }
    let (pk_ee, vk_ee) = EE::setup(ck);

    let S = S.iter().map(|s| s.pad()).collect::<Vec<_>>();
    let S_repr = S.iter().map(R1CSShapeSparkRepr::new).collect::<Vec<_>>();
    let S_comm = S_repr
      .iter()
      .map(|s_repr| s_repr.commit(ck))
      .collect::<Vec<_>>();
    let num_vars = S.iter().map(|s| s.num_vars).collect::<Vec<_>>();
    let vk = VerifierKey::new(num_vars, S_comm.clone(), vk_ee);
    let pk = ProverKey {
      pk_ee,
      S_repr,
      S_comm,
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
    // Pad shapes so that num_vars = num_cons = Nᵢ and check the sizes are correct
    let S = S
      .par_iter()
      .map(|s| {
        let s = s.pad();
        if s.is_regular_shape() {
          Ok(s)
        } else {
          Err(NovaError::InternalError)
        }
      })
      .collect::<Result<Vec<_>, _>>()?;

    // N[i] = max(|Aᵢ|+|Bᵢ|+|Cᵢ|, 2*num_varsᵢ, num_consᵢ)
    let N = pk.S_repr.iter().map(|s| s.N).collect::<Vec<_>>();
    assert!(N.iter().all(|&Ni| Ni.is_power_of_two()));

    // Pad [(Wᵢ,Eᵢ)] to the next power of 2 (not to Ni)
    let W = W
      .par_iter()
      .zip(S.par_iter())
      .map(|(w, s)| w.pad(s))
      .collect::<Vec<RelaxedR1CSWitness<G>>>();

    // number of rounds of sum-check
    let num_rounds_sc = N.iter().max().unwrap().log_2();

    // Initialize transcript with vk || [Uᵢ]
    // NOTE: We should prepend with the number of instances
    let mut transcript = G::TE::new(b"BatchedRelaxedR1CSSNARK");
    transcript.absorb(b"vk", &pk.vk_digest);
    U.iter().for_each(|u| {
      transcript.absorb(b"U", u);
    });

    // Append public inputs to Wᵢ: Zᵢ = [Wᵢ, uᵢ, Xᵢ]
    let polys_Z = W
      .par_iter()
      .zip(U.par_iter())
      .zip(N.par_iter())
      .map(|((W, U), &Ni)| {
        // poly_Z will be resized later, so we preallocate the correct capacity
        let mut poly_Z = Vec::with_capacity(Ni);
        poly_Z.extend(W.W.iter().chain([&U.u]).chain(U.X.iter()));
        poly_Z
      })
      .collect::<Vec<Vec<G::Scalar>>>();

    // Move polys_W and polys_E, as well as U.u out of U
    let (comms_W_E, us): (Vec<_>, Vec<_>) = U.iter().map(|U| ([U.comm_W, U.comm_E], U.u)).unzip();
    let (polys_W, polys_E): (Vec<_>, Vec<_>) = W.into_iter().map(|w| (w.W, w.E)).unzip();

    // Compute [Az, Bz, Cz]
    let mut polys_Az_Bz_Cz = polys_Z
      .par_iter()
      .zip(S.par_iter())
      .map(|(z, s)| {
        let (Az, Bz, Cz) = s.multiply_vec(z)?;
        Ok([Az, Bz, Cz])
      })
      .collect::<Result<Vec<_>, _>>()?;

    // Commit to [Az, Bz, Cz] and add to transcript
    let comms_Az_Bz_Cz = polys_Az_Bz_Cz
      .par_iter()
      .map(|[Az, Bz, Cz]| {
        let (comm_Az, (comm_Bz, comm_Cz)) = rayon::join(
          || G::CE::commit(ck, Az),
          || rayon::join(|| G::CE::commit(ck, Bz), || G::CE::commit(ck, Cz)),
        );
        [comm_Az, comm_Bz, comm_Cz]
      })
      .collect::<Vec<_>>();
    comms_Az_Bz_Cz
      .iter()
      .for_each(|comms| transcript.absorb(b"c", &comms.as_slice()));

    // Compute eq(tau) for each instance in log2(Ni) variables
    let tau = transcript.squeeze(b"t")?;
    let (polys_tau, coords_tau): (Vec<_>, Vec<_>) = N
      .iter()
      .map(|&N_i| {
        let log_Ni = N_i.log_2();
        let poly = PowPolynomial::new(&tau, log_Ni);
        let evals = poly.evals();
        let coords = poly.coordinates();
        (evals, coords)
      })
      .unzip();

    // Pad [Az, Bz, Cz] to Ni
    polys_Az_Bz_Cz
      .par_iter_mut()
      .zip(N.par_iter())
      .for_each(|(az_bz_cz, &Ni)| {
        az_bz_cz
          .par_iter_mut()
          .for_each(|mz| mz.resize(Ni, G::Scalar::ZERO))
      });

    // Evaluate and commit to [Az(tau), Bz(tau), Cz(tau)]
    let evals_Az_Bz_Cz_at_tau = polys_Az_Bz_Cz
      .par_iter()
      .zip(coords_tau.par_iter())
      .map(|([Az, Bz, Cz], tau_coords)| {
        let (eval_Az, (eval_Bz, eval_Cz)) = rayon::join(
          || MultilinearPolynomial::evaluate_with(Az, tau_coords),
          || {
            rayon::join(
              || MultilinearPolynomial::evaluate_with(Bz, tau_coords),
              || MultilinearPolynomial::evaluate_with(Cz, tau_coords),
            )
          },
        );
        [eval_Az, eval_Bz, eval_Cz]
      })
      .collect::<Vec<_>>();

    // absorb the claimed evaluations into the transcript
    evals_Az_Bz_Cz_at_tau.iter().for_each(|evals| {
      transcript.absorb(b"e", &evals.as_slice());
    });

    // Pad Z, E to Nᵢ
    let polys_Z = polys_Z
      .into_par_iter()
      .zip(N.par_iter())
      .map(|(mut poly_Z, &Ni)| {
        poly_Z.resize(Ni, G::Scalar::ZERO);
        poly_Z
      })
      .collect::<Vec<_>>();
    // Pad both W,E to have the same size. This is inefficient for W since the second half is empty,
    // but it makes it easier to handle the batching at the end.
    let polys_E = polys_E
      .into_par_iter()
      .zip(N.par_iter())
      .map(|(mut poly_E, &Ni)| {
        poly_E.resize(Ni, G::Scalar::ZERO);
        poly_E
      })
      .collect::<Vec<_>>();
    let polys_W = polys_W
      .into_par_iter()
      .zip(N.par_iter())
      .map(|(mut poly_W, &Ni)| {
        poly_W.resize(Ni, G::Scalar::ZERO);
        poly_W
      })
      .collect::<Vec<_>>();

    // (2) send commitments to the following two oracles
    // L_row(i) = eq(tau, row(i)) for all i in [0..Nᵢ]
    // L_col(i) = z(col(i)) for all i in [0..Nᵢ]
    let polys_L_row_col = S
      .par_iter()
      .zip(N.par_iter())
      .zip(polys_Z.par_iter())
      .zip(polys_tau.par_iter())
      .map(|(((S, &Ni), poly_Z), poly_tau)| {
        let mut L_row = vec![poly_tau[0]; Ni]; // we place mem_row[0] since resized row is appended with 0s
        let mut L_col = vec![poly_Z[Ni - 1]; Ni]; // we place mem_col[Ni-1] since resized col is appended with Ni-1

        for (i, (val_r, val_c)) in S
          .A
          .iter()
          .chain(S.B.iter())
          .chain(S.C.iter())
          .map(|(r, c, _)| (poly_tau[r], poly_Z[c]))
          .enumerate()
        {
          L_row[i] = val_r;
          L_col[i] = val_c;
        }

        [L_row, L_col]
      })
      .collect::<Vec<_>>();

    let comms_L_row_col = polys_L_row_col
      .par_iter()
      .map(|[L_row, L_col]| {
        let (comm_L_row, comm_L_col) =
          rayon::join(|| G::CE::commit(ck, L_row), || G::CE::commit(ck, L_col));
        [comm_L_row, comm_L_col]
      })
      .collect::<Vec<_>>();

    // absorb commitments to L_row and L_col in the transcript
    comms_L_row_col.iter().for_each(|comms| {
      transcript.absorb(b"e", &comms.as_slice());
    });

    // For each instance, batch Mz = Az + c*Bz + c^2*Cz
    let c = transcript.squeeze(b"c")?;

    let polys_Mz: Vec<_> = polys_Az_Bz_Cz
      .par_iter()
      .map(|polys_Az_Bz_Cz| {
        let poly_vec = polys_Az_Bz_Cz.iter().collect::<Vec<_>>();
        let w = PolyEvalWitness::<G>::batch(&poly_vec, &c);
        w.p
      })
      .collect();

    let evals_Mz: Vec<_> = comms_Az_Bz_Cz
      .iter()
      .zip(evals_Az_Bz_Cz_at_tau.iter())
      .map(|(comm_Az_Bz_Cz, evals_Az_Bz_Cz_at_tau)| {
        let u = PolyEvalInstance::<G>::batch(
          comm_Az_Bz_Cz.as_slice(),
          &[], // ignored by the function
          evals_Az_Bz_Cz_at_tau.as_slice(),
          &c,
        );
        u.e
      })
      .collect();

    // we now need to prove three claims for each instance
    // (outer)
    //   0 = \sum_x poly_tau(x) * (poly_Az(x) * poly_Bz(x) - poly_uCz_E(x))
    //   eval_Az_at_tau + c * eval_Bz_at_tau + c^2 * eval_Cz_at_tau = (Az+c*Bz+c^2*Cz)(tau)
    // (inner)
    //   eval_Az_at_tau + c * eval_Bz_at_tau + c^2 * eval_Cz_at_tau = \sum_y L_row(y) * (val_A(y) + c * val_B(y) + c^2 * val_C(y)) * L_col(y)
    // (mem)
    //   L_row(i) = eq(tau, row(i))
    //   L_col(i) = z(col(i))
    let outer_sc_inst = polys_Az_Bz_Cz
      .par_iter()
      .zip(polys_E.par_iter())
      .zip(polys_Mz.into_par_iter())
      .zip(polys_tau.par_iter())
      .zip(evals_Mz.par_iter())
      .zip(us.par_iter())
      .map(
        |((((([poly_Az, poly_Bz, poly_Cz], poly_E), poly_Mz), poly_tau), eval_Mz), u)| {
          let poly_uCz_E = poly_Cz
            .par_iter()
            .zip(poly_E.par_iter())
            .map(|(cz, e)| *u * cz + e)
            .collect();
          OuterSumcheckInstance::new(
            poly_tau.clone(),
            poly_Az.clone(),
            poly_Bz.clone(),
            poly_uCz_E,
            poly_Mz, // Mz = Az + c * Bz + c^2 * Cz
            eval_Mz, // eval_Az_at_tau + c * eval_Az_at_tau + c^2 * eval_Cz_at_tau
          )
        },
      )
      .collect::<Vec<_>>();

    let inner_sc_inst = pk
      .S_repr
      .par_iter()
      .zip(evals_Mz.par_iter())
      .zip(polys_L_row_col.par_iter())
      .map(|((s_repr, eval_Mz), [poly_L_row, poly_L_col])| {
        let c_square = c.square();
        let val = s_repr
          .val_A
          .par_iter()
          .zip(s_repr.val_B.par_iter())
          .zip(s_repr.val_C.par_iter())
          .map(|((v_a, v_b), v_c)| *v_a + c * *v_b + c_square * *v_c)
          .collect::<Vec<G::Scalar>>();
        InnerSumcheckInstance::new(
          *eval_Mz,
          MultilinearPolynomial::new(poly_L_row.clone()),
          MultilinearPolynomial::new(poly_L_col.clone()),
          MultilinearPolynomial::new(val),
        )
      })
      .collect::<Vec<_>>();

    // a third sum-check instance to prove the read-only memory claim
    // we now need to prove that L_row and L_col are well-formed
    let (mem_sc_inst, comms_mem_oracles, polys_mem_oracles) = {
      let gamma = transcript.squeeze(b"g")?;
      let r = transcript.squeeze(b"r")?;

      // We start by computing oracles and auxiliary polynomials to help prove the claim
      // oracles correspond to [t_plus_r_inv_row, w_plus_r_inv_row, t_plus_r_inv_col, w_plus_r_inv_col]
      let (comms_mem_oracles, polys_mem_oracles, mem_aux): (Vec<_>, Vec<_>, Vec<_>) = pk
        .S_repr
        .iter()
        .zip(polys_tau.iter())
        .zip(polys_Z.iter())
        .zip(polys_L_row_col.iter())
        .map(|(((s_repr, poly_tau), poly_Z), [L_row, L_col])| {
          let (comm_mem_oracles, poly_mem_oracles, aux_poly_mem_oracles) =
            MemorySumcheckInstance::<G>::compute_oracles(
              ck,
              &r,
              &gamma,
              poly_tau,
              &s_repr.row,
              L_row,
              &s_repr.ts_row,
              poly_Z,
              &s_repr.col,
              L_col,
              &s_repr.ts_col,
            )?;
          Ok((comm_mem_oracles, poly_mem_oracles, aux_poly_mem_oracles))
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .multiunzip();

      // Commit to oracles
      comms_mem_oracles.iter().for_each(|comms| {
        transcript.absorb(b"l", &comms.as_slice());
      });

      // Sample new random variable for eq polynomial
      let rho = transcript.squeeze(b"r")?;
      let N_max = N.iter().max().unwrap();
      let all_rhos = PowPolynomial::powers(&rho, N_max.log_2());

      let instances = pk
        .S_repr
        .par_iter()
        .zip(N.par_iter())
        .zip(polys_mem_oracles.par_iter())
        .zip(mem_aux.into_par_iter())
        .map(|(((s_repr, &Ni), polys_mem_oracles), polys_aux)| {
          MemorySumcheckInstance::<G>::new(
            polys_mem_oracles.clone(),
            polys_aux,
            PowPolynomial::evals_with_powers(&all_rhos, Ni.log_2()),
            s_repr.ts_row.clone(),
            s_repr.ts_col.clone(),
          )
        })
        .collect::<Vec<_>>();
      (instances, comms_mem_oracles, polys_mem_oracles)
    };

    // Run batched Sumcheck for the 3 claims for all instances.
    // Note that the polynomials for claims relating to instance i have size Ni.
    let (sc, rand_sc, claims_outer, claims_inner, claims_mem) = Self::prove_helper(
      num_rounds_sc,
      mem_sc_inst,
      outer_sc_inst,
      inner_sc_inst,
      &mut transcript,
    )?;

    let (evals_Az_Bz_Cz_W_E, evals_L_row_col, evals_mem_oracle, evals_mem_preprocessed) = {
      let evals_Az_Bz = claims_outer
        .into_iter()
        .map(|claims| [claims[0][0], claims[0][1]])
        .collect::<Vec<_>>();

      let evals_L_row_col = claims_inner
        .into_iter()
        .map(|claims| {
          // [L_row, L_col]
          [claims[0][0], claims[0][1]]
        })
        .collect::<Vec<_>>();

      let (evals_mem_oracle, evals_mem_ts): (Vec<_>, Vec<_>) = claims_mem
        .into_iter()
        .map(|claims| {
          (
            // [t_plus_r_inv_row, w_plus_r_inv_row, t_plus_r_inv_col, w_plus_r_inv_col]
            [claims[0][0], claims[0][1], claims[1][0], claims[1][1]],
            // [ts_row, ts_col]
            [claims[0][2], claims[1][2]],
          )
        })
        .unzip();

      let (evals_Cz_W_E, evals_mem_val_row_col): (Vec<_>, Vec<_>) = polys_Az_Bz_Cz
        .iter()
        .zip(polys_W.iter())
        .zip(polys_E.iter())
        .zip(pk.S_repr.iter())
        .map(|((([_, _, Cz], poly_W), poly_E), s_repr)| {
          let log_Ni = s_repr.N.log_2();
          let (_, rand_sc) = rand_sc.split_at(num_rounds_sc - log_Ni);
          let rand_sc_evals = EqPolynomial::new(rand_sc.to_vec()).evals();
          let e = [
            Cz,
            poly_W,
            poly_E,
            &s_repr.val_A,
            &s_repr.val_B,
            &s_repr.val_C,
            &s_repr.row,
            &s_repr.col,
          ]
          .into_iter()
          .map(|p| {
            // Manually compute evaluation to avoid recomputing rand_sc_evals
            p.par_iter()
              .zip(rand_sc_evals.par_iter())
              .map(|(p, eq)| *p * eq)
              .sum()
          })
          .collect::<Vec<G::Scalar>>();
          ([e[0], e[1], e[2]], [e[3], e[4], e[5], e[6], e[7]])
        })
        .unzip();

      let evals_Az_Bz_Cz_W_E = evals_Az_Bz
        .into_iter()
        .zip(evals_Cz_W_E)
        .map(|([Az, Bz], [Cz, W, E])| [Az, Bz, Cz, W, E])
        .collect::<Vec<_>>();

      // [val_A, val_B, val_C, row, col, ts_row, ts_col]
      let evals_mem_preprocessed = evals_mem_val_row_col
        .into_iter()
        .zip(evals_mem_ts)
        .map(|([val_A, val_B, val_C, row, col], [ts_row, ts_col])| {
          [val_A, val_B, val_C, row, col, ts_row, ts_col]
        })
        .collect::<Vec<_>>();
      (
        evals_Az_Bz_Cz_W_E,
        evals_L_row_col,
        evals_mem_oracle,
        evals_mem_preprocessed,
      )
    };

    let evals_vec = evals_Az_Bz_Cz_W_E
      .iter()
      .zip(evals_L_row_col.iter())
      .zip(evals_mem_oracle.iter())
      .zip(evals_mem_preprocessed.iter())
      .map(
        |(((Az_Bz_Cz_W_E, L_row_col), mem_oracles), mem_preprocessed)| {
          Az_Bz_Cz_W_E
            .iter()
            .chain(L_row_col)
            .chain(mem_oracles)
            .chain(mem_preprocessed)
            .cloned()
            .collect::<Vec<_>>()
        },
      )
      .collect::<Vec<_>>();

    let comms_vec = comms_Az_Bz_Cz
      .iter()
      .zip(comms_W_E.iter())
      .zip(comms_L_row_col.iter())
      .zip(comms_mem_oracles.iter())
      .zip(pk.S_comm.iter())
      .flat_map(
        |((((Az_Bz_Cz, comms_W_E), L_row_col), mem_oracles), S_comm)| {
          Az_Bz_Cz
            .iter()
            .chain(comms_W_E)
            .chain(L_row_col)
            .chain(mem_oracles)
            .chain([
              &S_comm.comm_val_A,
              &S_comm.comm_val_B,
              &S_comm.comm_val_C,
              &S_comm.comm_row,
              &S_comm.comm_col,
              &S_comm.comm_ts_row,
              &S_comm.comm_ts_col,
            ])
        },
      )
      .cloned()
      .collect::<Vec<_>>();

    let w_vec = polys_Az_Bz_Cz
      .into_iter()
      .zip(polys_W)
      .zip(polys_E)
      .zip(polys_L_row_col)
      .zip(polys_mem_oracles)
      .zip(pk.S_repr.iter())
      .flat_map(|(((((Az_Bz_Cz, W), E), L_row_col), mem_oracles), S_repr)| {
        Az_Bz_Cz
          .into_iter()
          .chain([W, E])
          .chain(L_row_col)
          .chain(mem_oracles)
          .chain([
            S_repr.val_A.clone(),
            S_repr.val_B.clone(),
            S_repr.val_C.clone(),
            S_repr.row.clone(),
            S_repr.col.clone(),
            S_repr.ts_row.clone(),
            S_repr.ts_col.clone(),
          ])
      })
      .map(|p| PolyEvalWitness::<G> { p })
      .collect::<Vec<_>>();

    evals_vec.iter().for_each(|evals| {
      transcript.absorb(b"e", &evals.as_slice()); // comm_vec is already in the transcript
    });
    let evals_vec = evals_vec.into_iter().flatten().collect::<Vec<_>>();

    let c = transcript.squeeze(b"c")?;

    // Compute number of variables for each polynomial
    let num_vars_u = w_vec.iter().map(|w| w.p.len().log_2()).collect::<Vec<_>>();
    let u_batch =
      PolyEvalInstance::<G>::batch_diff_size(&comms_vec, &evals_vec, &num_vars_u, rand_sc, c);
    let w_batch = PolyEvalWitness::<G>::batch_diff_size(w_vec, c);

    let eval_arg = EE::prove(
      ck,
      &pk.pk_ee,
      &mut transcript,
      &u_batch.c,
      &w_batch.p,
      &u_batch.x,
      &u_batch.e,
    )?;

    let comms_Az_Bz_Cz = comms_Az_Bz_Cz
      .into_iter()
      .map(|comms| comms.map(|comm| comm.compress()))
      .collect();
    let comms_L_row_col = comms_L_row_col
      .into_iter()
      .map(|comms| comms.map(|comm| comm.compress()))
      .collect();
    let comms_mem_oracles = comms_mem_oracles
      .into_iter()
      .map(|comms| comms.map(|comm| comm.compress()))
      .collect();

    Ok(BatchedRelaxedR1CSSNARK {
      comms_Az_Bz_Cz,
      comms_L_row_col,
      comms_mem_oracles,
      evals_Az_Bz_Cz_at_tau,
      sc,
      evals_Az_Bz_Cz_W_E,
      evals_L_row_col,
      evals_mem_oracle,
      evals_mem_preprocessed,
      eval_arg,
    })
  }

  fn verify(&self, vk: &Self::VerifierKey, U: &[RelaxedR1CSInstance<G>]) -> Result<(), NovaError> {
    let mut transcript = G::TE::new(b"BatchedRelaxedR1CSSNARK");

    transcript.absorb(b"vk", &vk.digest());
    U.iter().for_each(|u| {
      transcript.absorb(b"U", u);
    });

    let comms_Az_Bz_Cz = self
      .comms_Az_Bz_Cz
      .iter()
      .map(|comms| {
        comms
          .iter()
          .map(Commitment::<G>::decompress)
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;

    let comms_L_row_col = self
      .comms_L_row_col
      .iter()
      .map(|comms| {
        comms
          .iter()
          .map(Commitment::<G>::decompress)
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;

    let comms_mem_oracles = self
      .comms_mem_oracles
      .iter()
      .map(|comms| {
        comms
          .iter()
          .map(Commitment::<G>::decompress)
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;

    comms_Az_Bz_Cz
      .iter()
      .for_each(|comms| transcript.absorb(b"c", &comms.as_slice()));

    // number of rounds of sum-check
    let num_rounds_sc = vk.S_comm.iter().map(|s| s.N.log_2()).max().unwrap();
    let tau = transcript.squeeze(b"t")?;
    let tau_coords = PowPolynomial::new(&tau, num_rounds_sc).coordinates();

    // absorb the claimed evaluations into the transcript
    self.evals_Az_Bz_Cz_at_tau.iter().for_each(|evals| {
      transcript.absorb(b"e", &evals.as_slice());
    });

    comms_L_row_col.iter().for_each(|comms| {
      // absorb commitments to L_row and L_col in the transcript
      transcript.absorb(b"e", &comms.as_slice());
    });

    // Batch at tau for each instance
    let c = transcript.squeeze(b"c")?;

    let evals_Mz: Vec<_> = comms_Az_Bz_Cz
      .iter()
      .zip(self.evals_Az_Bz_Cz_at_tau.iter())
      .map(|(comm_Az_Bz_Cz, evals_Az_Bz_Cz_at_tau)| {
        let u = PolyEvalInstance::<G>::batch(
          comm_Az_Bz_Cz.as_slice(),
          &tau_coords,
          evals_Az_Bz_Cz_at_tau.as_slice(),
          &c,
        );
        u.e
      })
      .collect();

    let gamma = transcript.squeeze(b"g")?;
    let r = transcript.squeeze(b"r")?;

    comms_mem_oracles.iter().for_each(|comms| {
      transcript.absorb(b"l", &comms.as_slice());
    });

    let num_instances = U.len();
    let num_claims = num_instances * 9;

    let rho = transcript.squeeze(b"r")?;
    let s = transcript.squeeze(b"r")?;
    let coeffs = powers::<G>(&s, num_claims);

    // Scale initial claims by 2^{log(N)-log(Ni)}
    let claim = coeffs
      .chunks_exact(9)
      .zip(evals_Mz.iter())
      .zip(vk.S_comm.iter())
      .map(|((coeffs, eval_Mz), s_comm)| {
        let scaling = 1 << (num_rounds_sc - s_comm.N.log_2()) as u64;
        G::Scalar::from(scaling) * (coeffs[7] + coeffs[8]) * eval_Mz
      })
      .sum::<G::Scalar>();

    // verify sc
    let (claim_sc_final, rand_sc) = self.sc.verify(claim, num_rounds_sc, 3, &mut transcript)?;

    let claim_sc_final_expected = vk
      .num_vars
      .iter()
      .zip(vk.S_comm.iter())
      .zip(coeffs.chunks_exact(9))
      .zip(U.iter())
      .zip(self.evals_Az_Bz_Cz_W_E.iter().cloned())
      .zip(self.evals_L_row_col.iter().cloned())
      .zip(self.evals_mem_oracle.iter().cloned())
      .zip(self.evals_mem_preprocessed.iter().cloned())
      .map(
        |(
          (
            (((((&num_vars, s_comm), coeffs), U), [Az, Bz, Cz, W, E]), [L_row, L_col]),
            [t_plus_r_inv_row, w_plus_r_inv_row, t_plus_r_inv_col, w_plus_r_inv_col],
          ),
          [val_A, val_B, val_C, row, col, ts_row, ts_col],
        )| {
          let num_rounds_i = s_comm.N.log_2();
          // Only consider the last log(Ni) rounds of Sumcheck
          let (_, rand_sc) = rand_sc.split_at(num_rounds_sc - num_rounds_i);

          let eq_rho = {
            let rho_coords = PowPolynomial::new(&rho, num_rounds_i).coordinates();
            EqPolynomial::new(rho_coords).evaluate(rand_sc)
          };

          let eq_tau = {
            let tau_coords = PowPolynomial::new(&tau, num_rounds_i).coordinates();
            EqPolynomial::new(tau_coords).evaluate(rand_sc)
          };

          // Evaluate identity polynomial
          let id = IdentityPolynomial::new(num_rounds_i).evaluate(rand_sc);

          let Z = {
            // rand_sc was padded, so we now remove the padding
            let (factor, rand_sc_unpad) = {
              let l = num_rounds_i - (2 * num_vars).log_2();

              let (rand_sc_lo, rand_sc_hi) = rand_sc.split_at(l);

              let factor = rand_sc_lo
                .iter()
                .fold(G::Scalar::ONE, |acc, r_p| acc * (G::Scalar::ONE - r_p));

              (factor, rand_sc_hi)
            };

            let X = {
              // constant term
              let mut poly_X = vec![(0, U.u)];
              //remaining inputs
              poly_X.extend(
                (0..U.X.len())
                  .map(|i| (i + 1, U.X[i]))
                  .collect::<Vec<(usize, G::Scalar)>>(),
              );
              SparsePolynomial::new(num_vars.log_2(), poly_X).evaluate(&rand_sc_unpad[1..])
            };

            // W was evaluated as if it was padded to logNi variables,
            // so we don't multiply it by (1-rand_sc_unpad[0])
            W + factor * rand_sc_unpad[0] * X
          };

          let t_plus_r_row = {
            let addr_row = id;
            let val_row = eq_tau;
            let t = addr_row + gamma * val_row;
            t + r
          };

          let w_plus_r_row = {
            let addr_row = row;
            let val_row = L_row;
            let w = addr_row + gamma * val_row;
            w + r
          };

          let t_plus_r_col = {
            let addr_col = id;
            let val_col = Z;
            let t = addr_col + gamma * val_col;
            t + r
          };

          let w_plus_r_col = {
            let addr_col = col;
            let val_col = L_col;
            let w = addr_col + gamma * val_col;
            w + r
          };

          let claim_mem_final_expected: G::Scalar = coeffs[0]
            * (t_plus_r_inv_row - w_plus_r_inv_row)
            + coeffs[1] * (t_plus_r_inv_col - w_plus_r_inv_col)
            + coeffs[2] * (eq_rho * (t_plus_r_inv_row * t_plus_r_row - ts_row))
            + coeffs[3] * (eq_rho * (w_plus_r_inv_row * w_plus_r_row - G::Scalar::ONE))
            + coeffs[4] * (eq_rho * (t_plus_r_inv_col * t_plus_r_col - ts_col))
            + coeffs[5] * (eq_rho * (w_plus_r_inv_col * w_plus_r_col - G::Scalar::ONE));

          let claim_outer_final_expected = coeffs[6] * eq_tau * (Az * Bz - U.u * Cz - E)
            + coeffs[7] * eq_tau * (Az + c * Bz + c * c * Cz);
          let claim_inner_final_expected =
            coeffs[8] * L_row * L_col * (val_A + c * val_B + c * c * val_C);

          claim_mem_final_expected + claim_outer_final_expected + claim_inner_final_expected
        },
      )
      .sum::<G::Scalar>();

    if claim_sc_final_expected != claim_sc_final {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let evals_vec = self
      .evals_Az_Bz_Cz_W_E
      .iter()
      .zip(self.evals_L_row_col.iter())
      .zip(self.evals_mem_oracle.iter())
      .zip(self.evals_mem_preprocessed.iter())
      .map(
        |(((Az_Bz_Cz_W_E, L_row_col), mem_oracles), mem_preprocessed)| {
          Az_Bz_Cz_W_E
            .iter()
            .chain(L_row_col)
            .chain(mem_oracles)
            .chain(mem_preprocessed)
            .cloned()
            .collect::<Vec<_>>()
        },
      )
      .collect::<Vec<_>>();

    let comms_vec = comms_Az_Bz_Cz
      .iter()
      .zip(U.iter())
      .zip(comms_L_row_col.iter())
      .zip(comms_mem_oracles.iter())
      .zip(vk.S_comm.iter())
      .flat_map(|((((Az_Bz_Cz, U), L_row_col), mem_oracles), S_comm)| {
        Az_Bz_Cz
          .iter()
          .chain([&U.comm_W, &U.comm_E])
          .chain(L_row_col)
          .chain(mem_oracles)
          .chain([
            &S_comm.comm_val_A,
            &S_comm.comm_val_B,
            &S_comm.comm_val_C,
            &S_comm.comm_row,
            &S_comm.comm_col,
            &S_comm.comm_ts_row,
            &S_comm.comm_ts_col,
          ])
      })
      .cloned()
      .collect::<Vec<_>>();

    evals_vec.iter().for_each(|evals| {
      transcript.absorb(b"e", &evals.as_slice()); // comm_vec is already in the transcript
    });

    // Rescale all evaluations by L_0(rand_sc_lo)
    let evals_vec = evals_vec
      .into_iter()
      .zip(vk.S_comm.iter())
      .flat_map(|(evals, s_comm)| {
        let Ni = s_comm.N;
        let (rand_sc_lo, _) = rand_sc.split_at(num_rounds_sc - Ni.log_2());
        let scaling = rand_sc_lo
          .iter()
          .fold(G::Scalar::ONE, |acc, r| acc * (G::Scalar::ONE - r));
        evals.into_iter().map(move |eval| scaling * eval)
      })
      .collect::<Vec<_>>();

    let c = transcript.squeeze(b"c")?;
    let u: PolyEvalInstance<G> = PolyEvalInstance::batch(&comms_vec, &rand_sc, &evals_vec, &c);
    // verify
    EE::verify(
      &vk.vk_ee,
      &mut transcript,
      &u.c,
      &rand_sc,
      &u.e,
      &self.eval_arg,
    )?;

    Ok(())
  }
}

impl<G: Group, EE: EvaluationEngineTrait<G>> BatchedRelaxedR1CSSNARK<G, EE>
where
  <G::Scalar as PrimeField>::Repr: Abomonation,
{
  /// Runs the batched Sumcheck protocol for the claims of multiple instance of possibly different sizes.
  ///
  /// # Details
  ///
  /// In order to avoid padding all polynomials to the same maximum size, we adopt the following strategy.
  ///
  /// Let n be the number of variables for the largest instance,
  /// and let m be the number of variables for a shorter one.
  /// Let P(X_{0},...,X_{m-1}) be one of the MLEs of the short instance, which has been committed to
  /// by taking the MSM of its evaluations with the first 2^m basis points of the commitment key.
  ///
  /// This Sumcheck prover will interpret it as the polynomial
  ///   P'(X_{0},...,X_{n-1}) = P(X_{n-m},...,X_{n-1}),
  /// whose MLE evaluations over {0,1}^m is equal to 2^{n-m} repetitions of the evaluations of P.
  ///
  /// In order to account for these "imagined" repetitions, the initial claims for this short instances
  /// are scaled by 2^{n-m}.
  ///
  /// For the first n-m rounds, the univariate polynomials relating to this shorter claim will be constant,
  /// and equal to the initial claims, scaled by 2^{n-m-i}, where i is the round number.
  /// By definition, P' does not depend on X_i, so binding P' to r_i has no effect on the evaluations.
  /// The Sumcheck prover will then interpret the polynomial P' as having half as many repetitions
  /// in the next round.
  ///
  /// When we get to round n-m, the Sumcheck proceeds as usual since the polynomials are the expected size
  /// for the round.
  ///
  /// Note that at the end of the protocol, the prover returns the evaluation
  ///   u' = P'(r_{0},...,r_{n-1}) = P(r_{n-m},...,r_{n-1})
  /// However, the polynomial we actually committed to over {0,1}^n is
  ///   P''(X_{0},...,X_{n-1}) = L_0(X_{0},...,X_{n-m-1}) * P(X_{n-m},...,X_{n-1})
  /// The SNARK prover/verifier will need to rescale the evaluation by the first Lagrange polynomial
  ///   u'' = L_0(r_{0},...,r_{n-m-1}) * u'
  /// in order batch all evaluations with a single PCS call.
  fn prove_helper<T1, T2, T3>(
    num_rounds: usize,
    mut mem: Vec<T1>,
    mut outer: Vec<T2>,
    mut inner: Vec<T3>,
    transcript: &mut G::TE,
  ) -> Result<
    (
      SumcheckProof<G>,
      Vec<G::Scalar>,
      Vec<Vec<Vec<G::Scalar>>>,
      Vec<Vec<Vec<G::Scalar>>>,
      Vec<Vec<Vec<G::Scalar>>>,
    ),
    NovaError,
  >
  where
    T1: SumcheckEngine<G>,
    T2: SumcheckEngine<G>,
    T3: SumcheckEngine<G>,
  {
    // sanity checks
    let num_instances = mem.len();
    assert_eq!(outer.len(), num_instances);
    assert_eq!(inner.len(), num_instances);

    mem.iter_mut().for_each(|inst| {
      assert!(inst.size().is_power_of_two());
    });
    outer.iter().for_each(|inst| {
      assert!(inst.size().is_power_of_two());
    });
    inner.iter().for_each(|inst| {
      assert!(inst.size().is_power_of_two());
    });

    let degree = mem[0].degree();
    assert!(mem.iter().all(|inst| inst.degree() == degree));
    assert!(outer.iter().all(|inst| inst.degree() == degree));
    assert!(inner.iter().all(|inst| inst.degree() == degree));

    // these claims are already added to the transcript, so we do not need to add
    let claims = mem
      .iter()
      .zip(outer.iter())
      .zip(inner.iter())
      .flat_map(|((mem, outer), inner)| {
        Self::scaled_claims(mem, num_rounds)
          .into_iter()
          .chain(Self::scaled_claims(outer, num_rounds))
          .chain(Self::scaled_claims(inner, num_rounds))
      })
      .collect::<Vec<G::Scalar>>();

    let s = transcript.squeeze(b"r")?;
    let coeffs = powers::<G>(&s, claims.len());

    // compute the joint claim
    let claim = claims
      .iter()
      .zip(coeffs.iter())
      .map(|(c_1, c_2)| *c_1 * c_2)
      .sum();

    let mut e = claim;
    let mut r: Vec<G::Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly<G::Scalar>> = Vec::new();

    for i in 0..num_rounds {
      let remaining_variables = num_rounds - i;

      let evals = mem
        .par_iter()
        .zip(outer.par_iter())
        .zip(inner.par_iter())
        .flat_map(|((mem, outer), inner)| {
          let (evals_mem, (evals_outer, evals_inner)) = rayon::join(
            || Self::get_evals(mem, remaining_variables),
            || {
              rayon::join(
                || Self::get_evals(outer, remaining_variables),
                || Self::get_evals(inner, remaining_variables),
              )
            },
          );
          evals_mem
            .into_par_iter()
            .chain(evals_outer.into_par_iter())
            .chain(evals_inner.into_par_iter())
        })
        .collect::<Vec<_>>();

      assert_eq!(evals.len(), claims.len());

      let evals_combined_0 = (0..evals.len()).map(|i| evals[i][0] * coeffs[i]).sum();
      let evals_combined_2 = (0..evals.len()).map(|i| evals[i][1] * coeffs[i]).sum();
      let evals_combined_3 = (0..evals.len()).map(|i| evals[i][2] * coeffs[i]).sum();

      let evals = vec![
        evals_combined_0,
        e - evals_combined_0,
        evals_combined_2,
        evals_combined_3,
      ];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      transcript.absorb(b"p", &poly);

      // derive the verifier's challenge for the next round
      let r_i = transcript.squeeze(b"c")?;
      r.push(r_i);

      mem
        .par_iter_mut()
        .zip(outer.par_iter_mut())
        .zip(inner.par_iter_mut())
        .for_each(|((mem, outer), inner)| {
          rayon::join(
            || Self::bind(mem, remaining_variables, &r_i),
            || {
              rayon::join(
                || Self::bind(outer, remaining_variables, &r_i),
                || Self::bind(inner, remaining_variables, &r_i),
              )
            },
          );
        });

      e = poly.evaluate(&r_i);
      cubic_polys.push(poly.compress());
    }

    let claims_outer = outer.into_iter().map(|inst| inst.final_claims()).collect();
    let claims_inner = inner.into_iter().map(|inst| inst.final_claims()).collect();
    let claims_mem = mem.into_iter().map(|inst| inst.final_claims()).collect();

    Ok((
      SumcheckProof::new(cubic_polys),
      r,
      claims_outer,
      claims_inner,
      claims_mem,
    ))
  }

  // When the size of the current round is larger than the instance's size,
  // the evaluations are constant and equal to the initial claims, appropriately
  // scaled to the current round number.
  fn get_evals<T: SumcheckEngine<G>>(inst: &T, remaining_variables: usize) -> Vec<Vec<G::Scalar>> {
    let expected_current_size = 1 << remaining_variables;
    if inst.size() != expected_current_size {
      let deg = inst.degree();

      Self::scaled_claims(inst, remaining_variables - 1)
        .into_iter()
        .map(|scaled_claim| vec![scaled_claim; deg])
        .collect()
    } else {
      inst.evaluation_points()
    }
  }

  // When the size of the current round size is larger than the instance's size,
  // binding the polynomials to r has no effect on the polynomial that we imagine repeats.
  fn bind<T: SumcheckEngine<G>>(inst: &mut T, remaining_variables: usize, r: &G::Scalar) {
    let expected_current_size = 1 << remaining_variables;
    if inst.size() == expected_current_size {
      inst.bound(r)
    }
  }

  // In the current round, if the polynomials in the instance are smaller than the expected size,
  // the claims are equal to the initial ones, scaled by expected_size/round_size to
  // account for the imagined repetitions of the input polynomials.
  fn scaled_claims<T: SumcheckEngine<G>>(inst: &T, remaining_variables: usize) -> Vec<G::Scalar> {
    let expected_current_size = 1 << remaining_variables;
    let inst_size = inst.size();
    let num_repetitions = expected_current_size / inst_size;
    let scaling = G::Scalar::from(num_repetitions as u64);
    inst
      .initial_claims()
      .iter()
      .map(|claim| scaling * claim)
      .collect()
  }
}
