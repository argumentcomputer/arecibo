//! This module defines R1CS related types and a folding scheme for Relaxed R1CS
mod sparse;
#[cfg(test)]
pub(crate) mod util;

use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  gadgets::{
    nonnative::{bignat::nat_to_limbs, util::f_to_nat},
    utils::scalar_as_base,
  },
  traits::{
    commitment::CommitmentEngineTrait, AbsorbInROTrait, Group, ROTrait, TranscriptReprTrait,
  },
  Commitment, CommitmentKey, CE,
};
use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use core::cmp::max;
use ff::Field;
use once_cell::sync::OnceCell;

use rayon::prelude::*;
use serde::{Deserialize, Serialize};

pub(crate) use self::sparse::SparseMatrix;

/// A type that holds the shape of the R1CS matrices
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
#[abomonation_bounds(where <G::Scalar as ff::PrimeField>::Repr: Abomonation)]
pub struct R1CSShape<G: Group> {
  pub(crate) num_cons: usize,
  pub(crate) num_vars: usize,
  pub(crate) num_io: usize,
  pub(crate) A: SparseMatrix<G::Scalar>,
  pub(crate) B: SparseMatrix<G::Scalar>,
  pub(crate) C: SparseMatrix<G::Scalar>,
  #[abomonation_skip]
  #[serde(skip, default = "OnceCell::new")]
  pub(crate) digest: OnceCell<G::Scalar>,
}

impl<G: Group> SimpleDigestible for R1CSShape<G> {}

/// A type that holds a witness for a given R1CS instance
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R1CSWitness<G: Group> {
  pub(crate) W: Vec<G::Scalar>,
}

/// A type that holds an R1CS instance
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct R1CSInstance<G: Group> {
  pub(crate) comm_W: Commitment<G>,
  /// This is intended to be a buffer for `WitnessViewCS`, which has an extra allocated one variable.
  /// It ends up working out, and we use the extra slot for `G::Scalar::ONE` anyways
  ///
  /// We refer to `one_and_X[1..]` as just `X`
  ///
  /// ## TODO:
  /// **MUST ASSERT THAT `one_and_X[0] == G::Scalar::ONE`**
  pub(crate) one_and_X: Vec<G::Scalar>,
}

/// A type that holds a witness for a given Relaxed R1CS instance
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelaxedR1CSWitness<G: Group> {
  pub(crate) W: Vec<G::Scalar>,
  pub(crate) E: Vec<G::Scalar>,
}

/// A type that holds a Relaxed R1CS instance
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RelaxedR1CSInstance<G: Group> {
  pub(crate) comm_W: Commitment<G>,
  pub(crate) comm_E: Commitment<G>,
  /// This is intended to be a buffer for `WitnessViewCS`, which has an extra allocated one variable.
  /// It ends up working out, and we use the extra slot for `u`
  ///
  /// We refer to `u_and_X[1..]` as just `X`
  pub(crate) u_and_X: Vec<G::Scalar>,
}

/// A type for functions that hints commitment key sizing by returning the floor of the number of required generators.
pub type CommitmentKeyHint<G> = dyn Fn(&R1CSShape<G>) -> usize;

/// Generates public parameters for a Rank-1 Constraint System (R1CS).
///
/// This function takes into consideration the shape of the R1CS matrices and a hint function
/// for the number of generators. It returns a `CommitmentKey`.
///
/// # Arguments
///
/// * `S`: The shape of the R1CS matrices.
/// * `ck_floor`: A function that provides a floor for the number of generators. A good function to
///   provide is the `commitment_key_floor` field in the trait `RelaxedR1CSSNARKTrait`.
///
pub fn commitment_key<G: Group>(
  S: &R1CSShape<G>,
  ck_floor: &CommitmentKeyHint<G>,
) -> CommitmentKey<G> {
  let size = commitment_key_size(S, ck_floor);
  G::CE::setup(b"ck", size)
}

/// Computes the number of generators required for the commitment key corresponding to shape `S`.
pub fn commitment_key_size<G: Group>(S: &R1CSShape<G>, ck_floor: &CommitmentKeyHint<G>) -> usize {
  let num_cons = S.num_cons;
  let num_vars = S.num_vars;
  let ck_hint = ck_floor(S);
  max(max(num_cons, num_vars), ck_hint)
}

impl<G: Group> R1CSShape<G> {
  /// Create an object of type `R1CSShape` from the explicitly specified R1CS matrices
  pub fn new(
    num_cons: usize,
    num_vars: usize,
    num_io: usize,
    A: SparseMatrix<G::Scalar>,
    B: SparseMatrix<G::Scalar>,
    C: SparseMatrix<G::Scalar>,
  ) -> Result<R1CSShape<G>, NovaError> {
    let is_valid = |num_cons: usize,
                    num_vars: usize,
                    num_io: usize,
                    M: &SparseMatrix<G::Scalar>|
     -> Result<Vec<()>, NovaError> {
      M.iter()
        .map(|(row, col, _val)| {
          if row >= num_cons || col > num_io + num_vars {
            Err(NovaError::InvalidIndex)
          } else {
            Ok(())
          }
        })
        .collect::<Result<Vec<()>, NovaError>>()
    };

    is_valid(num_cons, num_vars, num_io, &A)?;
    is_valid(num_cons, num_vars, num_io, &B)?;
    is_valid(num_cons, num_vars, num_io, &C)?;

    // We require the number of public inputs/outputs to be even
    if num_io % 2 != 0 {
      return Err(NovaError::OddInputLength);
    }

    Ok(R1CSShape {
      num_cons,
      num_vars,
      num_io,
      A,
      B,
      C,
      digest: OnceCell::new(),
    })
  }

  /// returnd the digest of the `R1CSShape`
  pub fn digest(&self) -> G::Scalar {
    self
      .digest
      .get_or_try_init(|| DigestComputer::new(self).digest())
      .cloned()
      .expect("Failure retrieving digest")
  }

  // Checks regularity conditions on the R1CSShape, required in Spartan-class SNARKs
  // Returns false if num_cons, num_vars, or num_io are not powers of two, or if num_io > num_vars
  #[inline]
  pub(crate) fn is_regular_shape(&self) -> bool {
    let cons_valid = self.num_cons.next_power_of_two() == self.num_cons;
    let vars_valid = self.num_vars.next_power_of_two() == self.num_vars;
    let io_valid = self.num_io.next_power_of_two() == self.num_io;
    let io_lt_vars = self.num_io < self.num_vars;
    cons_valid && vars_valid && io_valid && io_lt_vars
  }

  pub(crate) fn multiply_vec(
    &self,
    z: &[G::Scalar],
  ) -> Result<(Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>), NovaError> {
    if z.len() != self.num_io + self.num_vars + 1 {
      return Err(NovaError::InvalidWitnessLength);
    }

    let (Az, (Bz, Cz)) = rayon::join(
      || self.A.multiply_vec(z),
      || rayon::join(|| self.B.multiply_vec(z), || self.C.multiply_vec(z)),
    );

    Ok((Az, Bz, Cz))
  }

  pub(crate) fn multiply_witness(
    &self,
    W: &[G::Scalar],
    u_and_X: &[G::Scalar],
  ) -> Result<(Vec<G::Scalar>, Vec<G::Scalar>, Vec<G::Scalar>), NovaError> {
    if u_and_X.len() != self.num_io + 1 || W.len() != self.num_vars {
      return Err(NovaError::InvalidWitnessLength);
    }

    let (Az, (Bz, Cz)) = rayon::join(
      || self.A.multiply_witness(W, u_and_X),
      || {
        rayon::join(
          || self.B.multiply_witness(W, u_and_X),
          || self.C.multiply_witness(W, u_and_X),
        )
      },
    );

    Ok((Az, Bz, Cz))
  }

  /// Checks if the Relaxed R1CS instance is satisfiable given a witness and its shape
  pub fn is_sat_relaxed(
    &self,
    ck: &CommitmentKey<G>,
    U: &RelaxedR1CSInstance<G>,
    W: &RelaxedR1CSWitness<G>,
  ) -> Result<(), NovaError> {
    assert_eq!(W.W.len(), self.num_vars);
    assert_eq!(W.E.len(), self.num_cons);
    assert_eq!(U.u_and_X.len(), self.num_io + 1);

    // verify if Az * Bz = u*Cz + E
    let res_eq = {
      let (Az, Bz, Cz) = self.multiply_witness(&W.W, &U.u_and_X)?;
      assert_eq!(Az.len(), self.num_cons);
      assert_eq!(Bz.len(), self.num_cons);
      assert_eq!(Cz.len(), self.num_cons);

      (0..self.num_cons).try_for_each(|i| {
        if Az[i] * Bz[i] != U.u_and_X[0] * Cz[i] + W.E[i] {
          // constraint failed
          Err(NovaError::UnSatIndex(i))
        } else {
          Ok(())
        }
      })
    };
    res_eq?;

    // verify if comm_E and comm_W are commitments to E and W
    let res_comm = {
      let (comm_W, comm_E) =
        rayon::join(|| CE::<G>::commit(ck, &W.W), || CE::<G>::commit(ck, &W.E));
      U.comm_W == comm_W && U.comm_E == comm_E
    };

    if !res_comm {
      return Err(NovaError::UnSat);
    }
    Ok(())
  }

  /// Checks if the R1CS instance is satisfiable given a witness and its shape
  pub fn is_sat(
    &self,
    ck: &CommitmentKey<G>,
    U: &R1CSInstance<G>,
    W: &R1CSWitness<G>,
  ) -> Result<(), NovaError> {
    assert_eq!(W.W.len(), self.num_vars);
    assert_eq!(U.one_and_X.len(), self.num_io + 1);
    assert_eq!(U.one_and_X[0], G::Scalar::ONE);

    // verify if Az * Bz = u*Cz
    let res_eq = {
      let (Az, Bz, Cz) = self.multiply_witness(&W.W, &U.one_and_X)?;
      assert_eq!(Az.len(), self.num_cons);
      assert_eq!(Bz.len(), self.num_cons);
      assert_eq!(Cz.len(), self.num_cons);

      (0..self.num_cons).try_for_each(|i| {
        if Az[i] * Bz[i] != Cz[i] {
          // constraint failed, retrieve constaint name
          Err(NovaError::UnSatIndex(i))
        } else {
          Ok(())
        }
      })
    };
    res_eq?;

    // verify if comm_W is a commitment to W
    if U.comm_W != CE::<G>::commit(ck, &W.W) {
      return Err(NovaError::UnSat);
    }
    Ok(())
  }

  /// A method to compute a commitment to the cross-term `T` given a
  /// Relaxed R1CS instance-witness pair and an R1CS instance-witness pair
  pub fn commit_T(
    &self,
    ck: &CommitmentKey<G>,
    U1: &RelaxedR1CSInstance<G>,
    W1: &RelaxedR1CSWitness<G>,
    U2: &R1CSInstance<G>,
    W2: &R1CSWitness<G>,
  ) -> Result<(Vec<G::Scalar>, Commitment<G>), NovaError> {
    let (AZ_1, BZ_1, CZ_1) = tracing::trace_span!("AZ_1, BZ_1, CZ_1")
      .in_scope(|| self.multiply_witness(&W1.W, &U1.u_and_X))?;

    let (AZ_2, BZ_2, CZ_2) = tracing::trace_span!("AZ_2, BZ_2, CZ_2")
      .in_scope(|| self.multiply_witness(&W2.W, &U2.one_and_X))?;

    let (AZ_1_circ_BZ_2, AZ_2_circ_BZ_1, u_1_cdot_CZ_2, u_2_cdot_CZ_1) =
      tracing::trace_span!("cross terms").in_scope(|| {
        let AZ_1_circ_BZ_2 = (0..AZ_1.len())
          .into_par_iter()
          .map(|i| AZ_1[i] * BZ_2[i])
          .collect::<Vec<G::Scalar>>();
        let AZ_2_circ_BZ_1 = (0..AZ_2.len())
          .into_par_iter()
          .map(|i| AZ_2[i] * BZ_1[i])
          .collect::<Vec<G::Scalar>>();
        let u_1_cdot_CZ_2 = (0..CZ_2.len())
          .into_par_iter()
          .map(|i| U1.u_and_X[0] * CZ_2[i])
          .collect::<Vec<G::Scalar>>();
        let u_2_cdot_CZ_1 = (0..CZ_1.len())
          .into_par_iter()
          .map(|i| CZ_1[i])
          .collect::<Vec<G::Scalar>>();
        (AZ_1_circ_BZ_2, AZ_2_circ_BZ_1, u_1_cdot_CZ_2, u_2_cdot_CZ_1)
      });

    let T = tracing::trace_span!("T").in_scope(|| {
      AZ_1_circ_BZ_2
        .par_iter()
        .zip(&AZ_2_circ_BZ_1)
        .zip(&u_1_cdot_CZ_2)
        .zip(&u_2_cdot_CZ_1)
        .map(|(((a, b), c), d)| *a + *b - *c - *d)
        .collect::<Vec<G::Scalar>>()
    });

    let comm_T = CE::<G>::commit(ck, &T);

    Ok((T, comm_T))
  }

  /// A method to compute a commitment to the cross-term `T` given a
  /// Relaxed R1CS instance-witness pair and an R1CS instance-witness pair
  ///
  /// This is [`R1CSShape::commit_T`] but into a buffer.
  pub fn commit_T_into(
    &self,
    ck: &CommitmentKey<G>,
    U1: &RelaxedR1CSInstance<G>,
    W1: &RelaxedR1CSWitness<G>,
    U2: &R1CSInstance<G>,
    W2: &R1CSWitness<G>,
    T: &mut Vec<G::Scalar>,
  ) -> Result<Commitment<G>, NovaError> {
    let (AZ_1, BZ_1, CZ_1) = tracing::trace_span!("AZ_1, BZ_1, CZ_1")
      .in_scope(|| self.multiply_witness(&W1.W, &U1.u_and_X))?;

    let (AZ_2, BZ_2, CZ_2) = tracing::trace_span!("AZ_2, BZ_2, CZ_2")
      .in_scope(|| self.multiply_witness(&W2.W, &U2.one_and_X))?;

    // this doesn't allocate memory but has bad temporal cache locality -- should test to see which is faster
    T.clear();
    tracing::trace_span!("T").in_scope(|| {
      (0..AZ_1.len())
        .into_par_iter()
        .map(|i| {
          let AZ_1_circ_BZ_2 = AZ_1[i] * BZ_2[i];
          let AZ_2_circ_BZ_1 = AZ_2[i] * BZ_1[i];
          let u_1_cdot_CZ_2 = U1.u_and_X[0] * CZ_2[i];
          AZ_1_circ_BZ_2 + AZ_2_circ_BZ_1 - u_1_cdot_CZ_2 - CZ_1[i]
        })
        .collect_into_vec(T)
    });

    let comm_T = CE::<G>::commit(ck, T);

    Ok(comm_T)
  }

  /// Pads the `R1CSShape` so that the number of variables is a power of two
  /// Renumbers variables to accomodate padded variables
  pub fn pad(&self) -> Self {
    // equalize the number of variables and constraints
    let m = max(self.num_vars, self.num_cons).next_power_of_two();

    // check if the provided R1CSShape is already as required
    if self.num_vars == m && self.num_cons == m {
      return self.clone();
    }

    // check if the number of variables are as expected, then
    // we simply set the number of constraints to the next power of two
    if self.num_vars == m {
      return R1CSShape {
        num_cons: m,
        num_vars: m,
        num_io: self.num_io,
        A: self.A.clone(),
        B: self.B.clone(),
        C: self.C.clone(),
        digest: OnceCell::new(),
      };
    }

    // otherwise, we need to pad the number of variables and renumber variable accesses
    let num_vars_padded = m;
    let num_cons_padded = m;

    let apply_pad = |mut M: SparseMatrix<G::Scalar>| -> SparseMatrix<G::Scalar> {
      M.indices.par_iter_mut().for_each(|c| {
        if *c >= self.num_vars {
          *c += num_vars_padded - self.num_vars
        }
      });

      M.cols += num_vars_padded - self.num_vars;

      let ex = {
        let nnz = M.indptr.last().unwrap();
        vec![*nnz; num_cons_padded - self.num_cons]
      };
      M.indptr.extend(ex);
      M
    };

    let A_padded = apply_pad(self.A.clone());
    let B_padded = apply_pad(self.B.clone());
    let C_padded = apply_pad(self.C.clone());

    R1CSShape {
      num_cons: num_cons_padded,
      num_vars: num_vars_padded,
      num_io: self.num_io,
      A: A_padded,
      B: B_padded,
      C: C_padded,
      digest: OnceCell::new(),
    }
  }
}

impl<G: Group> R1CSWitness<G> {
  /// Produces a default `RelaxedR1CSWitness` given an `R1CSShape`
  pub fn default(S: &R1CSShape<G>) -> R1CSWitness<G> {
    let mut W = vec![G::Scalar::ZERO; S.num_vars];
    W.shrink_to_fit();

    R1CSWitness { W }
  }

  /// A method to create a witness object using a vector of scalars
  pub fn new(S: &R1CSShape<G>, W: Vec<G::Scalar>) -> Result<R1CSWitness<G>, NovaError> {
    if S.num_vars != W.len() {
      Err(NovaError::InvalidWitnessLength)
    } else {
      Ok(R1CSWitness { W })
    }
  }

  /// Commits to the witness using the supplied generators
  pub fn commit(&self, ck: &CommitmentKey<G>) -> Commitment<G> {
    CE::<G>::commit(ck, &self.W)
  }
}

impl<G: Group> R1CSInstance<G> {
  /// Produces a default `R1CSInstance` given `CommitmentKey` and `R1CSShape`
  pub fn default(_ck: &CommitmentKey<G>, S: &R1CSShape<G>) -> R1CSInstance<G> {
    let comm_W = Commitment::<G>::default();
    let mut one_and_X = vec![G::Scalar::ZERO; S.num_io + 1];
    one_and_X[0] = G::Scalar::ONE;
    one_and_X.shrink_to_fit();
    R1CSInstance { comm_W, one_and_X }
  }

  /// A method to create an instance object using consitituent elements
  pub fn new(
    S: &R1CSShape<G>,
    comm_W: Commitment<G>,
    one_and_X: Vec<G::Scalar>,
  ) -> Result<R1CSInstance<G>, NovaError> {
    if S.num_io + 1 != one_and_X.len() || one_and_X[0] != G::Scalar::ONE {
      Err(NovaError::InvalidInputLength)
    } else {
      Ok(R1CSInstance { comm_W, one_and_X })
    }
  }
}

impl<G: Group> AbsorbInROTrait<G> for R1CSInstance<G> {
  fn absorb_in_ro(&self, ro: &mut G::RO) {
    self.comm_W.absorb_in_ro(ro);
    // make sure to skip the one allocation
    for x in &self.one_and_X[1..] {
      ro.absorb(scalar_as_base::<G>(*x));
    }
  }
}

impl<G: Group> RelaxedR1CSWitness<G> {
  /// Produces a default `RelaxedR1CSWitness` given an `R1CSShape`
  pub fn default(S: &R1CSShape<G>) -> RelaxedR1CSWitness<G> {
    let mut W = vec![G::Scalar::ZERO; S.num_vars];
    W.shrink_to_fit();
    let mut E = vec![G::Scalar::ZERO; S.num_cons];
    E.shrink_to_fit();

    RelaxedR1CSWitness { W, E }
  }

  /// Initializes a new `RelaxedR1CSWitness` from an `R1CSWitness`
  pub fn from_r1cs_witness(S: &R1CSShape<G>, witness: R1CSWitness<G>) -> RelaxedR1CSWitness<G> {
    let mut E = vec![G::Scalar::ZERO; S.num_cons];
    E.shrink_to_fit();

    RelaxedR1CSWitness { W: witness.W, E }
  }

  /// Commits to the witness using the supplied generators
  pub fn commit(&self, ck: &CommitmentKey<G>) -> (Commitment<G>, Commitment<G>) {
    (CE::<G>::commit(ck, &self.W), CE::<G>::commit(ck, &self.E))
  }

  /// Folds an incoming `R1CSWitness` into the current one
  pub fn fold(
    &self,
    W2: &R1CSWitness<G>,
    T: &[G::Scalar],
    r: &G::Scalar,
  ) -> Result<RelaxedR1CSWitness<G>, NovaError> {
    let (W1, E1) = (&self.W, &self.E);
    let W2 = &W2.W;

    if W1.len() != W2.len() {
      return Err(NovaError::InvalidWitnessLength);
    }

    let W = W1
      .par_iter()
      .zip(W2)
      .map(|(a, b)| *a + *r * *b)
      .collect::<Vec<G::Scalar>>();
    let E = E1
      .par_iter()
      .zip(T)
      .map(|(a, b)| *a + *r * *b)
      .collect::<Vec<G::Scalar>>();
    Ok(RelaxedR1CSWitness { W, E })
  }

  /// Mutably folds an incoming `R1CSWitness` into the current one
  pub fn fold_mut(
    &mut self,
    W2: &R1CSWitness<G>,
    T: &[G::Scalar],
    r: &G::Scalar,
  ) -> Result<(), NovaError> {
    if self.W.len() != W2.W.len() {
      return Err(NovaError::InvalidWitnessLength);
    }

    self
      .W
      .par_iter_mut()
      .zip(&W2.W)
      .for_each(|(a, b)| *a += *r * *b);
    self
      .E
      .par_iter_mut()
      .zip(T)
      .for_each(|(a, b)| *a += *r * *b);

    Ok(())
  }

  /// Pads the provided witness to the correct length
  pub fn pad(&self, S: &R1CSShape<G>) -> RelaxedR1CSWitness<G> {
    let mut W = self.W.clone();
    W.extend(vec![G::Scalar::ZERO; S.num_vars - W.len()]);

    let mut E = self.E.clone();
    E.extend(vec![G::Scalar::ZERO; S.num_cons - E.len()]);

    Self { W, E }
  }
}

impl<G: Group> RelaxedR1CSInstance<G> {
  /// Produces a default `RelaxedR1CSInstance` given `R1CSGens` and `R1CSShape`
  pub fn default(_ck: &CommitmentKey<G>, S: &R1CSShape<G>) -> RelaxedR1CSInstance<G> {
    let (comm_W, comm_E) = (Commitment::<G>::default(), Commitment::<G>::default());
    let mut u_and_X = vec![G::Scalar::ZERO; S.num_io + 1];
    u_and_X.shrink_to_fit();

    RelaxedR1CSInstance {
      comm_W,
      comm_E,
      u_and_X,
    }
  }

  /// Initializes a new `RelaxedR1CSInstance` from an `R1CSInstance`
  pub fn from_r1cs_instance(
    _ck: &CommitmentKey<G>,
    S: &R1CSShape<G>,
    instance: R1CSInstance<G>,
  ) -> RelaxedR1CSInstance<G> {
    assert_eq!(S.num_io + 1, instance.one_and_X.len());
    assert_eq!(G::Scalar::ONE, instance.one_and_X[0]);

    RelaxedR1CSInstance {
      comm_W: instance.comm_W,
      comm_E: Commitment::<G>::default(),
      u_and_X: instance.one_and_X,
    }
  }

  /// Initializes a new `RelaxedR1CSInstance` from an `R1CSInstance`
  pub fn from_r1cs_instance_unchecked(
    comm_W: Commitment<G>,
    X: &[G::Scalar],
  ) -> RelaxedR1CSInstance<G> {
    let mut u_and_X = vec![G::Scalar::ONE];
    u_and_X.extend_from_slice(X);

    RelaxedR1CSInstance {
      comm_W,
      comm_E: Commitment::<G>::default(),
      u_and_X,
    }
  }

  /// Folds an incoming `RelaxedR1CSInstance` into the current one
  pub fn fold(
    &self,
    U2: &R1CSInstance<G>,
    comm_T: &Commitment<G>,
    r: &G::Scalar,
  ) -> RelaxedR1CSInstance<G> {
    let (u1_and_X1, comm_W_1, comm_E_1) =
      (&self.u_and_X, &self.comm_W.clone(), &self.comm_E.clone());
    let (one_and_X2, comm_W_2) = (&U2.one_and_X, &U2.comm_W);

    // weighted sum of X, comm_W, comm_E, and u
    let u_and_X = u1_and_X1
      .par_iter()
      .zip(one_and_X2)
      .map(|(a, b)| *a + *r * *b)
      .collect::<Vec<G::Scalar>>();
    let comm_W = *comm_W_1 + *comm_W_2 * *r;
    let comm_E = *comm_E_1 + *comm_T * *r;

    RelaxedR1CSInstance {
      comm_W,
      comm_E,
      u_and_X,
    }
  }

  /// Mutably folds an incoming `RelaxedR1CSInstance` into the current one
  pub fn fold_mut(&mut self, U2: &R1CSInstance<G>, comm_T: &Commitment<G>, r: &G::Scalar) {
    let (one_and_X2, comm_W_2) = (&U2.one_and_X, &U2.comm_W);

    // weighted sum of X, comm_W, comm_E, and u
    self
      .u_and_X
      .par_iter_mut()
      .zip(one_and_X2)
      .for_each(|(a, b)| {
        *a += *r * *b;
      });
    self.comm_W += *comm_W_2 * *r;
    self.comm_E += *comm_T * *r;
  }
}

impl<G: Group> TranscriptReprTrait<G> for RelaxedR1CSInstance<G> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    [
      self.comm_W.to_transcript_bytes(),
      self.comm_E.to_transcript_bytes(),
      self.u_and_X.as_slice().to_transcript_bytes(),
    ]
    .concat()
  }
}

impl<G: Group> AbsorbInROTrait<G> for RelaxedR1CSInstance<G> {
  fn absorb_in_ro(&self, ro: &mut G::RO) {
    self.comm_W.absorb_in_ro(ro);
    self.comm_E.absorb_in_ro(ro);
    ro.absorb(scalar_as_base::<G>(self.u_and_X[0]));

    // absorb each element of self.X in bignum format
    for x in &self.u_and_X[1..] {
      let limbs: Vec<G::Scalar> = nat_to_limbs(&f_to_nat(x), BN_LIMB_WIDTH, BN_N_LIMBS).unwrap();
      for limb in limbs {
        ro.absorb(scalar_as_base::<G>(limb));
      }
    }
  }
}

/// Return an instance and witness, given a shape, ck, and the needed vectors.
pub fn instance_and_witness<G: Group>(
  shape: &R1CSShape<G>,
  ck: &CommitmentKey<G>,
  input_assignment: Vec<G::Scalar>,
  aux_assignment: Vec<G::Scalar>,
) -> Result<(R1CSInstance<G>, R1CSWitness<G>), NovaError> {
  let W = R1CSWitness::<G>::new(shape, aux_assignment)?;
  let comm_W = W.commit(ck);
  let instance = R1CSInstance::<G>::new(shape, comm_W, input_assignment)?;

  Ok((instance, W))
}

/// Empty buffer for `commit_T_into`
pub fn default_T<G: Group>(shape: &R1CSShape<G>) -> Vec<G::Scalar> {
  Vec::with_capacity(shape.num_cons)
}

#[cfg(test)]
mod tests {
  use ff::Field;

  use super::*;
  use crate::{r1cs::sparse::SparseMatrix, traits::Group};

  fn tiny_r1cs<G: Group>(num_vars: usize) -> R1CSShape<G> {
    let one = <G::Scalar as Field>::ONE;
    let (num_cons, num_vars, num_io, A, B, C) = {
      let num_cons = 4;
      let num_io = 2;

      // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
      // The R1CS for this problem consists of the following constraints:
      // `I0 * I0 - Z0 = 0`
      // `Z0 * I0 - Z1 = 0`
      // `(Z1 + I0) * 1 - Z2 = 0`
      // `(Z2 + 5) * 1 - I1 = 0`

      // Relaxed R1CS is a set of three sparse matrices (A B C), where there is a row for every
      // constraint and a column for every entry in z = (vars, u, inputs)
      // An R1CS instance is satisfiable iff:
      // Az \circ Bz = u \cdot Cz + E, where z = (vars, 1, inputs)
      let mut A: Vec<(usize, usize, G::Scalar)> = Vec::new();
      let mut B: Vec<(usize, usize, G::Scalar)> = Vec::new();
      let mut C: Vec<(usize, usize, G::Scalar)> = Vec::new();

      // constraint 0 entries in (A,B,C)
      // `I0 * I0 - Z0 = 0`
      A.push((0, num_vars + 1, one));
      B.push((0, num_vars + 1, one));
      C.push((0, 0, one));

      // constraint 1 entries in (A,B,C)
      // `Z0 * I0 - Z1 = 0`
      A.push((1, 0, one));
      B.push((1, num_vars + 1, one));
      C.push((1, 1, one));

      // constraint 2 entries in (A,B,C)
      // `(Z1 + I0) * 1 - Z2 = 0`
      A.push((2, 1, one));
      A.push((2, num_vars + 1, one));
      B.push((2, num_vars, one));
      C.push((2, 2, one));

      // constraint 3 entries in (A,B,C)
      // `(Z2 + 5) * 1 - I1 = 0`
      A.push((3, 2, one));
      A.push((3, num_vars, one + one + one + one + one));
      B.push((3, num_vars, one));
      C.push((3, num_vars + 2, one));

      (num_cons, num_vars, num_io, A, B, C)
    };

    // create a shape object
    let rows = num_cons;
    let cols = num_vars + num_io + 1;

    let res = R1CSShape::new(
      num_cons,
      num_vars,
      num_io,
      SparseMatrix::new(&A, rows, cols),
      SparseMatrix::new(&B, rows, cols),
      SparseMatrix::new(&C, rows, cols),
    );
    assert!(res.is_ok());
    res.unwrap()
  }

  fn test_pad_tiny_r1cs_with<G: Group>() {
    let padded_r1cs = tiny_r1cs::<G>(3).pad();
    assert!(padded_r1cs.is_regular_shape());

    let expected_r1cs = tiny_r1cs::<G>(4);

    assert_eq!(padded_r1cs, expected_r1cs);
  }

  #[test]
  fn test_pad_tiny_r1cs() {
    test_pad_tiny_r1cs_with::<pasta_curves::pallas::Point>();
    test_pad_tiny_r1cs_with::<crate::provider::bn256_grumpkin::bn256::Point>();
    test_pad_tiny_r1cs_with::<crate::provider::secp_secq::secp256k1::Point>();
  }
}
