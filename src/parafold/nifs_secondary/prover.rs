use ff::{Field, PrimeField};
use itertools::zip_eq;
use rayon::prelude::*;

use crate::{Commitment, CommitmentKey, zip_with};
use crate::constants::NUM_CHALLENGE_BITS;
use crate::errors::NovaError::{ProofVerifyError, UnSatIndex};
use crate::parafold::hash::HashElement;
use crate::parafold::nifs::compute_fold_proof;
use crate::parafold::nifs_secondary::{NUM_IO_SECONDARY, RelaxedSecondaryR1CSInstance};
use crate::parafold::transcript::prover::Transcript;
use crate::r1cs::R1CSShape;
use crate::supernova::error::SuperNovaError;
use crate::traits::{CurveCycleEquipped, Engine};
use crate::traits::commitment::CommitmentEngineTrait;

/// A full Relaxed-R1CS accumulator for a circuit
#[derive(Debug, PartialEq, Eq)]
pub struct RelaxedSecondaryR1CS<E: CurveCycleEquipped> {
  instance: RelaxedSecondaryR1CSInstance<E>,
  W: Vec<E::Base>,
  E: Vec<E::Base>,
}

impl<E: CurveCycleEquipped> RelaxedSecondaryR1CS<E> {
  pub fn new(shape: &R1CSShape<E::Secondary>) -> Self {
    assert_eq!(shape.num_io, NUM_IO_SECONDARY);
    Self {
      instance: RelaxedSecondaryR1CSInstance {
        u: E::Base::ZERO,
        X: vec![E::Base::ZERO; NUM_IO_SECONDARY],
        W: Commitment::<E::Secondary>::default(),
        E: Commitment::<E::Secondary>::default(),
      },
      W: vec![E::Base::ZERO; shape.num_vars],
      E: vec![E::Base::ZERO; shape.num_cons],
    }
  }

  pub fn instance(&self) -> &RelaxedSecondaryR1CSInstance<E> {
    &self.instance
  }

  pub fn fold(
    &mut self,
    ck: &CommitmentKey<E::Secondary>,
    shape: &R1CSShape<E::Secondary>,
    X_new: &[E::Base],
    W_new: &[E::Base],
    transcript: &mut Transcript<E>,
  ) {
    // TODO: Parallelize both of these operations
    let W_comm_new = { <E::Secondary as Engine>::CE::commit(ck, W_new) };
    let (T, T_comm) = {
      compute_fold_proof(
        ck,
        shape,
        self.instance.u,
        &self.instance.X,
        &self.W,
        None,
        X_new,
        W_new,
      )
    };

    transcript.absorb(HashElement::CommitmentSecondary(W_comm_new));
    transcript.absorb(HashElement::CommitmentSecondary(T_comm));

    // TODO: Squeeze
    let r_bits = transcript.squeeze_bits(NUM_CHALLENGE_BITS);
    let r = bits_le_to_scalar::<E::Base>(&r_bits);

    self
      .W
      .par_iter_mut()
      .zip_eq(W_new.par_iter())
      .for_each(|(w, w_new)| *w += r * w_new);
    self
      .E
      .par_iter_mut()
      .zip_eq(T.par_iter())
      .for_each(|(e, t)| *e += r * t);

    // For non-relaxed instances, u_new = 1
    self.instance.u += r;
    self.instance.X = zip_eq(&self.instance.X, X_new)
      .map(|(x, x_new)| *x + r * x_new)
      .collect();
    self.instance.W = self.instance.W + W_comm_new * r;
    self.instance.E = self.instance.E + T_comm * r;
  }

  pub fn merge(
    ck: &CommitmentKey<E::Secondary>,
    shape: &R1CSShape<E::Secondary>,
    acc_L: Self,
    acc_R: Self,
    transcript: &mut Transcript<E>,
  ) -> Self {
    let (T, T_comm) = compute_fold_proof(
      ck,
      shape,
      acc_L.instance.u,
      &acc_L.instance.X,
      &acc_L.W,
      Some(acc_R.instance.u),
      &acc_R.instance.X,
      &acc_R.W,
    );

    transcript.absorb(HashElement::CommitmentSecondary(T_comm));
    let r_bits = transcript.squeeze_bits(NUM_CHALLENGE_BITS);
    let r = bits_le_to_scalar::<E::Base>(&r_bits);

    let instance = {
      let u = acc_L.instance.u + r * acc_R.instance.u;
      let X = zip_eq(acc_L.instance.X, acc_R.instance.X)
        .map(|(x_L, x_R)| x_L + r * x_R)
        .collect();

      let W = acc_L.instance.W + acc_R.instance.W * r;
      let E_tmp = T_comm + acc_R.instance.E * r;
      let E = acc_L.instance.E + E_tmp * r;

      RelaxedSecondaryR1CSInstance { u, X, W, E }
    };

    let W = zip_with!(
      (acc_L.W.into_par_iter(), acc_R.W.par_iter()),
      |w_L, w_R| w_L + r * w_R
    )
    .collect();

    let E = zip_with!(
      (acc_L.E.into_par_iter(), T.par_iter(), acc_R.E.par_iter()),
      |e_L, t, e_R| e_L + r * (*t + r * e_R)
    )
    .collect();

    Self { instance, W, E }
  }
  pub fn verify(
    &self,
    ck: &CommitmentKey<E::Secondary>,
    shape: &R1CSShape<E::Secondary>,
  ) -> Result<(), SuperNovaError> {
    let E_expected = shape.compute_E(&self.W, &self.instance.u, &self.instance.X)?;

    zip_eq(&self.E, &E_expected)
      .enumerate()
      .try_for_each(|(i, (e, e_expected))| {
        if e != e_expected {
          Err(UnSatIndex(i))
        } else {
          Ok(())
        }
      })?;

    let W_comm = <E::Secondary as Engine>::CE::commit(ck, &self.W);
    if W_comm != self.instance.W {
      return Err(SuperNovaError::NovaError(ProofVerifyError));
    }

    let E_comm = <E::Secondary as Engine>::CE::commit(ck, &self.E);

    if E_comm != self.instance.E {
      return Err(SuperNovaError::NovaError(ProofVerifyError));
    }
    Ok(())
  }
}

fn bits_le_to_scalar<F: PrimeField>(bits: &[bool]) -> F {
  bits.iter().rev().fold(F::ZERO, |mut acc: F, bit| {
    acc = acc.double();
    if *bit {
      acc += F::ONE;
    }
    acc
  })
}
