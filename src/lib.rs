//! This library implements Nova, a high-speed recursive SNARK.
#![deny(
  warnings,
  unused,
  future_incompatible,
  nonstandard_style,
  rust_2018_idioms,
  missing_docs
)]
#![allow(non_snake_case)]
// #![forbid(unsafe_code)] // Commented for development with `Abomonation`

// private modules
mod bellpepper;
mod circuit;
mod digest;
mod nifs;

// public modules
pub mod constants;
pub mod errors;
pub mod gadgets;
pub mod provider;
pub mod r1cs;
pub mod spartan;
pub mod traits;

pub mod supernova;

use gadgets::lookup::Lookup;
use once_cell::sync::OnceCell;
use traits::snark::RelaxedR1CSSNARKTraitV2;

use crate::digest::{DigestComputer, SimpleDigestible};
use crate::{
  bellpepper::{
    r1cs::{NovaShape, NovaWitness},
    shape_cs::ShapeCS,
    solver::SatisfyingAssignment,
  },
  r1cs::R1CSResult,
};
use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use circuit::{NovaAugmentedCircuit, NovaAugmentedCircuitInputs, NovaAugmentedCircuitParams};
use constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use core::marker::PhantomData;
use errors::NovaError;
use ff::{Field, PrimeField};
use gadgets::utils::scalar_as_base;
use nifs::NIFS;
use r1cs::{
  CommitmentKeyHint, R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness,
};
use serde::{Deserialize, Serialize};
use traits::{
  circuit::StepCircuit,
  commitment::{CommitmentEngineTrait, CommitmentTrait},
  snark::RelaxedR1CSSNARKTrait,
  AbsorbInROTrait, Engine, ROConstants, ROConstantsCircuit, ROTrait,
};

/// A type that holds parameters for the primary and secondary circuits of Nova and SuperNova
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(where <E::Scalar as PrimeField>::Repr: Abomonation)]
pub struct R1CSWithArity<E: Engine> {
  F_arity: usize,
  r1cs_shape: R1CSShape<E>,
}

impl<E: Engine> SimpleDigestible for R1CSWithArity<E> {}

impl<E: Engine> R1CSWithArity<E> {
  /// Create a new `R1CSWithArity`
  pub fn new(r1cs_shape: R1CSShape<E>, F_arity: usize) -> Self {
    Self {
      F_arity,
      r1cs_shape,
    }
  }

  /// Return the [R1CSWithArity]' digest.
  pub fn digest(&self) -> E::Scalar {
    let dc: DigestComputer<'_, <E as Engine>::Scalar, Self> = DigestComputer::new(self);
    dc.digest().expect("Failure in computing digest")
  }
}

/// A type that holds public parameters of Nova
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  <E1::Scalar as PrimeField>::Repr: Abomonation,
  <E2::Scalar as PrimeField>::Repr: Abomonation,
)]
pub struct PublicParams<E1, E2, C1, C2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
{
  F_arity_primary: usize,
  F_arity_secondary: usize,
  ro_consts_primary: ROConstants<E1>,
  ro_consts_circuit_primary: ROConstantsCircuit<E2>,
  ck_primary: CommitmentKey<E1>,
  circuit_shape_primary: R1CSWithArity<E1>,
  ro_consts_secondary: ROConstants<E2>,
  ro_consts_circuit_secondary: ROConstantsCircuit<E1>,
  ck_secondary: CommitmentKey<E2>,
  circuit_shape_secondary: R1CSWithArity<E2>,
  augmented_circuit_params_primary: NovaAugmentedCircuitParams,
  augmented_circuit_params_secondary: NovaAugmentedCircuitParams,
  #[abomonation_skip]
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<E1::Scalar>,
  _p: PhantomData<(C1, C2)>,
}

impl<E1, E2, C1, C2> SimpleDigestible for PublicParams<E1, E2, C1, C2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
{
}

impl<E1, E2, C1, C2> PublicParams<E1, E2, C1, C2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
{
  /// Set up builder to create `PublicParams` for a pair of circuits `C1` and `C2`.
  ///
  /// # Note
  ///
  /// Public parameters set up a number of bases for the homomorphic commitment scheme of Nova.
  ///
  /// Some final compressing SNARKs, like variants of Spartan, use computation commitments that require
  /// larger sizes for these parameters. These SNARKs provide a hint for these values by
  /// implementing `RelaxedR1CSSNARKTrait::ck_floor()`, which can be passed to this function.
  ///
  /// If you're not using such a SNARK, pass `arecibo::traits::snark::default_ck_hint()` instead.
  ///
  /// # Arguments
  ///
  /// * `c_primary`: The primary circuit of type `C1`.
  /// * `c_secondary`: The secondary circuit of type `C2`.
  /// * `ck_hint1`: A `CommitmentKeyHint` for `G1`, which is a function that provides a hint
  ///   for the number of generators required in the commitment scheme for the primary circuit.
  /// * `ck_hint2`: A `CommitmentKeyHint` for `G2`, similar to `ck_hint1`, but for the secondary circuit.
  ///
  /// # Example
  ///
  /// ```rust
  /// # use arecibo::spartan::ppsnark::RelaxedR1CSSNARK;
  /// # use arecibo::provider::ipa_pc::EvaluationEngine;
  /// # use arecibo::provider::{PallasEngine, VestaEngine};
  /// # use arecibo::traits::{circuit::TrivialCircuit, Engine, snark::RelaxedR1CSSNARKTrait};
  /// use arecibo::PublicParams;
  ///
  /// type E1 = PallasEngine;
  /// type E2 = VestaEngine;
  /// type EE<E> = EvaluationEngine<E>;
  /// type SPrime<E> = RelaxedR1CSSNARK<E, EE<E>>;
  ///
  /// let circuit1 = TrivialCircuit::<<E1 as Engine>::Scalar>::default();
  /// let circuit2 = TrivialCircuit::<<E2 as Engine>::Scalar>::default();
  /// // Only relevant for a SNARK using computation commitmnets, pass &(|_| 0)
  /// // or &*nova_snark::traits::snark::default_ck_hint() otherwise.
  /// let ck_hint1 = &*SPrime::<E1, EE<_>>::ck_floor();
  /// let ck_hint2 = &*SPrime::<E2, EE<_>>::ck_floor();
  ///
  /// let pp = PublicParams::setup(&circuit1, &circuit2, ck_hint1, ck_hint2);
  /// ```
  pub fn setup(
    c_primary: &C1,
    c_secondary: &C2,
    ck_hint1: &CommitmentKeyHint<E1>,
    ck_hint2: &CommitmentKeyHint<E2>,
  ) -> Self {
    let augmented_circuit_params_primary =
      NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let augmented_circuit_params_secondary =
      NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);

    let ro_consts_primary: ROConstants<E1> = ROConstants::<E1>::default();
    let ro_consts_secondary: ROConstants<E2> = ROConstants::<E2>::default();

    let F_arity_primary = c_primary.arity();
    let F_arity_secondary = c_secondary.arity();

    // ro_consts_circuit_primary are parameterized by E2 because the type alias uses E2::Base = E1::Scalar
    let ro_consts_circuit_primary: ROConstantsCircuit<E2> = ROConstantsCircuit::<E2>::default();
    let ro_consts_circuit_secondary: ROConstantsCircuit<E1> = ROConstantsCircuit::<E1>::default();

    // Initialize ck for the primary
    let circuit_primary: NovaAugmentedCircuit<'_, E2, C1> = NovaAugmentedCircuit::new(
      &augmented_circuit_params_primary,
      None,
      c_primary,
      ro_consts_circuit_primary.clone(),
    );
    let mut cs: ShapeCS<E1> = ShapeCS::new();
    let _ = circuit_primary.synthesize(&mut cs);
    let (r1cs_shape_primary, ck_primary) = cs.r1cs_shape_and_key(ck_hint1);
    let circuit_shape_primary = R1CSWithArity::new(r1cs_shape_primary, F_arity_primary);

    // Initialize ck for the secondary
    let circuit_secondary: NovaAugmentedCircuit<'_, E1, C2> = NovaAugmentedCircuit::new(
      &augmented_circuit_params_secondary,
      None,
      c_secondary,
      ro_consts_circuit_secondary.clone(),
    );
    let mut cs: ShapeCS<E2> = ShapeCS::new();
    let _ = circuit_secondary.synthesize(&mut cs);
    let (r1cs_shape_secondary, ck_secondary) = cs.r1cs_shape_and_key(ck_hint2);
    let circuit_shape_secondary = R1CSWithArity::new(r1cs_shape_secondary, F_arity_secondary);

    Self {
      F_arity_primary,
      F_arity_secondary,
      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary,
      circuit_shape_primary,
      ro_consts_secondary,
      ro_consts_circuit_secondary,
      ck_secondary,
      circuit_shape_secondary,
      augmented_circuit_params_primary,
      augmented_circuit_params_secondary,
      digest: OnceCell::new(),
      _p: Default::default(),
    }
  }

  /// Retrieve the digest of the public parameters.
  pub fn digest(&self) -> E1::Scalar {
    self
      .digest
      .get_or_try_init(|| DigestComputer::new(self).digest())
      .cloned()
      .expect("Failure in retrieving digest")
  }

  /// Returns the number of constraints in the primary and secondary circuits
  pub const fn num_constraints(&self) -> (usize, usize) {
    (
      self.circuit_shape_primary.r1cs_shape.num_cons,
      self.circuit_shape_secondary.r1cs_shape.num_cons,
    )
  }

  /// Returns the number of variables in the primary and secondary circuits
  pub const fn num_variables(&self) -> (usize, usize) {
    (
      self.circuit_shape_primary.r1cs_shape.num_vars,
      self.circuit_shape_secondary.r1cs_shape.num_vars,
    )
  }
}

/// A resource buffer for [`RecursiveSNARK`] for storing scratch values that are computed by `prove_step`,
/// which allows the reuse of memory allocations and avoids unnecessary new allocations in the critical section.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ResourceBuffer<E: Engine> {
  l_w: Option<R1CSWitness<E>>,
  l_u: Option<R1CSInstance<E>>,

  ABC_Z_1: R1CSResult<E>,
  ABC_Z_2: R1CSResult<E>,

  /// buffer for `commit_T`
  T: Vec<E::Scalar>,
}

/// A SNARK that proves the correct execution of an incremental computation
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RecursiveSNARK<E1, E2, C1, C2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
{
  z0_primary: Vec<E1::Scalar>,
  z0_secondary: Vec<E2::Scalar>,
  r_W_primary: RelaxedR1CSWitness<E1>,
  r_U_primary: RelaxedR1CSInstance<E1>,
  r_W_secondary: RelaxedR1CSWitness<E2>,
  r_U_secondary: RelaxedR1CSInstance<E2>,
  l_w_secondary: R1CSWitness<E2>,
  l_u_secondary: R1CSInstance<E2>,

  /// Buffer for memory needed by the primary fold-step
  buffer_primary: ResourceBuffer<E1>,
  /// Buffer for memory needed by the secondary fold-step
  buffer_secondary: ResourceBuffer<E2>,

  i: usize,
  zi_primary: Vec<E1::Scalar>,
  zi_secondary: Vec<E2::Scalar>,
  _p: PhantomData<(C1, C2)>,
}

impl<E1, E2, C1, C2> RecursiveSNARK<E1, E2, C1, C2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
{
  /// Create new instance of recursive SNARK
  pub fn new(
    pp: &PublicParams<E1, E2, C1, C2>,
    c_primary: &C1,
    c_secondary: &C2,
    z0_primary: &[E1::Scalar],
    z0_secondary: &[E2::Scalar],
  ) -> Result<Self, NovaError> {
    if z0_primary.len() != pp.F_arity_primary || z0_secondary.len() != pp.F_arity_secondary {
      return Err(NovaError::InvalidInitialInputLength);
    }

    let r1cs_primary = &pp.circuit_shape_primary.r1cs_shape;
    let r1cs_secondary = &pp.circuit_shape_secondary.r1cs_shape;

    // base case for the primary
    let mut cs_primary = SatisfyingAssignment::<E1>::new();
    let inputs_primary: NovaAugmentedCircuitInputs<E2> = NovaAugmentedCircuitInputs::new(
      scalar_as_base::<E1>(pp.digest()),
      E1::Scalar::ZERO,
      z0_primary.to_vec(),
      None,
      None,
      None,
      None,
    );

    let circuit_primary: NovaAugmentedCircuit<'_, E2, C1> = NovaAugmentedCircuit::new(
      &pp.augmented_circuit_params_primary,
      Some(inputs_primary),
      c_primary,
      pp.ro_consts_circuit_primary.clone(),
    );
    let zi_primary = circuit_primary.synthesize(&mut cs_primary)?;
    let (u_primary, w_primary) =
      cs_primary.r1cs_instance_and_witness(r1cs_primary, &pp.ck_primary)?;

    // base case for the secondary
    let mut cs_secondary = SatisfyingAssignment::<E2>::new();
    let inputs_secondary: NovaAugmentedCircuitInputs<E1> = NovaAugmentedCircuitInputs::new(
      pp.digest(),
      E2::Scalar::ZERO,
      z0_secondary.to_vec(),
      None,
      None,
      Some(u_primary.clone()),
      None,
    );
    let circuit_secondary: NovaAugmentedCircuit<'_, E1, C2> = NovaAugmentedCircuit::new(
      &pp.augmented_circuit_params_secondary,
      Some(inputs_secondary),
      c_secondary,
      pp.ro_consts_circuit_secondary.clone(),
    );
    let zi_secondary = circuit_secondary.synthesize(&mut cs_secondary)?;
    let (u_secondary, w_secondary) = cs_secondary
      .r1cs_instance_and_witness(&pp.circuit_shape_secondary.r1cs_shape, &pp.ck_secondary)?;

    // IVC proof for the primary circuit
    let l_w_primary = w_primary;
    let l_u_primary = u_primary;
    let r_W_primary = RelaxedR1CSWitness::from_r1cs_witness(r1cs_primary, l_w_primary);
    let r_U_primary = RelaxedR1CSInstance::from_r1cs_instance(
      &pp.ck_primary,
      &pp.circuit_shape_primary.r1cs_shape,
      l_u_primary,
    );

    // IVC proof for the secondary circuit
    let l_w_secondary = w_secondary;
    let l_u_secondary = u_secondary;
    let r_W_secondary = RelaxedR1CSWitness::<E2>::default(r1cs_secondary);
    let r_U_secondary = RelaxedR1CSInstance::<E2>::default(&pp.ck_secondary, r1cs_secondary);

    assert!(
      !(zi_primary.len() != pp.F_arity_primary || zi_secondary.len() != pp.F_arity_secondary),
      "Invalid step length"
    );

    let zi_primary = zi_primary
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<<E1 as Engine>::Scalar>, _>>()?;

    let zi_secondary = zi_secondary
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<<E2 as Engine>::Scalar>, _>>()?;

    let buffer_primary = ResourceBuffer {
      l_w: None,
      l_u: None,
      ABC_Z_1: R1CSResult::default(r1cs_primary.num_cons),
      ABC_Z_2: R1CSResult::default(r1cs_primary.num_cons),
      T: r1cs::default_T::<E1>(r1cs_primary.num_cons),
    };

    let buffer_secondary = ResourceBuffer {
      l_w: None,
      l_u: None,
      ABC_Z_1: R1CSResult::default(r1cs_secondary.num_cons),
      ABC_Z_2: R1CSResult::default(r1cs_secondary.num_cons),
      T: r1cs::default_T::<E2>(r1cs_secondary.num_cons),
    };

    Ok(Self {
      z0_primary: z0_primary.to_vec(),
      z0_secondary: z0_secondary.to_vec(),
      r_W_primary,
      r_U_primary,
      r_W_secondary,
      r_U_secondary,
      l_w_secondary,
      l_u_secondary,

      buffer_primary,
      buffer_secondary,
      i: 0,
      zi_primary,
      zi_secondary,
      _p: Default::default(),
    })
  }

  /// Create a new `RecursiveSNARK` (or updates the provided `RecursiveSNARK`)
  /// by executing a step of the incremental computation
  #[tracing::instrument(skip_all, name = "nova::RecursiveSNARK::prove_step")]
  pub fn prove_step(
    &mut self,
    pp: &PublicParams<E1, E2, C1, C2>,
    c_primary: &C1,
    c_secondary: &C2,
  ) -> Result<(), NovaError> {
    // first step was already done in the constructor
    if self.i == 0 {
      self.i = 1;
      return Ok(());
    }

    // save the inputs before proceeding to the `i+1`th step
    let r_U_primary_i = self.r_U_primary.clone();
    let r_U_secondary_i = self.r_U_secondary.clone();
    let l_u_secondary_i = self.l_u_secondary.clone();

    // fold the secondary circuit's instance
    let nifs_secondary = NIFS::prove_mut(
      &pp.ck_secondary,
      &pp.ro_consts_secondary,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.circuit_shape_secondary.r1cs_shape,
      &mut self.r_U_secondary,
      &mut self.r_W_secondary,
      &self.l_u_secondary,
      &self.l_w_secondary,
      &mut self.buffer_secondary.T,
      &mut self.buffer_secondary.ABC_Z_1,
      &mut self.buffer_secondary.ABC_Z_2,
    )?;

    let mut cs_primary = SatisfyingAssignment::<E1>::with_capacity(
      pp.circuit_shape_primary.r1cs_shape.num_io + 1,
      pp.circuit_shape_primary.r1cs_shape.num_vars,
    );
    let inputs_primary: NovaAugmentedCircuitInputs<E2> = NovaAugmentedCircuitInputs::new(
      scalar_as_base::<E1>(pp.digest()),
      E1::Scalar::from(self.i as u64),
      self.z0_primary.to_vec(),
      Some(self.zi_primary.clone()),
      Some(r_U_secondary_i),
      Some(l_u_secondary_i),
      Some(Commitment::<E2>::decompress(&nifs_secondary.comm_T)?),
    );

    let circuit_primary: NovaAugmentedCircuit<'_, E2, C1> = NovaAugmentedCircuit::new(
      &pp.augmented_circuit_params_primary,
      Some(inputs_primary),
      c_primary,
      pp.ro_consts_circuit_primary.clone(),
    );

    let zi_primary = circuit_primary.synthesize(&mut cs_primary)?;

    let (l_u_primary, l_w_primary) =
      cs_primary.r1cs_instance_and_witness(&pp.circuit_shape_primary.r1cs_shape, &pp.ck_primary)?;

    // fold the primary circuit's instance
    let nifs_primary = NIFS::prove_mut(
      &pp.ck_primary,
      &pp.ro_consts_primary,
      &pp.digest(),
      &pp.circuit_shape_primary.r1cs_shape,
      &mut self.r_U_primary,
      &mut self.r_W_primary,
      &l_u_primary,
      &l_w_primary,
      &mut self.buffer_primary.T,
      &mut self.buffer_primary.ABC_Z_1,
      &mut self.buffer_primary.ABC_Z_2,
    )?;

    let mut cs_secondary = SatisfyingAssignment::<E2>::with_capacity(
      pp.circuit_shape_secondary.r1cs_shape.num_io + 1,
      pp.circuit_shape_secondary.r1cs_shape.num_vars,
    );
    let inputs_secondary: NovaAugmentedCircuitInputs<E1> = NovaAugmentedCircuitInputs::new(
      pp.digest(),
      E2::Scalar::from(self.i as u64),
      self.z0_secondary.to_vec(),
      Some(self.zi_secondary.clone()),
      Some(r_U_primary_i),
      Some(l_u_primary),
      Some(Commitment::<E1>::decompress(&nifs_primary.comm_T)?),
    );

    let circuit_secondary: NovaAugmentedCircuit<'_, E1, C2> = NovaAugmentedCircuit::new(
      &pp.augmented_circuit_params_secondary,
      Some(inputs_secondary),
      c_secondary,
      pp.ro_consts_circuit_secondary.clone(),
    );
    let zi_secondary = circuit_secondary.synthesize(&mut cs_secondary)?;

    let (l_u_secondary, l_w_secondary) = cs_secondary
      .r1cs_instance_and_witness(&pp.circuit_shape_secondary.r1cs_shape, &pp.ck_secondary)
      .map_err(|_e| NovaError::UnSat)?;

    // update the running instances and witnesses
    self.zi_primary = zi_primary
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<<E1 as Engine>::Scalar>, _>>()?;
    self.zi_secondary = zi_secondary
      .iter()
      .map(|v| v.get_value().ok_or(SynthesisError::AssignmentMissing))
      .collect::<Result<Vec<<E2 as Engine>::Scalar>, _>>()?;

    self.l_u_secondary = l_u_secondary;
    self.l_w_secondary = l_w_secondary;

    self.i += 1;

    Ok(())
  }

  /// Verify the correctness of the `RecursiveSNARK`
  pub fn verify(
    &self,
    pp: &PublicParams<E1, E2, C1, C2>,
    num_steps: usize,
    z0_primary: &[E1::Scalar],
    z0_secondary: &[E2::Scalar],
  ) -> Result<(Vec<E1::Scalar>, Vec<E2::Scalar>), NovaError> {
    // number of steps cannot be zero
    let is_num_steps_zero = num_steps == 0;

    // check if the provided proof has executed num_steps
    let is_num_steps_not_match = self.i != num_steps;

    // check if the initial inputs match
    let is_inputs_not_match = self.z0_primary != z0_primary || self.z0_secondary != z0_secondary;

    // check if the (relaxed) R1CS instances have two public outputs
    let is_instance_has_two_outpus = self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2;

    if is_num_steps_zero
      || is_num_steps_not_match
      || is_inputs_not_match
      || is_instance_has_two_outpus
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let (hash_primary, hash_secondary) = {
      let mut hasher = <E2 as Engine>::RO::new(
        pp.ro_consts_secondary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_primary,
      );
      hasher.absorb(pp.digest());
      hasher.absorb(E1::Scalar::from(num_steps as u64));
      for e in z0_primary {
        hasher.absorb(*e);
      }
      for e in &self.zi_primary {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 = <E1 as Engine>::RO::new(
        pp.ro_consts_primary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_secondary,
      );
      hasher2.absorb(scalar_as_base::<E1>(pp.digest()));
      hasher2.absorb(E2::Scalar::from(num_steps as u64));
      for e in z0_secondary {
        hasher2.absorb(*e);
      }
      for e in &self.zi_secondary {
        hasher2.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro(&mut hasher2);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != self.l_u_secondary.X[0]
      || hash_secondary != scalar_as_base::<E2>(self.l_u_secondary.X[1])
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check the satisfiability of the provided instances
    let (res_r_primary, (res_r_secondary, res_l_secondary)) = rayon::join(
      || {
        pp.circuit_shape_primary.r1cs_shape.is_sat_relaxed(
          &pp.ck_primary,
          &self.r_U_primary,
          &self.r_W_primary,
        )
      },
      || {
        rayon::join(
          || {
            pp.circuit_shape_secondary.r1cs_shape.is_sat_relaxed(
              &pp.ck_secondary,
              &self.r_U_secondary,
              &self.r_W_secondary,
            )
          },
          || {
            pp.circuit_shape_secondary.r1cs_shape.is_sat(
              &pp.ck_secondary,
              &self.l_u_secondary,
              &self.l_w_secondary,
            )
          },
        )
      },
    );

    // check the returned res objects
    res_r_primary?;
    res_r_secondary?;
    res_l_secondary?;

    Ok((self.zi_primary.clone(), self.zi_secondary.clone()))
  }

  /// Get the outputs after the last step of computation.
  pub fn outputs(&self) -> (&[E1::Scalar], &[E2::Scalar]) {
    (&self.zi_primary, &self.zi_secondary)
  }

  /// The number of steps which have been executed thus far.
  pub fn num_steps(&self) -> usize {
    self.i
  }
}

/// A type that holds the prover key for `CompressedSNARK`
#[derive(Clone, Debug, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_omit_bounds]
pub struct ProverKey<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  pk_primary: S1::ProverKey,
  pk_secondary: S2::ProverKey,
  _p: PhantomData<(C1, C2)>,
}

/// A type that holds the verifier key for `CompressedSNARK`
#[derive(Debug, Clone, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    C1: StepCircuit<E1::Scalar>,
    C2: StepCircuit<E2::Scalar>,
    S1: RelaxedR1CSSNARKTrait<E1>,
    S2: RelaxedR1CSSNARKTrait<E2>,
    <E1::Scalar as PrimeField>::Repr: Abomonation,
  )]
pub struct VerifierKey<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  F_arity_primary: usize,
  F_arity_secondary: usize,
  ro_consts_primary: ROConstants<E1>,
  ro_consts_secondary: ROConstants<E2>,
  #[abomonate_with(<E1::Scalar as PrimeField>::Repr)]
  pp_digest: E1::Scalar,
  vk_primary: S1::VerifierKey,
  vk_secondary: S2::VerifierKey,
  _p: PhantomData<(C1, C2)>,
}

/// A SNARK that proves the knowledge of a valid `RecursiveSNARK`
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CompressedSNARK<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  r_U_primary: RelaxedR1CSInstance<E1>,
  r_W_snark_primary: S1,

  r_U_secondary: RelaxedR1CSInstance<E2>,
  l_u_secondary: R1CSInstance<E2>,
  nifs_secondary: NIFS<E2>,
  f_W_snark_secondary: S2,

  zn_primary: Vec<E1::Scalar>,
  zn_secondary: Vec<E2::Scalar>,

  _p: PhantomData<(C1, C2)>,
}

impl<E1, E2, C1, C2, S1, S2> CompressedSNARK<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  /// Creates prover and verifier keys for `CompressedSNARK`
  pub fn setup(
    pp: &PublicParams<E1, E2, C1, C2>,
  ) -> Result<
    (
      ProverKey<E1, E2, C1, C2, S1, S2>,
      VerifierKey<E1, E2, C1, C2, S1, S2>,
    ),
    NovaError,
  > {
    let (pk_primary, vk_primary) = S1::setup(&pp.ck_primary, &pp.circuit_shape_primary.r1cs_shape)?;
    let (pk_secondary, vk_secondary) =
      S2::setup(&pp.ck_secondary, &pp.circuit_shape_secondary.r1cs_shape)?;

    let pk = ProverKey {
      pk_primary,
      pk_secondary,
      _p: Default::default(),
    };

    let vk = VerifierKey {
      F_arity_primary: pp.F_arity_primary,
      F_arity_secondary: pp.F_arity_secondary,
      ro_consts_primary: pp.ro_consts_primary.clone(),
      ro_consts_secondary: pp.ro_consts_secondary.clone(),
      pp_digest: pp.digest(),
      vk_primary,
      vk_secondary,
      _p: Default::default(),
    };

    Ok((pk, vk))
  }

  /// Create a new `CompressedSNARK`
  pub fn prove(
    pp: &PublicParams<E1, E2, C1, C2>,
    pk: &ProverKey<E1, E2, C1, C2, S1, S2>,
    recursive_snark: &RecursiveSNARK<E1, E2, C1, C2>,
  ) -> Result<Self, NovaError> {
    // fold the secondary circuit's instance with its running instance
    let (nifs_secondary, (f_U_secondary, f_W_secondary)) = NIFS::prove(
      &pp.ck_secondary,
      &pp.ro_consts_secondary,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.circuit_shape_secondary.r1cs_shape,
      &recursive_snark.r_U_secondary,
      &recursive_snark.r_W_secondary,
      &recursive_snark.l_u_secondary,
      &recursive_snark.l_w_secondary,
    )?;

    // create SNARKs proving the knowledge of f_W_primary and f_W_secondary
    let (r_W_snark_primary, f_W_snark_secondary) = rayon::join(
      || {
        S1::prove(
          &pp.ck_primary,
          &pk.pk_primary,
          &pp.circuit_shape_primary.r1cs_shape,
          &recursive_snark.r_U_primary,
          &recursive_snark.r_W_primary,
        )
      },
      || {
        S2::prove(
          &pp.ck_secondary,
          &pk.pk_secondary,
          &pp.circuit_shape_secondary.r1cs_shape,
          &f_U_secondary,
          &f_W_secondary,
        )
      },
    );

    Ok(Self {
      r_U_primary: recursive_snark.r_U_primary.clone(),
      r_W_snark_primary: r_W_snark_primary?,

      r_U_secondary: recursive_snark.r_U_secondary.clone(),
      l_u_secondary: recursive_snark.l_u_secondary.clone(),
      nifs_secondary,
      f_W_snark_secondary: f_W_snark_secondary?,

      zn_primary: recursive_snark.zi_primary.clone(),
      zn_secondary: recursive_snark.zi_secondary.clone(),

      _p: Default::default(),
    })
  }

  /// Verify the correctness of the `CompressedSNARK`
  pub fn verify(
    &self,
    vk: &VerifierKey<E1, E2, C1, C2, S1, S2>,
    num_steps: usize,
    z0_primary: &[E1::Scalar],
    z0_secondary: &[E2::Scalar],
  ) -> Result<(Vec<E1::Scalar>, Vec<E2::Scalar>), NovaError> {
    // the number of steps cannot be zero
    if num_steps == 0 {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the (relaxed) R1CS instances have two public outputs
    if self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let (hash_primary, hash_secondary) = {
      let mut hasher = <E2 as Engine>::RO::new(
        vk.ro_consts_secondary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * vk.F_arity_primary,
      );
      hasher.absorb(vk.pp_digest);
      hasher.absorb(E1::Scalar::from(num_steps as u64));
      for e in z0_primary {
        hasher.absorb(*e);
      }
      for e in &self.zn_primary {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 = <E1 as Engine>::RO::new(
        vk.ro_consts_primary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * vk.F_arity_secondary,
      );
      hasher2.absorb(scalar_as_base::<E1>(vk.pp_digest));
      hasher2.absorb(E2::Scalar::from(num_steps as u64));
      for e in z0_secondary {
        hasher2.absorb(*e);
      }
      for e in &self.zn_secondary {
        hasher2.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro(&mut hasher2);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != self.l_u_secondary.X[0]
      || hash_secondary != scalar_as_base::<E2>(self.l_u_secondary.X[1])
    {
      return Err(NovaError::ProofVerifyError);
    }

    // fold the secondary's running instance with the last instance to get a folded instance
    let f_U_secondary = self.nifs_secondary.verify(
      &vk.ro_consts_secondary,
      &scalar_as_base::<E1>(vk.pp_digest),
      &self.r_U_secondary,
      &self.l_u_secondary,
    )?;

    // check the satisfiability of the folded instances using
    // SNARKs proving the knowledge of their satisfying witnesses
    let (res_primary, res_secondary) = rayon::join(
      || {
        self
          .r_W_snark_primary
          .verify(&vk.vk_primary, &self.r_U_primary)
      },
      || {
        self
          .f_W_snark_secondary
          .verify(&vk.vk_secondary, &f_U_secondary)
      },
    );

    res_primary?;
    res_secondary?;

    Ok((self.zn_primary.clone(), self.zn_secondary.clone()))
  }
}

/// A type that holds the prover key for `CompressedSNARK`
#[derive(Clone, Debug, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_omit_bounds]
pub struct ProverKeyV2<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTraitV2<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  pk_primary: S1::ProverKey,
  pk_secondary: S2::ProverKey,
  _p: PhantomData<(C1, C2)>,
}

/// A type that holds the verifier key for `CompressedSNARK`
#[derive(Clone, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    C1: StepCircuit<E1::Scalar>,
    C2: StepCircuit<E2::Scalar>,
    S1: RelaxedR1CSSNARKTraitV2<E1>,
    S2: RelaxedR1CSSNARKTrait<E2>,
    <E1::Scalar as PrimeField>::Repr: Abomonation,
  )]
pub struct VerifierKeyV2<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTraitV2<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  F_arity_primary: usize,
  F_arity_secondary: usize,
  ro_consts_primary: ROConstants<E1>,
  ro_consts_secondary: ROConstants<E2>,
  #[abomonate_with(<E1::Scalar as PrimeField>::Repr)]
  pp_digest: E1::Scalar,
  vk_primary: S1::VerifierKey,
  vk_secondary: S2::VerifierKey,
  _p: PhantomData<(C1, C2)>,
}

/// A SNARK that proves the knowledge of a valid `RecursiveSNARK`
/// and support lookup argument
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CompressedSNARKV2<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTraitV2<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  r_U_primary: RelaxedR1CSInstance<E1>,
  r_W_snark_primary: S1,

  r_U_secondary: RelaxedR1CSInstance<E2>,
  l_u_secondary: R1CSInstance<E2>,
  nifs_secondary: NIFS<E2>,
  f_W_snark_secondary: S2,

  zn_primary: Vec<E1::Scalar>,
  zn_secondary: Vec<E2::Scalar>,

  _p: PhantomData<(C1, C2)>,
}

impl<E1, E2, C1, C2, S1, S2> CompressedSNARKV2<E1, E2, C1, C2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C1: StepCircuit<E1::Scalar>,
  C2: StepCircuit<E2::Scalar>,
  S1: RelaxedR1CSSNARKTraitV2<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  /// Creates prover and verifier keys for `CompressedSNARK`
  pub fn setup(
    pp: &PublicParams<E1, E2, C1, C2>,
    initial_table: &Lookup<E1::Scalar>,
  ) -> Result<
    (
      ProverKeyV2<E1, E2, C1, C2, S1, S2>,
      VerifierKeyV2<E1, E2, C1, C2, S1, S2>,
    ),
    NovaError,
  >
  where
    <E1 as Engine>::Scalar: Ord,
  {
    let (pk_primary, vk_primary) = S1::setup(
      &pp.ck_primary,
      &pp.circuit_shape_primary.r1cs_shape,
      initial_table,
    )?;
    let (pk_secondary, vk_secondary) =
      S2::setup(&pp.ck_secondary, &pp.circuit_shape_secondary.r1cs_shape)?;

    let pk = ProverKeyV2 {
      pk_primary,
      pk_secondary,
      _p: Default::default(),
    };

    let vk = VerifierKeyV2 {
      F_arity_primary: pp.F_arity_primary,
      F_arity_secondary: pp.F_arity_secondary,
      ro_consts_primary: pp.ro_consts_primary.clone(),
      ro_consts_secondary: pp.ro_consts_secondary.clone(),
      pp_digest: pp.digest(),
      vk_primary,
      vk_secondary,
      _p: Default::default(),
    };

    Ok((pk, vk))
  }

  /// Create a new `CompressedSNARK`
  pub fn prove(
    pp: &PublicParams<E1, E2, C1, C2>,
    pk: &ProverKeyV2<E1, E2, C1, C2, S1, S2>,
    recursive_snark: &RecursiveSNARK<E1, E2, C1, C2>,
    challenges: (E1::Scalar, E1::Scalar),
    R_acc: E1::Scalar,
    W_acc: E1::Scalar,
    initial_table: &Lookup<E1::Scalar>,
    final_table: &Lookup<E1::Scalar>,
  ) -> Result<Self, NovaError> {
    // fold the secondary circuit's instance with its running instance
    let (nifs_secondary, (f_U_secondary, f_W_secondary)) = NIFS::prove(
      &pp.ck_secondary,
      &pp.ro_consts_secondary,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.circuit_shape_secondary.r1cs_shape,
      &recursive_snark.r_U_secondary,
      &recursive_snark.r_W_secondary,
      &recursive_snark.l_u_secondary,
      &recursive_snark.l_w_secondary,
    )?;

    // create SNARKs proving the knowledge of f_W_primary and f_W_secondary
    let (r_W_snark_primary, f_W_snark_secondary) = rayon::join(
      || {
        S1::prove(
          &pp.ck_primary,
          &pk.pk_primary,
          &pp.circuit_shape_primary.r1cs_shape,
          &recursive_snark.r_U_primary,
          &recursive_snark.r_W_primary,
          challenges,
          R_acc,
          W_acc,
          initial_table.clone(),
          final_table.clone(),
        )
      },
      || {
        S2::prove(
          &pp.ck_secondary,
          &pk.pk_secondary,
          &pp.circuit_shape_secondary.r1cs_shape,
          &f_U_secondary,
          &f_W_secondary,
        )
      },
    );

    Ok(Self {
      r_U_primary: recursive_snark.r_U_primary.clone(),
      r_W_snark_primary: r_W_snark_primary?,

      r_U_secondary: recursive_snark.r_U_secondary.clone(),
      l_u_secondary: recursive_snark.l_u_secondary.clone(),
      nifs_secondary,
      f_W_snark_secondary: f_W_snark_secondary?,

      zn_primary: recursive_snark.zi_primary.clone(),
      zn_secondary: recursive_snark.zi_secondary.clone(),

      _p: Default::default(),
    })
  }

  /// Verify the correctness of the `CompressedSNARK`
  pub fn verify(
    &self,
    vk: &VerifierKeyV2<E1, E2, C1, C2, S1, S2>,
    num_steps: usize,
    z0_primary: &[E1::Scalar],
    z0_secondary: &[E2::Scalar],
    lookup_intermediate_gamma: E1::Scalar,
    R_acc: E1::Scalar,
    W_acc: E1::Scalar,
    challenges: (E1::Scalar, E1::Scalar),
  ) -> Result<(Vec<E1::Scalar>, Vec<E2::Scalar>), NovaError> {
    // the number of steps cannot be zero
    if num_steps == 0 {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the (relaxed) R1CS instances have two public outputs
    if self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let (hash_primary, hash_secondary) = {
      let mut hasher = <E2 as Engine>::RO::new(
        vk.ro_consts_secondary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * vk.F_arity_primary,
      );
      hasher.absorb(vk.pp_digest);
      hasher.absorb(E1::Scalar::from(num_steps as u64));
      for e in z0_primary {
        hasher.absorb(*e);
      }
      for e in &self.zn_primary {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 = <E1 as Engine>::RO::new(
        vk.ro_consts_primary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * vk.F_arity_secondary,
      );
      hasher2.absorb(scalar_as_base::<E1>(vk.pp_digest));
      hasher2.absorb(E2::Scalar::from(num_steps as u64));
      for e in z0_secondary {
        hasher2.absorb(*e);
      }
      for e in &self.zn_secondary {
        hasher2.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro(&mut hasher2);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != self.l_u_secondary.X[0]
      || hash_secondary != scalar_as_base::<E2>(self.l_u_secondary.X[1])
    {
      return Err(NovaError::ProofVerifyError);
    }

    // fold the secondary's running instance with the last instance to get a folded instance
    let f_U_secondary = self.nifs_secondary.verify(
      &vk.ro_consts_secondary,
      &scalar_as_base::<E1>(vk.pp_digest),
      &self.r_U_secondary,
      &self.l_u_secondary,
    )?;

    // check the satisfiability of the folded instances using
    // SNARKs proving the knowledge of their satisfying witnesses
    let (res_primary, res_secondary) = rayon::join(
      || {
        self.r_W_snark_primary.verify::<E2>(
          &vk.vk_primary,
          &self.r_U_primary,
          lookup_intermediate_gamma,
          R_acc,
          W_acc,
          challenges.clone(),
        )
      },
      || {
        self
          .f_W_snark_secondary
          .verify(&vk.vk_secondary, &f_U_secondary)
      },
    );

    res_primary?;
    res_secondary?;

    Ok((self.zn_primary.clone(), self.zn_secondary.clone()))
  }
}

/// Compute the circuit digest of a [StepCircuit].
///
/// Note for callers: This function should be called with its performance characteristics in mind.
/// It will synthesize and digest the full `circuit` given.
pub fn circuit_digest<
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  C: StepCircuit<E1::Scalar>,
>(
  circuit: &C,
) -> E1::Scalar {
  let augmented_circuit_params = NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);

  // ro_consts_circuit are parameterized by G2 because the type alias uses G2::Base = G1::Scalar
  let ro_consts_circuit: ROConstantsCircuit<E2> = ROConstantsCircuit::<E2>::default();

  // Initialize ck for the primary
  let augmented_circuit: NovaAugmentedCircuit<'_, E2, C> =
    NovaAugmentedCircuit::new(&augmented_circuit_params, None, circuit, ro_consts_circuit);
  let mut cs: ShapeCS<E1> = ShapeCS::new();
  let _ = augmented_circuit.synthesize(&mut cs);
  cs.r1cs_shape().digest()
}

type CommitmentKey<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey;
type Commitment<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment;
type CompressedCommitment<E> = <<<E as Engine>::CE as CommitmentEngineTrait<E>>::Commitment as CommitmentTrait<E>>::CompressedCommitment;
type CE<E> = <E as Engine>::CE;

#[cfg(test)]
mod tests {
  use crate::bellpepper::test_shape_cs::TestShapeCS;
  use crate::gadgets::lookup::{less_than, Lookup, LookupTrace, LookupTraceBuilder, TableType};
  use crate::gadgets::utils::conditionally_select2;
  use crate::provider::poseidon::PoseidonConstantsCircuit;
  // use crate::spartan::lookupsnark::LookupSNARK;
  use crate::spartan::math::Math;
  use crate::traits::evaluation::EvaluationEngineTrait;
  use core::fmt::Write;

  use super::*;
  use crate::{
    provider::{
      non_hiding_zeromorph::ZMPCS, traits::DlogGroup, Bn256Engine, Bn256EngineKZG, Bn256EngineZM,
      GrumpkinEngine, PallasEngine, Secp256k1Engine, Secq256k1Engine, VestaEngine,
    },
    traits::snark::default_ck_hint,
  };
  use ::bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
  use bellpepper_core::Namespace;
  use core::marker::PhantomData;
  use expect_test::{expect, Expect};
  use ff::PrimeField;
  use halo2curves::bn256::Bn256;
  use tap::TapOptional;
  use traits::circuit::TrivialCircuit;

  type EE<E> = provider::ipa_pc::EvaluationEngine<E>;
  type S<E, EE> = spartan::snark::RelaxedR1CSSNARK<E, EE>;
  type SPrime<E, EE> = spartan::ppsnark::RelaxedR1CSSNARK<E, EE>;

  #[derive(Clone, Debug, Default)]
  struct CubicCircuit<F> {
    _p: PhantomData<F>,
  }

  impl<F: PrimeField> StepCircuit<F> for CubicCircuit<F> {
    fn arity(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
      let x = &z[0];
      let x_sq = x.square(cs.namespace(|| "x_sq"))?;
      let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), x)?;
      let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
        Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
      })?;

      cs.enforce(
        || "y = x^3 + x + 5",
        |lc| {
          lc + x_cu.get_variable()
            + x.get_variable()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
        },
        |lc| lc + CS::one(),
        |lc| lc + y.get_variable(),
      );

      Ok(vec![y])
    }
  }

  impl<F: PrimeField> CubicCircuit<F> {
    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0] * z[0] * z[0] + z[0] + F::from(5u64)]
    }
  }

  fn test_pp_digest_with<E1, E2, T1, T2, EE1, EE2>(circuit1: &T1, circuit2: &T2, expected: &Expect)
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    E1::GE: DlogGroup,
    E2::GE: DlogGroup,
    T1: StepCircuit<E1::Scalar>,
    T2: StepCircuit<E2::Scalar>,
    EE1: EvaluationEngineTrait<E1>,
    EE2: EvaluationEngineTrait<E2>,
    // this is due to the reliance on Abomonation
    <E1::Scalar as PrimeField>::Repr: Abomonation,
    <E2::Scalar as PrimeField>::Repr: Abomonation,
  {
    // this tests public parameters with a size specifically intended for a spark-compressed SNARK
    let ck_hint1 = &*SPrime::<E1, EE1>::ck_floor();
    let ck_hint2 = &*SPrime::<E2, EE2>::ck_floor();
    let pp = PublicParams::<E1, E2, T1, T2>::setup(circuit1, circuit2, ck_hint1, ck_hint2);

    let digest_str = pp
      .digest()
      .to_repr()
      .as_ref()
      .iter()
      .fold(String::new(), |mut output, b| {
        let _ = write!(output, "{b:02x}");
        output
      });

    expected.assert_eq(&digest_str);
  }

  #[test]
  fn test_pp_digest() {
    let trivial_circuit1 = TrivialCircuit::<<PallasEngine as Engine>::Scalar>::default();
    let trivial_circuit2 = TrivialCircuit::<<VestaEngine as Engine>::Scalar>::default();
    let cubic_circuit1 = CubicCircuit::<<PallasEngine as Engine>::Scalar>::default();

    test_pp_digest_with::<PallasEngine, VestaEngine, _, _, EE<_>, EE<_>>(
      &trivial_circuit1,
      &trivial_circuit2,
      &expect!["492fd902cd7174159bc9a6f827d92eb54ff25efa9d0673dffdb0efd02995df01"],
    );

    test_pp_digest_with::<PallasEngine, VestaEngine, _, _, EE<_>, EE<_>>(
      &cubic_circuit1,
      &trivial_circuit2,
      &expect!["9b0701d9422658e3f74a85ab3e485c06f3ecca9c2b1800aab80004034d754f01"],
    );

    let trivial_circuit1_grumpkin = TrivialCircuit::<<Bn256Engine as Engine>::Scalar>::default();
    let trivial_circuit2_grumpkin = TrivialCircuit::<<GrumpkinEngine as Engine>::Scalar>::default();
    let cubic_circuit1_grumpkin = CubicCircuit::<<Bn256Engine as Engine>::Scalar>::default();

    // These tests should not need be different on the "asm" feature for bn256.
    // See https://github.com/privacy-scaling-explorations/halo2curves/issues/100 for why they are - closing the issue there
    // should eliminate the discrepancy here.
    test_pp_digest_with::<Bn256Engine, GrumpkinEngine, _, _, EE<_>, EE<_>>(
      &trivial_circuit1_grumpkin,
      &trivial_circuit2_grumpkin,
      &expect!["1267235eb3d139e466dd9c814eaf73f01b063ccb4cad04848c0eb62f079a9601"],
    );
    test_pp_digest_with::<Bn256Engine, GrumpkinEngine, _, _, EE<_>, EE<_>>(
      &cubic_circuit1_grumpkin,
      &trivial_circuit2_grumpkin,
      &expect!["57afac2edd20d39b202151906e41154ba186c9dde497448d1332dc6de2f76302"],
    );
    test_pp_digest_with::<Bn256EngineZM, GrumpkinEngine, _, _, ZMPCS<Bn256, _>, EE<_>>(
      &trivial_circuit1_grumpkin,
      &trivial_circuit2_grumpkin,
      &expect!["070d247d83e17411d65c12260980ebcc59df88d3882d84eb62e6ab466e381503"],
    );
    test_pp_digest_with::<Bn256EngineZM, GrumpkinEngine, _, _, ZMPCS<Bn256, _>, EE<_>>(
      &cubic_circuit1_grumpkin,
      &trivial_circuit2_grumpkin,
      &expect!["47c2caa008323b588b47ab8b6c0e94f980599188abe117c4d21ffff81494f303"],
    );

    let trivial_circuit1_secp = TrivialCircuit::<<Secp256k1Engine as Engine>::Scalar>::default();
    let trivial_circuit2_secp = TrivialCircuit::<<Secq256k1Engine as Engine>::Scalar>::default();
    let cubic_circuit1_secp = CubicCircuit::<<Secp256k1Engine as Engine>::Scalar>::default();

    test_pp_digest_with::<Secp256k1Engine, Secq256k1Engine, _, _, EE<_>, EE<_>>(
      &trivial_circuit1_secp,
      &trivial_circuit2_secp,
      &expect!["04b5d1798be6d74b3701390b87078e70ebf3ddaad80c375319f320cedf8bca00"],
    );
    test_pp_digest_with::<Secp256k1Engine, Secq256k1Engine, _, _, EE<_>, EE<_>>(
      &cubic_circuit1_secp,
      &trivial_circuit2_secp,
      &expect!["346b5f27cf24c79386f4de7a8bfb58970181ae7f0de7d2e3f10ad5dfd8fc2302"],
    );
  }

  fn test_ivc_trivial_with<E1, E2>()
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    let test_circuit1 = TrivialCircuit::<<E1 as Engine>::Scalar>::default();
    let test_circuit2 = TrivialCircuit::<<E2 as Engine>::Scalar>::default();

    // produce public parameters
    let pp = PublicParams::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      TrivialCircuit<<E2 as Engine>::Scalar>,
    >::setup(
      &test_circuit1,
      &test_circuit2,
      &*default_ck_hint(),
      &*default_ck_hint(),
    );
    let num_steps = 1;

    // produce a recursive SNARK
    let mut recursive_snark = RecursiveSNARK::new(
      &pp,
      &test_circuit1,
      &test_circuit2,
      &[<E1 as Engine>::Scalar::ZERO],
      &[<E2 as Engine>::Scalar::ZERO],
    )
    .unwrap();

    let res = recursive_snark.prove_step(&pp, &test_circuit1, &test_circuit2);

    assert!(res.is_ok());

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      &[<E1 as Engine>::Scalar::ZERO],
      &[<E2 as Engine>::Scalar::ZERO],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_trivial() {
    test_ivc_trivial_with::<PallasEngine, VestaEngine>();
    test_ivc_trivial_with::<Bn256Engine, GrumpkinEngine>();
    test_ivc_trivial_with::<Secp256k1Engine, Secq256k1Engine>();
  }

  fn test_ivc_nontrivial_with<E1, E2>()
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    let circuit_primary = TrivialCircuit::default();
    let circuit_secondary = CubicCircuit::default();

    // produce public parameters
    let pp = PublicParams::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::setup(
      &circuit_primary,
      &circuit_secondary,
      &*default_ck_hint(),
      &*default_ck_hint(),
    );

    let num_steps = 3;

    // produce a recursive SNARK
    let mut recursive_snark = RecursiveSNARK::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::new(
      &pp,
      &circuit_primary,
      &circuit_secondary,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    )
    .unwrap();

    for i in 0..num_steps {
      let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
      assert!(res.is_ok());

      // verify the recursive snark at each step of recursion
      let res = recursive_snark.verify(
        &pp,
        i + 1,
        &[<E1 as Engine>::Scalar::ONE],
        &[<E2 as Engine>::Scalar::ZERO],
      );
      assert!(res.is_ok());
    }

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(zn_primary, vec![<E1 as Engine>::Scalar::ONE]);
    let mut zn_secondary_direct = vec![<E2 as Engine>::Scalar::ZERO];
    for _i in 0..num_steps {
      zn_secondary_direct = circuit_secondary.clone().output(&zn_secondary_direct);
    }
    assert_eq!(zn_secondary, zn_secondary_direct);
    assert_eq!(zn_secondary, vec![<E2 as Engine>::Scalar::from(2460515u64)]);
  }

  #[test]
  fn test_ivc_nontrivial() {
    test_ivc_nontrivial_with::<PallasEngine, VestaEngine>();
    test_ivc_nontrivial_with::<Bn256Engine, GrumpkinEngine>();
    test_ivc_nontrivial_with::<Secp256k1Engine, Secq256k1Engine>();
  }

  fn test_ivc_nontrivial_with_compression_with<E1, E2, EE1, EE2>()
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    EE1: EvaluationEngineTrait<E1>,
    EE2: EvaluationEngineTrait<E2>,
    // this is due to the reliance on Abomonation
    <E1::Scalar as PrimeField>::Repr: Abomonation,
    <E2::Scalar as PrimeField>::Repr: Abomonation,
  {
    let circuit_primary = TrivialCircuit::default();
    let circuit_secondary = CubicCircuit::default();

    // produce public parameters
    let pp = PublicParams::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::setup(
      &circuit_primary,
      &circuit_secondary,
      &*default_ck_hint(),
      &*default_ck_hint(),
    );

    let num_steps = 3;

    // produce a recursive SNARK
    let mut recursive_snark = RecursiveSNARK::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::new(
      &pp,
      &circuit_primary,
      &circuit_secondary,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    )
    .unwrap();

    for _i in 0..num_steps {
      let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
      assert!(res.is_ok());
    }

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(zn_primary, vec![<E1 as Engine>::Scalar::ONE]);
    let mut zn_secondary_direct = vec![<E2 as Engine>::Scalar::ZERO];
    for _i in 0..num_steps {
      zn_secondary_direct = circuit_secondary.clone().output(&zn_secondary_direct);
    }
    assert_eq!(zn_secondary, zn_secondary_direct);
    assert_eq!(zn_secondary, vec![<E2 as Engine>::Scalar::from(2460515u64)]);

    // produce the prover and verifier keys for compressed snark
    let (pk, vk) = CompressedSNARK::<_, _, _, _, S<E1, EE1>, S<E2, EE2>>::setup(&pp).unwrap();

    // produce a compressed SNARK
    let res =
      CompressedSNARK::<_, _, _, _, S<E1, EE1>, S<E2, EE2>>::prove(&pp, &pk, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(
      &vk,
      num_steps,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_nontrivial_with_compression() {
    test_ivc_nontrivial_with_compression_with::<PallasEngine, VestaEngine, EE<_>, EE<_>>();
    test_ivc_nontrivial_with_compression_with::<Bn256Engine, GrumpkinEngine, EE<_>, EE<_>>();
    test_ivc_nontrivial_with_compression_with::<Secp256k1Engine, Secq256k1Engine, EE<_>, EE<_>>();
    test_ivc_nontrivial_with_compression_with::<
      Bn256EngineZM,
      GrumpkinEngine,
      ZMPCS<Bn256, _>,
      EE<_>,
    >();

    test_ivc_nontrivial_with_spark_compression_with::<
      Bn256EngineKZG,
      GrumpkinEngine,
      provider::hyperkzg::EvaluationEngine<Bn256, _>,
      EE<_>,
    >();
  }

  fn test_ivc_nontrivial_with_spark_compression_with<E1, E2, EE1, EE2>()
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    EE1: EvaluationEngineTrait<E1>,
    EE2: EvaluationEngineTrait<E2>,
    // this is due to the reliance on Abomonation
    <E1::Scalar as PrimeField>::Repr: Abomonation,
    <E2::Scalar as PrimeField>::Repr: Abomonation,
  {
    let circuit_primary = TrivialCircuit::default();
    let circuit_secondary = CubicCircuit::default();

    // produce public parameters, which we'll use with a spark-compressed SNARK
    let pp = PublicParams::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::setup(
      &circuit_primary,
      &circuit_secondary,
      &*SPrime::<E1, EE1>::ck_floor(),
      &*SPrime::<E2, EE2>::ck_floor(),
    );

    let num_steps = 3;

    // produce a recursive SNARK
    let mut recursive_snark = RecursiveSNARK::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::new(
      &pp,
      &circuit_primary,
      &circuit_secondary,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    )
    .unwrap();

    for _i in 0..num_steps {
      let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
      assert!(res.is_ok());
    }

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(zn_primary, vec![<E1 as Engine>::Scalar::ONE]);
    let mut zn_secondary_direct = vec![<E2 as Engine>::Scalar::ZERO];
    for _i in 0..num_steps {
      zn_secondary_direct = CubicCircuit::default().output(&zn_secondary_direct);
    }
    assert_eq!(zn_secondary, zn_secondary_direct);
    assert_eq!(zn_secondary, vec![<E2 as Engine>::Scalar::from(2460515u64)]);

    // run the compressed snark with Spark compiler
    // produce the prover and verifier keys for compressed snark
    let (pk, vk) =
      CompressedSNARK::<_, _, _, _, SPrime<E1, EE1>, SPrime<E2, EE2>>::setup(&pp).unwrap();

    // produce a compressed SNARK
    let res = CompressedSNARK::<_, _, _, _, SPrime<E1, EE1>, SPrime<E2, EE2>>::prove(
      &pp,
      &pk,
      &recursive_snark,
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(
      &vk,
      num_steps,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_nontrivial_with_spark_compression() {
    test_ivc_nontrivial_with_spark_compression_with::<PallasEngine, VestaEngine, EE<_>, EE<_>>();
    test_ivc_nontrivial_with_spark_compression_with::<Bn256Engine, GrumpkinEngine, EE<_>, EE<_>>();
    test_ivc_nontrivial_with_spark_compression_with::<Secp256k1Engine, Secq256k1Engine, EE<_>, EE<_>>(
    );
    test_ivc_nontrivial_with_spark_compression_with::<
      Bn256EngineZM,
      GrumpkinEngine,
      ZMPCS<Bn256, _>,
      EE<_>,
    >();
  }

  fn test_ivc_nondet_with_compression_with<E1, E2, EE1, EE2>()
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    EE1: EvaluationEngineTrait<E1>,
    EE2: EvaluationEngineTrait<E2>,
    // this is due to the reliance on Abomonation
    <E1::Scalar as PrimeField>::Repr: Abomonation,
    <E2::Scalar as PrimeField>::Repr: Abomonation,
  {
    // y is a non-deterministic advice representing the fifth root of the input at a step.
    #[derive(Clone, Debug)]
    struct FifthRootCheckingCircuit<F> {
      y: F,
    }

    impl<F: PrimeField> FifthRootCheckingCircuit<F> {
      fn new(num_steps: usize) -> (Vec<F>, Vec<Self>) {
        let mut powers = Vec::new();
        let rng = &mut rand::rngs::OsRng;
        let mut seed = F::random(rng);
        for _i in 0..num_steps + 1 {
          seed *= seed.clone().square().square();

          powers.push(Self { y: seed });
        }

        // reverse the powers to get roots
        let roots = powers.into_iter().rev().collect::<Vec<Self>>();
        (vec![roots[0].y], roots[1..].to_vec())
      }
    }

    impl<F> StepCircuit<F> for FifthRootCheckingCircuit<F>
    where
      F: PrimeField,
    {
      fn arity(&self) -> usize {
        1
      }

      fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
      ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let x = &z[0];

        // we allocate a variable and set it to the provided non-deterministic advice.
        let y = AllocatedNum::alloc_infallible(cs.namespace(|| "y"), || self.y);

        // We now check if y = x^{1/5} by checking if y^5 = x
        let y_sq = y.square(cs.namespace(|| "y_sq"))?;
        let y_quad = y_sq.square(cs.namespace(|| "y_quad"))?;
        let y_pow_5 = y_quad.mul(cs.namespace(|| "y_fifth"), &y)?;

        cs.enforce(
          || "y^5 = x",
          |lc| lc + y_pow_5.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc + x.get_variable(),
        );

        Ok(vec![y])
      }
    }

    let circuit_primary = FifthRootCheckingCircuit {
      y: <E1 as Engine>::Scalar::ZERO,
    };

    let circuit_secondary = TrivialCircuit::default();

    // produce public parameters
    let pp = PublicParams::<
      E1,
      E2,
      FifthRootCheckingCircuit<<E1 as Engine>::Scalar>,
      TrivialCircuit<<E2 as Engine>::Scalar>,
    >::setup(
      &circuit_primary,
      &circuit_secondary,
      &*default_ck_hint(),
      &*default_ck_hint(),
    );

    let num_steps = 3;

    // produce non-deterministic advice
    let (z0_primary, roots) = FifthRootCheckingCircuit::new(num_steps);
    let z0_secondary = vec![<E2 as Engine>::Scalar::ZERO];

    // produce a recursive SNARK
    let mut recursive_snark: RecursiveSNARK<
      E1,
      E2,
      FifthRootCheckingCircuit<<E1 as Engine>::Scalar>,
      TrivialCircuit<<E2 as Engine>::Scalar>,
    > = RecursiveSNARK::<
      E1,
      E2,
      FifthRootCheckingCircuit<<E1 as Engine>::Scalar>,
      TrivialCircuit<<E2 as Engine>::Scalar>,
    >::new(
      &pp,
      &roots[0],
      &circuit_secondary,
      &z0_primary,
      &z0_secondary,
    )
    .unwrap();

    for circuit_primary in roots.iter().take(num_steps) {
      let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
      assert!(res.is_ok());
    }

    // verify the recursive SNARK
    let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
    assert!(res.is_ok());

    // produce the prover and verifier keys for compressed snark
    let (pk, vk) = CompressedSNARK::<_, _, _, _, S<E1, EE1>, S<E2, EE2>>::setup(&pp).unwrap();

    // produce a compressed SNARK
    let res =
      CompressedSNARK::<_, _, _, _, S<E1, EE1>, S<E2, EE2>>::prove(&pp, &pk, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(&vk, num_steps, &z0_primary, &z0_secondary);
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_nondet_with_compression() {
    test_ivc_nondet_with_compression_with::<PallasEngine, VestaEngine, EE<_>, EE<_>>();
    test_ivc_nondet_with_compression_with::<Bn256Engine, GrumpkinEngine, EE<_>, EE<_>>();
    test_ivc_nondet_with_compression_with::<Secp256k1Engine, Secq256k1Engine, EE<_>, EE<_>>();
    test_ivc_nondet_with_compression_with::<Bn256EngineZM, GrumpkinEngine, ZMPCS<Bn256, _>, EE<_>>(
    );
  }

  fn test_ivc_base_with<E1, E2>()
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
  {
    let test_circuit1 = TrivialCircuit::<<E1 as Engine>::Scalar>::default();
    let test_circuit2 = CubicCircuit::<<E2 as Engine>::Scalar>::default();

    // produce public parameters
    let pp = PublicParams::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::setup(
      &test_circuit1,
      &test_circuit2,
      &*default_ck_hint(),
      &*default_ck_hint(),
    );

    let num_steps = 1;

    // produce a recursive SNARK
    let mut recursive_snark = RecursiveSNARK::<
      E1,
      E2,
      TrivialCircuit<<E1 as Engine>::Scalar>,
      CubicCircuit<<E2 as Engine>::Scalar>,
    >::new(
      &pp,
      &test_circuit1,
      &test_circuit2,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    )
    .unwrap();

    // produce a recursive SNARK
    let res = recursive_snark.prove_step(&pp, &test_circuit1, &test_circuit2);

    assert!(res.is_ok());

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      &[<E1 as Engine>::Scalar::ONE],
      &[<E2 as Engine>::Scalar::ZERO],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    assert_eq!(zn_primary, vec![<E1 as Engine>::Scalar::ONE]);
    assert_eq!(zn_secondary, vec![<E2 as Engine>::Scalar::from(5u64)]);
  }

  #[test]
  fn test_ivc_base() {
    test_ivc_base_with::<PallasEngine, VestaEngine>();
    test_ivc_base_with::<Bn256Engine, GrumpkinEngine>();
    test_ivc_base_with::<Secp256k1Engine, Secq256k1Engine>();
  }

  fn print_constraints_name_on_error_index<E1, E2, C1>(err: &NovaError, c_primary: &C1)
  where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    C1: StepCircuit<E1::Scalar>,
  {
    match err {
      NovaError::UnSatIndex(index) => {
        let augmented_circuit_params_primary =
          NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);

        // let (mut circuit_primary, z0_primary) = HeapifyCircuit::new(ro_consts);
        let ro_consts_circuit_primary: ROConstantsCircuit<E2> = ROConstantsCircuit::<E2>::default();
        let circuit_primary: NovaAugmentedCircuit<'_, E2, C1> = NovaAugmentedCircuit::new(
          &augmented_circuit_params_primary,
          None,
          c_primary,
          ro_consts_circuit_primary,
        );
        // let mut cs: ShapeCS<E1> = ShapeCS::new();
        // let _ = circuit_primary.synthesize(&mut cs);
        let mut cs: TestShapeCS<E1> = TestShapeCS::new();
        let _ = circuit_primary.synthesize(&mut cs);
        cs.constraints
          .get(*index)
          .tap_some(|constraint| println!("failed at constraint {}", constraint.3));
      }
      error => unimplemented!("{:?}", error),
    }
  }

  #[test]
  fn test_ivc_rwlookup() {
    type S1<E, EE> = spartan::ppsnark::RelaxedR1CSSNARKV2<E, EE>;
    type S2<E, EE> = spartan::ppsnark::RelaxedR1CSSNARK<E, EE>;
    type E1 = provider::PallasEngine;
    type E2 = provider::VestaEngine;
    type EE<E> = provider::ipa_pc::EvaluationEngine<E>;

    // rw lookup to serve as a non-deterministic advices.
    #[derive(Clone)]
    struct HeapifyCircuit<E1: Engine, E2: Engine>
    where
      <E1 as Engine>::Scalar: Ord,
      E1: Engine<Base = <E2 as Engine>::Scalar>,
      E2: Engine<Base = <E1 as Engine>::Scalar>,
    {
      lookup_trace: LookupTrace<E1>,
      ro_consts: ROConstantsCircuit<E2>,
      max_value_bits: usize,
      _phantom: PhantomData<E2>,
    }

    impl<E1: Engine, E2: Engine> HeapifyCircuit<E1, E2>
    where
      <E1 as Engine>::Scalar: Ord,
      E1: Engine<Base = <E2 as Engine>::Scalar>,
      E2: Engine<Base = <E1 as Engine>::Scalar>,
    {
      fn new(
        initial_table: Lookup<E1::Scalar>,
        ro_consts_circuit: ROConstantsCircuit<E2>,
      ) -> (Vec<Self>, Lookup<E1::Scalar>, E1::Scalar) {
        let n = initial_table.table_size();

        let initial_index = (n - 4) / 2;
        let max_value_bits = (n - 1).log_2() + 1; // + 1 as a buffer
        let initial_intermediate_gamma = <E1 as Engine>::Scalar::from(1);

        let mut lookup = initial_table;
        let num_steps = initial_index;
        let mut intermediate_gamma = initial_intermediate_gamma;
        // simulate folding step lookup io
        let mut primary_circuits = Vec::with_capacity(num_steps + 1);
        let ro_consts = <<E2 as Engine>::RO as ROTrait<
          <E2 as Engine>::Base,
          <E2 as Engine>::Scalar,
        >>::Constants::default();
        for i in 0..num_steps + 1 {
          let mut lookup_trace_builder = LookupTraceBuilder::<E1>::new(&mut lookup);
          let addr = E1::Scalar::from((num_steps - i) as u64);
          let parent = lookup_trace_builder.read(addr);
          let left_child = lookup_trace_builder.read(E1::Scalar::from(2) * addr + E1::Scalar::ONE);
          let right_child =
            lookup_trace_builder.read(E1::Scalar::from(2) * addr + E1::Scalar::from(2));
          // swap left pair
          let (new_parent_left, new_left_child) = if left_child < parent {
            (left_child, parent)
          } else {
            (parent, left_child)
          };
          lookup_trace_builder.write(addr, new_parent_left);
          lookup_trace_builder.write(
            E1::Scalar::from(2) * addr + E1::Scalar::from(1),
            new_left_child,
          );
          // swap right pair
          let (new_parent_right, new_right_child) = if right_child < new_parent_left {
            (right_child, new_parent_left)
          } else {
            (new_parent_left, right_child)
          };
          lookup_trace_builder.write(addr, new_parent_right);
          lookup_trace_builder.write(
            E1::Scalar::from(2) * addr + E1::Scalar::from(2),
            new_right_child,
          );
          let res = lookup_trace_builder.snapshot::<E2>(ro_consts.clone(), intermediate_gamma);
          intermediate_gamma = res.0;
          let (_, lookup_trace) = res;
          primary_circuits.push(Self {
            lookup_trace,
            ro_consts: ro_consts_circuit.clone(),
            max_value_bits,
            _phantom: PhantomData::<E2> {},
          });
        }

        (primary_circuits, lookup, intermediate_gamma)
      }

      fn get_z0(
        ck: &CommitmentKey<E1>,
        final_table: &Lookup<E1::Scalar>,
        intermediate_gamma: E1::Scalar,
      ) -> Vec<E1::Scalar>
      where
        E1: Engine<Base = <E2 as Engine>::Scalar>,
        E2: Engine<Base = <E1 as Engine>::Scalar>,
      {
        let n = final_table.table_size();
        let initial_index = (n - 4) / 2;
        let (initial_intermediate_gamma, init_prev_R, init_prev_W, init_rw_counter) = (
          <E1 as Engine>::Scalar::from(1),
          <E1 as Engine>::Scalar::from(1),
          <E1 as Engine>::Scalar::from(1),
          <E1 as Engine>::Scalar::from(0),
        );

        let (alpha, gamma) =
          LookupTraceBuilder::<E1>::get_challenge::<E2>(ck, final_table, intermediate_gamma);
        vec![
          initial_intermediate_gamma,
          alpha,
          gamma,
          init_prev_R,
          init_prev_W,
          init_rw_counter,
          E1::Scalar::from(initial_index as u64),
        ]
      }
    }

    impl<F: PrimeField, E1: Engine + Engine<Scalar = F>, E2: Engine> StepCircuit<F>
      for HeapifyCircuit<E1, E2>
    where
      E1::Scalar: Ord,
      E1: Engine<Base = <E2 as Engine>::Scalar>,
      E2: Engine<Base = <E1 as Engine>::Scalar>,
    {
      fn arity(&self) -> usize {
        7
      }

      fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
      ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let mut lookup_trace = self.lookup_trace.clone();
        let prev_intermediate_gamma = &z[0];
        let alpha = &z[1];
        let gamma = &z[2];
        let prev_R = &z[3];
        let prev_W = &z[4];
        let prev_rw_counter = &z[5];
        let index = &z[6];

        let left_child_index = AllocatedNum::alloc(cs.namespace(|| "left_child_index"), || {
          index
            .get_value()
            .map(|i| i.mul(F::from(2)) + F::ONE)
            .ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
          || "(2*index + 1) * 1 = left_child_index",
          |lc| lc + (F::from(2), index.get_variable()) + CS::one(),
          |lc| lc + CS::one(),
          |lc| lc + left_child_index.get_variable(),
        );
        let right_child_index = AllocatedNum::alloc(cs.namespace(|| "right_child_index"), || {
          left_child_index
            .get_value()
            .map(|i| i + F::ONE)
            .ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
          || "(left_child_index + 1) * 1 = right_child_index",
          |lc| lc + left_child_index.get_variable() + CS::one(),
          |lc| lc + CS::one(),
          |lc| lc + right_child_index.get_variable(),
        );
        let parent = lookup_trace.read(cs.namespace(|| "parent"), index)?;
        let left_child = lookup_trace.read(cs.namespace(|| "left_child"), &left_child_index)?;
        let right_child = lookup_trace.read(cs.namespace(|| "right_child"), &right_child_index)?;

        let is_left_child_smaller = less_than(
          cs.namespace(|| "left_child < parent"),
          &left_child,
          &parent,
          self.max_value_bits,
        )?;

        let new_parent_left = conditionally_select2(
          cs.namespace(|| "new_left_pair_parent"),
          &left_child,
          &parent,
          &is_left_child_smaller,
        )?;

        let new_left_child = conditionally_select2(
          cs.namespace(|| "new_left_pair_child"),
          &parent,
          &left_child,
          &is_left_child_smaller,
        )?;

        lookup_trace.write(
          cs.namespace(|| "write_left_pair_parent"),
          index,
          &new_parent_left,
        )?;
        lookup_trace.write(
          cs.namespace(|| "write_left_pair_child"),
          &left_child_index,
          &new_left_child,
        )?;

        let is_right_child_smaller = less_than(
          cs.namespace(|| "right_child < parent"),
          &right_child,
          &new_parent_left,
          self.max_value_bits,
        )?;

        let new_parent_right = conditionally_select2(
          cs.namespace(|| "new_right_pair_parent"),
          &right_child,
          &new_parent_left,
          &is_right_child_smaller,
        )?;
        let new_right_child = conditionally_select2(
          cs.namespace(|| "new_right_pair_child"),
          &new_parent_left,
          &right_child,
          &is_right_child_smaller,
        )?;
        lookup_trace.write(
          cs.namespace(|| "write_right_pair_parent"),
          index,
          &new_parent_right,
        )?;
        lookup_trace.write(
          cs.namespace(|| "write_right_pair_child"),
          &right_child_index,
          &new_right_child,
        )?;

        // commit the rw change
        let (next_R, next_W, next_rw_counter, next_intermediate_gamma) = lookup_trace
          .commit::<E2, Namespace<'_, F, <CS as ConstraintSystem<F>>::Root>>(
            cs.namespace(|| "commit"),
            self.ro_consts.clone(),
            prev_intermediate_gamma,
            &(alpha.clone(), gamma.clone()),
            prev_W,
            prev_R,
            prev_rw_counter,
          )?;

        let next_index = AllocatedNum::alloc(cs.namespace(|| "next_index"), || {
          index
            .get_value()
            .map(|index| index - E1::Scalar::from(1))
            .ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
          || "(next_index + 1) * 1 = index",
          |lc| lc + next_index.get_variable() + CS::one(),
          |lc| lc + CS::one(),
          |lc| lc + index.get_variable(),
        );
        Ok(vec![
          next_intermediate_gamma,
          alpha.clone(),
          gamma.clone(),
          next_R,
          next_W,
          next_rw_counter,
          next_index,
        ])
      }
    }

    let heap_size: usize = 4;

    let ro_consts: ROConstantsCircuit<E2> = PoseidonConstantsCircuit::default();

    let initial_table = {
      let mut initial_table = (0..heap_size - 1)
        .map(|i| {
          (
            <E2 as Engine>::Base::from(i as u64),
            <E2 as Engine>::Base::from((heap_size - 2 - i) as u64),
          )
        })
        .collect::<Vec<(<E2 as Engine>::Base, <E2 as Engine>::Base)>>();
      initial_table.push((
        <E2 as Engine>::Base::from(heap_size as u64 - 1),
        <E2 as Engine>::Base::ZERO,
      )); // attach 1 dummy element to assure table size is power of 2
      Lookup::new(heap_size * 4, TableType::ReadWrite, initial_table)
    };

    let (circuit_primaries, final_table, expected_intermediate_gamma) =
      HeapifyCircuit::new(initial_table.clone(), ro_consts);

    let circuit_secondary = TrivialCircuit::default();

    let ck_hint1 = &*SPrime::<E1, EE<_>>::ck_floor();
    let ck_hint2 = &*SPrime::<E2, EE<_>>::ck_floor();

    // produce public parameters
    let pp =
      PublicParams::<E1, E2, HeapifyCircuit<E1, E2>, TrivialCircuit<<E2 as Engine>::Scalar>>::setup(
        &circuit_primaries[0],
        &circuit_secondary,
        ck_hint1,
        ck_hint2,
      );

    // produce the prover and verifier keys for compressed snark
    let (pk, vk) =
      CompressedSNARKV2::<_, _, _, _, S1<E1, EE<E1>>, S2<E2, EE<E2>>>::setup(&pp, &initial_table)
        .unwrap();

    let z0_primary =
      HeapifyCircuit::<E1, E2>::get_z0(&pp.ck_primary, &final_table, expected_intermediate_gamma);

    // 5th is initial index.
    // +1 for index end with 0
    let num_steps = u32::from_le_bytes(z0_primary[5].to_repr()[0..4].try_into().unwrap()) + 1;

    let z0_secondary = vec![<E2 as Engine>::Scalar::ZERO; 1];

    // produce a recursive SNARK
    let mut recursive_snark: RecursiveSNARK<
      E1,
      E2,
      HeapifyCircuit<E1, E2>,
      TrivialCircuit<<E2 as Engine>::Scalar>,
    > = RecursiveSNARK::new(
      &pp,
      &circuit_primaries[0],
      &circuit_secondary,
      &z0_primary,
      &z0_secondary,
    )
    .unwrap();

    for i in 0..num_steps {
      println!("step i {}", i);
      let res = recursive_snark.prove_step(&pp, &circuit_primaries[i as usize], &circuit_secondary);
      res
        .clone()
        .map_err(|err| println!("err {:?}", err))
        .unwrap();
      assert!(res.is_ok());
    }
    // verify the recursive SNARK
    let res = recursive_snark.verify(&pp, num_steps as usize, &z0_primary, &z0_secondary);
    let (zn_primary, _) = res
      .clone()
      .map_err(|err| {
        print_constraints_name_on_error_index::<E1, E2, _>(&err, &circuit_primaries[0])
      })
      .unwrap();

    assert_eq!(<E1 as Engine>::Scalar::from(1).neg(), zn_primary[6]);

    let number_of_iterated_nodes = (heap_size - 4) / 2 + 1;
    assert_eq!(
      <E1 as Engine>::Scalar::from((number_of_iterated_nodes * 7) as u64),
      zn_primary[5]
    ); // rw counter = number_of_iterated_nodes * (3r + 4w) operations

    assert_eq!(pp.circuit_shape_primary.r1cs_shape.num_cons, 12609);
    assert_eq!(pp.circuit_shape_primary.r1cs_shape.num_vars, 12615);
    assert_eq!(pp.circuit_shape_secondary.r1cs_shape.num_cons, 10357);
    assert_eq!(pp.circuit_shape_secondary.r1cs_shape.num_vars, 10337);

    println!("zn_primary {:?}", zn_primary);

    let intermediate_gamma = zn_primary[0];
    let alpha = zn_primary[1];
    let gamma = zn_primary[2];
    let R_acc = zn_primary[3];
    let W_acc = zn_primary[4];
    assert_eq!(
      expected_intermediate_gamma, intermediate_gamma,
      "expected_intermediate_gamma != intermediate_gamma"
    );

    // produce a compressed SNARK
    let res = CompressedSNARKV2::<_, _, _, _, S1<E1, EE<E1>>, S2<E2, EE<E2>>>::prove(
      &pp,
      &pk,
      &recursive_snark,
      (alpha, gamma),
      R_acc,
      W_acc,
      &initial_table,
      &final_table,
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(
      &vk,
      num_steps.try_into().unwrap(),
      &z0_primary,
      &z0_secondary,
      expected_intermediate_gamma,
      R_acc,
      W_acc,
      (alpha, gamma),
    );
    assert!(res.is_ok());
  }
}
