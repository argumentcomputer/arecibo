//! This module contains the Recursive SNARK for SuperNova with CycleFold

use super::augmented_circuit::SuperNovaAugmentedCircuitInputs;
use crate::bellpepper::r1cs::NovaShape;
use crate::bellpepper::r1cs::NovaWitness;
use crate::bellpepper::shape_cs::ShapeCS;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::constants::NIO_CYCLE_FOLD;
use crate::constants::NUM_CHALLENGE_BITS;
use crate::constants::NUM_FE_IN_EMULATED_POINT;
use crate::constants::NUM_HASH_BITS;
use crate::cyclefold::circuit::CycleFoldCircuit;
use crate::cyclefold::nifs::CycleFoldNIFS;
use crate::cyclefold::nifs::PrimaryNIFS;
use crate::cyclefold::util::absorb_primary_relaxed_r1cs;
use crate::cyclefold::util::FoldingData;
use crate::digest::DigestComputer;
use crate::errors::NovaError;
use crate::gadgets::scalar_as_base;
use crate::r1cs::commitment_key_size;
use crate::supernova::circuit::StepCircuit;
use crate::supernova::cyclefold::augmented_circuit::SuperNovaAugmentedCircuit;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::AbsorbInROTrait;
use crate::traits::Engine;
use crate::traits::ROTrait;
use itertools::Itertools as _;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::ParallelIterator;

use crate::Commitment;
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
  digest::SimpleDigestible,
  r1cs::{CommitmentKeyHint, R1CSInstance, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  supernova::error::SuperNovaError,
  traits::{CurveCycleEquipped, Dual, ROConstants, ROConstantsCircuit},
  CommitmentKey, R1CSWithArity,
};
use bellpepper_core::ConstraintSystem;
use bellpepper_core::SynthesisError;
use ff::Field;
use ff::PrimeFieldBits;
use once_cell::sync::OnceCell;
use rayon::iter::IndexedParallelIterator;
use serde::{Deserialize, Serialize};
use std::ops::Index;
use std::sync::Arc;
use tracing::debug;

use super::{augmented_circuit::SuperNovaAugmentedCircuitParams, traits::NonUniformCircuit};

impl<E1> Index<usize> for PublicParams<E1>
where
  E1: CurveCycleEquipped,
{
  type Output = R1CSWithArity<E1>;

  fn index(&self, index: usize) -> &Self::Output {
    &self.circuit_shapes[index]
  }
}

/// A vector of [`R1CSWithArity`] adjoined to a set of [`PublicParams`]
#[derive(Debug, Serialize)]
#[serde(bound = "")]
pub struct PublicParams<E1>
where
  E1: CurveCycleEquipped,
{
  /// The internal circuit shapes
  circuit_shapes: Vec<R1CSWithArity<E1>>,

  ro_consts_primary: ROConstants<Dual<E1>>,
  pub(crate) ro_consts_circuit_primary: ROConstantsCircuit<Dual<E1>>,
  ck_primary: Arc<CommitmentKey<E1>>, // This is shared between all circuit params
  pub(crate) augmented_circuit_params: SuperNovaAugmentedCircuitParams,

  ro_consts_cyclefold: ROConstants<Dual<E1>>,
  ck_cyclefold: Arc<CommitmentKey<Dual<E1>>>,
  circuit_shape_cyclefold: R1CSWithArity<Dual<E1>>,

  /// Digest constructed from this `PublicParams`' parameters
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<E1::Scalar>,
}

impl<E1> SimpleDigestible for PublicParams<E1> where E1: CurveCycleEquipped {}

impl<E1> PublicParams<E1>
where
  E1: CurveCycleEquipped,
{
  /// Construct a new [`PublicParams`]
  ///
  /// # Note
  ///
  /// Public parameters set up a number of bases for the homomorphic commitment scheme of Nova.
  ///
  /// Some final compressing SNARKs, like variants of Spartan, use computation commitments that require
  /// larger sizes for these parameters. These SNARKs provide a hint for these values by
  /// implementing `RelaxedR1CSSNARKTrait::commitment_key_floor()`, which can be passed to this function.
  ///
  /// If you're not using such a SNARK, pass `&(|_| 0)` instead.
  ///
  /// # Arguments
  ///
  /// * `non_uniform_circuit`: The non-uniform circuit of type `NC`.
  /// * `ck_hint1`: A `CommitmentKeyHint` for `E1`, which is a function that provides a hint
  ///    for the number of generators required in the commitment scheme for the primary circuit.
  /// * `ck_hint2`: A `CommitmentKeyHint` for `E2`, similar to `ck_hint1`, but for the secondary circuit.
  pub fn setup<NC: NonUniformCircuit<E1>>(
    non_uniform_circuit: &NC,
    ck_hint_primary: &CommitmentKeyHint<E1>,
    ck_hint_cyclefold: &CommitmentKeyHint<Dual<E1>>,
  ) -> Self {
    let num_circuits = non_uniform_circuit.num_circuits();

    let augmented_circuit_params = SuperNovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS);
    let ro_consts_primary = ROConstants::<Dual<E1>>::default();
    // ro_consts_circuit_primary are parameterized by E2 because the type alias uses E2::Base = E1::Scalar
    let ro_consts_circuit_primary: ROConstantsCircuit<Dual<E1>> =
      ROConstantsCircuit::<Dual<E1>>::default();

    let circuit_shapes = (0..num_circuits)
      .map(|i| {
        let c_primary = non_uniform_circuit.primary_circuit(i);
        let F_arity = c_primary.arity();
        // Initialize ck for the primary
        let circuit_primary: SuperNovaAugmentedCircuit<'_, Dual<E1>, E1, NC::C1> =
          SuperNovaAugmentedCircuit::new(
            &augmented_circuit_params,
            None,
            ro_consts_circuit_primary.clone(),
            &c_primary,
            num_circuits,
          );
        let mut cs: ShapeCS<E1> = ShapeCS::new();
        let _ = circuit_primary
          .synthesize(&mut cs)
          .expect("failed to synthesize");

        // We use the largest commitment_key for all instances
        let r1cs_shape_primary = cs.r1cs_shape();
        R1CSWithArity::new(r1cs_shape_primary, F_arity)
      })
      .collect::<Vec<_>>();

    let ck_primary = Self::compute_ck_primary(&circuit_shapes, ck_hint_primary);
    let ck_primary = Arc::new(ck_primary);

    let ro_consts_cyclefold = ROConstants::<Dual<E1>>::default();
    let mut cs: ShapeCS<Dual<E1>> = ShapeCS::new();
    let circuit_cyclefold: CycleFoldCircuit<E1> = CycleFoldCircuit::default();
    let _ = circuit_cyclefold.synthesize(&mut cs);
    let (r1cs_shape_cyclefold, ck_cyclefold) = cs.r1cs_shape_and_key(ck_hint_cyclefold);
    let ck_cyclefold = Arc::new(ck_cyclefold);
    let circuit_shape_cyclefold = R1CSWithArity::new(r1cs_shape_cyclefold, 0);

    let pp = Self {
      circuit_shapes,

      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary, // This is shared between all circuit params
      augmented_circuit_params,

      ro_consts_cyclefold,
      ck_cyclefold,
      circuit_shape_cyclefold,

      digest: OnceCell::new(),
    };

    // make sure to initialize the `OnceCell` and compute the digest
    // and avoid paying for unexpected performance costs later
    pp.digest();
    pp
  }

  /// Compute primary and secondary commitment keys sized to handle the largest of the circuits in the provided
  /// `R1CSWithArity`.
  fn compute_ck_primary(
    circuit_params: &[R1CSWithArity<E1>],
    ck_hint1: &CommitmentKeyHint<E1>,
  ) -> CommitmentKey<E1> {
    let size_primary = circuit_params
      .iter()
      .map(|circuit| commitment_key_size(&circuit.r1cs_shape, ck_hint1))
      .max()
      .unwrap();

    E1::CE::setup(b"ck", size_primary)
  }

  /// Return the [`PublicParams`]' digest.
  pub fn digest(&self) -> E1::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc: DigestComputer<'_, <E1 as Engine>::Scalar, Self> = DigestComputer::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure in retrieving digest")
  }
}

/// A SNARK that proves the correct execution of an non-uniform incremental computation
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RecursiveSNARK<E1>
where
  E1: CurveCycleEquipped,
{
  // Cached digest of the public parameters
  pp_digest: E1::Scalar,
  num_augmented_circuits: usize,

  // Number of iterations performed up to now
  i: usize,

  // Inputs and outputs of the primary circuits
  pub(crate) z0_primary: Vec<E1::Scalar>,
  pub(crate) zi_primary: Vec<E1::Scalar>,

  // Proven circuit index, and current program counter
  proven_circuit_index: usize,
  pub(crate) program_counter: E1::Scalar,

  // Relaxed instances for the primary circuits
  // Entries are `None` if the circuit has not been executed yet
  r_W_primary: Vec<Option<RelaxedR1CSWitness<E1>>>,
  r_U_primary: Vec<Option<RelaxedR1CSInstance<E1>>>,
  l_w_primary: R1CSWitness<E1>,
  l_u_primary: R1CSInstance<E1>,

  // cyclefold circuit data
  r_W_cyclefold: RelaxedR1CSWitness<Dual<E1>>,
  r_U_cyclefold: RelaxedR1CSInstance<Dual<E1>>,
}

impl<E1> RecursiveSNARK<E1>
where
  E1: CurveCycleEquipped,
{
  /// Runs the 0'th step of NIVC with CycleFold
  pub fn new<C0: NonUniformCircuit<E1>>(
    pp: &PublicParams<E1>,
    non_uniform_circuit: &C0,
    c_primary: &C0::C1,
    z0_primary: &[E1::Scalar],
  ) -> Result<Self, SuperNovaError> {
    let num_augmented_circuits = non_uniform_circuit.num_circuits();
    let circuit_index = non_uniform_circuit.initial_circuit_index();

    // Get circuit shapes to build base running instances
    let r1cs_cyclefold = &pp.circuit_shape_cyclefold.r1cs_shape;

    // running cyclefold instance
    let r_U_cyclefold = RelaxedR1CSInstance::default(&*pp.ck_cyclefold, r1cs_cyclefold);

    // running cyclefold witness
    let r_W_cyclefold = RelaxedR1CSWitness::default(r1cs_cyclefold);

    // check the arity of all the primary circuits match the initial input length
    pp.circuit_shapes.iter().try_for_each(|circuit| {
      if circuit.F_arity != z0_primary.len() {
        return Err(SuperNovaError::NovaError(
          NovaError::InvalidStepOutputLength,
        ));
      }
      Ok(())
    })?;

    // base case for the primary
    let mut cs_primary = SatisfyingAssignment::<E1>::new();
    let program_counter = E1::Scalar::from(circuit_index as u64);
    let inputs_primary: SuperNovaAugmentedCircuitInputs<'_, Dual<E1>, E1> =
      SuperNovaAugmentedCircuitInputs::new(
        scalar_as_base::<E1>(pp.digest()),
        E1::Scalar::ZERO,
        z0_primary.to_vec(),
        None, // zi = None for basecase
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        Some(program_counter), // pc = initial_program_counter for primary circuit
        E1::Scalar::from(circuit_index as u64), // u_index is always zero for the primary circuit
      );
    let circuit_primary: SuperNovaAugmentedCircuit<'_, Dual<E1>, E1, C0::C1> =
      SuperNovaAugmentedCircuit::new(
        &pp.augmented_circuit_params,
        Some(inputs_primary),
        pp.ro_consts_circuit_primary.clone(),
        c_primary,
        num_augmented_circuits,
      );

    let (zi_primary_pc_next, zi_primary) =
      circuit_primary.synthesize(&mut cs_primary).map_err(|err| {
        debug!("err {:?}", err);
        NovaError::from(err)
      })?;
    if zi_primary.len() != pp[circuit_index].F_arity {
      return Err(SuperNovaError::NovaError(
        NovaError::InvalidStepOutputLength,
      ));
    }
    let (u_primary, w_primary) = cs_primary
      .r1cs_instance_and_witness(&pp[circuit_index].r1cs_shape, &pp.ck_primary)
      .map_err(|err| {
        debug!("err {:?}", err);
        err
      })?;

    // IVC proof for the primary circuit
    let l_w_primary = w_primary;
    let l_u_primary = u_primary;

    // Outputs of the two circuits and next program counter thus far.
    let zi_primary = zi_primary
      .iter()
      .map(|v| {
        v.get_value()
          .ok_or(NovaError::from(SynthesisError::AssignmentMissing).into())
      })
      .collect::<Result<Vec<<E1 as Engine>::Scalar>, SuperNovaError>>()?;
    let zi_primary_pc_next = zi_primary_pc_next
      .expect("zi_primary_pc_next missing")
      .get_value()
      .ok_or::<SuperNovaError>(NovaError::from(SynthesisError::AssignmentMissing).into())?;

    // handle the base case by initialize U_next in next round
    let r_W_primary_initial_list = (0..num_augmented_circuits)
      .map(|i| {
        let c_primary = non_uniform_circuit.primary_circuit(i);
        // TODO: remove option
        Some(RelaxedR1CSWitness::default(
          &pp[c_primary.circuit_index()].r1cs_shape,
        ))
      })
      .collect::<Vec<Option<RelaxedR1CSWitness<E1>>>>();

    let r_U_primary_initial_list = (0..num_augmented_circuits)
      .map(|i| {
        let c_primary = non_uniform_circuit.primary_circuit(i);
        Some(RelaxedR1CSInstance::default(
          &*pp.ck_primary,
          &pp[c_primary.circuit_index()].r1cs_shape,
        ))
      })
      .collect::<Vec<Option<RelaxedR1CSInstance<E1>>>>();
    // let r_U_primary_initial_list = (0..num_augmented_circuits)
    //   .map(|i| Some(r_U_primary.clone()))
    //   .collect::<Vec<Option<RelaxedR1CSInstance<E1>>>>();

    Ok(Self {
      pp_digest: pp.digest(),
      num_augmented_circuits,
      i: 0,
      z0_primary: z0_primary.to_vec(),
      zi_primary,
      proven_circuit_index: circuit_index,
      program_counter: zi_primary_pc_next,
      r_W_primary: r_W_primary_initial_list,
      r_U_primary: r_U_primary_initial_list,
      l_w_primary,
      l_u_primary,
      r_W_cyclefold,
      r_U_cyclefold,
    })
  }

  /// Run the i'th step of NIVC with CycleFold
  pub fn prove_step<C1: StepCircuit<E1::Scalar>>(
    &mut self,
    pp: &PublicParams<E1>,
    c_primary: &C1,
  ) -> Result<(), SuperNovaError> {
    // First step was already done in the constructor
    if self.i == 0 {
      self.i = 1;
      return Ok(());
    }
    let circuit_index = c_primary.circuit_index();
    let proven_circuit_index = self.proven_circuit_index;
    assert_eq!(self.program_counter, E1::Scalar::from(circuit_index as u64));
    // Fold previous U & W into running_primary_instance & running_primary_witness
    // get new primary_running_instance & new running_primary_witness

    let r_U_primary_i = self.r_U_primary[proven_circuit_index].as_ref().unwrap();
    let r_W_primary_i = self.r_W_primary[proven_circuit_index].as_ref().unwrap();

    let (nifs_primary, (r_U_primary, r_W_primary), r) = PrimaryNIFS::<E1, Dual<E1>>::prove(
      &pp.ck_primary,
      &pp.ro_consts_primary,
      &pp.digest(),
      &pp[proven_circuit_index].r1cs_shape,
      r_U_primary_i,
      r_W_primary_i,
      &self.l_u_primary,
      &self.l_w_primary,
    )?;

    // Get challenge
    let r_bools = r
      .to_le_bits()
      .iter()
      .map(|b| Some(*b))
      .take(NUM_CHALLENGE_BITS)
      .collect::<Option<Vec<_>>>()
      .map(|v| v.try_into().unwrap());

    // Emulated values
    let comm_T = Commitment::<E1>::decompress(&nifs_primary.comm_T)?;
    let E_new = r_U_primary_i.comm_E + comm_T * r;

    let W_new = r_U_primary_i.comm_W + self.l_u_primary.comm_W * r;

    // Cyclefold instance to compute E_new = comm_E + comm_T * r;
    let mut cs_cyclefold_E = SatisfyingAssignment::<Dual<E1>>::with_capacity(
      pp.circuit_shape_cyclefold.r1cs_shape.num_io + 1,
      pp.circuit_shape_cyclefold.r1cs_shape.num_vars,
    );

    let circuit_cyclefold_E: CycleFoldCircuit<E1> =
      CycleFoldCircuit::new(Some(r_U_primary_i.comm_E), Some(comm_T), r_bools);

    let _ = circuit_cyclefold_E.synthesize(&mut cs_cyclefold_E);

    // Get cyclefold_instance_E, cyclefold_witness_E
    let (l_u_cyclefold_E, l_w_cyclefold_E) = cs_cyclefold_E
      .r1cs_instance_and_witness(&pp.circuit_shape_cyclefold.r1cs_shape, &pp.ck_cyclefold)
      .map_err(|_| NovaError::UnSat)?;

    // Fold cyclefold_instance_E into running_cycleFold_instance
    // Fold cyclefold_witnesss_E into running_cycleFold_witness
    //
    // Get running_cyclefold_instance_E, running_cyclefold_witness_E and comm_T_E
    let (nifs_cyclefold_E, (r_U_cyclefold_E, r_W_cyclefold_E)) = CycleFoldNIFS::prove(
      &*pp.ck_cyclefold,
      &pp.ro_consts_cyclefold,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.circuit_shape_cyclefold.r1cs_shape,
      &self.r_U_cyclefold,
      &self.r_W_cyclefold,
      &l_u_cyclefold_E,
      &l_w_cyclefold_E,
    )?;

    // Get comm_T_E for folding data c_E
    let comm_T_E = Commitment::<Dual<E1>>::decompress(&nifs_cyclefold_E.comm_T)?;

    // Cyclefold instance to compute W_new = comm_W + comm_W * r;
    let mut cs_cyclefold_W = SatisfyingAssignment::<Dual<E1>>::with_capacity(
      pp.circuit_shape_cyclefold.r1cs_shape.num_io + 1,
      pp.circuit_shape_cyclefold.r1cs_shape.num_vars,
    );

    let circuit_cyclefold_W: CycleFoldCircuit<E1> = CycleFoldCircuit::new(
      Some(r_U_primary_i.comm_W),
      Some(self.l_u_primary.comm_W),
      r_bools,
    );

    let _ = circuit_cyclefold_W.synthesize(&mut cs_cyclefold_W);

    // get cyclefold_instance_W and cyclefold_witness_W
    let (l_u_cyclefold_W, l_w_cyclefold_W) = cs_cyclefold_W
      .r1cs_instance_and_witness(&pp.circuit_shape_cyclefold.r1cs_shape, &pp.ck_cyclefold)
      .map_err(|_| NovaError::UnSat)?;

    // Fold cyclefold_instance_W into running_cyclefold_instance_E
    // Fold cyclefold_witness_W into running_cyclefold_witness_E
    //
    // Get running_cyclefold_instance_W, running_cyclefold_witness_W and comm_T_W
    let (nifs_cyclefold_W, (r_U_cyclefold_W, r_W_cyclefold_W)) = CycleFoldNIFS::prove(
      &*pp.ck_cyclefold,
      &pp.ro_consts_cyclefold,
      &scalar_as_base::<E1>(pp.digest()),
      &pp.circuit_shape_cyclefold.r1cs_shape,
      &r_U_cyclefold_E,
      &r_W_cyclefold_E,
      &l_u_cyclefold_W,
      &l_w_cyclefold_W,
    )?;

    // Get comm_T_W for folding data c_W
    let comm_T_W = Commitment::<Dual<E1>>::decompress(&nifs_cyclefold_W.comm_T)?;

    // cyclefold_running_instance, cyclefold_instance_E, commT_E
    let data_c_E = FoldingData::new(self.r_U_cyclefold.clone(), l_u_cyclefold_E, comm_T_E);

    // cyclefold_running_instance_E, cyclefold_instance_W, commT_W
    let data_c_W = FoldingData::new(r_U_cyclefold_E, l_u_cyclefold_W, comm_T_W);

    let mut cs_primary = SatisfyingAssignment::<E1>::with_capacity(
      pp[circuit_index].r1cs_shape.num_io + 1,
      pp[circuit_index].r1cs_shape.num_vars,
    );

    let inputs_primary: SuperNovaAugmentedCircuitInputs<'_, Dual<E1>, E1> =
      SuperNovaAugmentedCircuitInputs::new(
        scalar_as_base::<E1>(pp.digest()),
        E1::Scalar::from(self.i as u64),
        self.z0_primary.clone(),
        Some(self.zi_primary.clone()), // zi = None for basecase
        Some(&self.r_U_primary),
        Some(self.l_u_primary.clone()),
        Some(comm_T),
        Some(data_c_E),
        Some(data_c_W),
        Some(E_new),
        Some(W_new),
        Some(self.program_counter), // pc = initial_program_counter for primary circuit
        E1::Scalar::from(proven_circuit_index as u64),
      );

    let circuit_primary: SuperNovaAugmentedCircuit<'_, Dual<E1>, E1, C1> =
      SuperNovaAugmentedCircuit::new(
        &pp.augmented_circuit_params,
        Some(inputs_primary),
        pp.ro_consts_circuit_primary.clone(),
        c_primary,
        self.num_augmented_circuits,
      );

    let (zi_primary_pc_next, zi_primary) = circuit_primary
      .synthesize(&mut cs_primary)
      .map_err(NovaError::from)?;

    if zi_primary.len() != pp[circuit_index].F_arity {
      return Err(SuperNovaError::NovaError(
        NovaError::InvalidInitialInputLength,
      ));
    }

    let (l_u_primary, l_w_primary) = cs_primary
      .r1cs_instance_and_witness(&pp[circuit_index].r1cs_shape, &pp.ck_primary)
      .map_err(SuperNovaError::NovaError)?;

    // update the running instances and witnesses
    let zi_primary = zi_primary
      .iter()
      .map(|v| {
        v.get_value()
          .ok_or(NovaError::from(SynthesisError::AssignmentMissing).into())
      })
      .collect::<Result<Vec<<E1 as Engine>::Scalar>, SuperNovaError>>()?;

    let zi_primary_pc_next = zi_primary_pc_next
      .expect("zi_primary_pc_next missing")
      .get_value()
      .ok_or::<SuperNovaError>(NovaError::from(SynthesisError::AssignmentMissing).into())?;

    // running primary Instance
    self.r_U_primary[proven_circuit_index] = Some(r_U_primary);

    // running primary Witness
    self.r_W_primary[proven_circuit_index] = Some(r_W_primary);

    // U
    self.l_u_primary = l_u_primary;

    // W
    self.l_w_primary = l_w_primary;

    // running cyclefold Instance
    self.r_U_cyclefold = r_U_cyclefold_W;

    // running cyclefold Witness
    self.r_W_cyclefold = r_W_cyclefold_W;

    self.zi_primary = zi_primary;

    self.proven_circuit_index = circuit_index;
    self.program_counter = zi_primary_pc_next;
    self.i += 1;
    Ok(())
  }

  /// Verify the i'th step of NIVC with CycleFold
  pub fn verify(
    &self,
    pp: &PublicParams<E1>,
    z0_primary: &[E1::Scalar],
  ) -> Result<Vec<E1::Scalar>, SuperNovaError> {
    // number of steps cannot be zero
    if self.i == 0 {
      debug!("must verify on valid RecursiveSNARK where i > 0");
      return Err(SuperNovaError::NovaError(NovaError::ProofVerifyError));
    }

    // Check lengths of r_primary
    if self.r_U_primary.len() != self.num_augmented_circuits
      || self.r_W_primary.len() != self.num_augmented_circuits
    {
      debug!("r_primary length mismatch");
      return Err(SuperNovaError::NovaError(NovaError::ProofVerifyError));
    }

    // Check that there are no missing instance/witness pairs
    self
      .r_U_primary
      .iter()
      .zip_eq(self.r_W_primary.iter())
      .enumerate()
      .try_for_each(|(i, (u, w))| match (u, w) {
        (Some(_), Some(_)) | (None, None) => Ok(()),
        _ => {
          debug!("r_primary[{:?}]: mismatched instance/witness pair", i);
          Err(SuperNovaError::NovaError(NovaError::ProofVerifyError))
        }
      })?;

    let circuit_index = self.proven_circuit_index;
    // check we have an instance/witness pair for the circuit_index
    if self.r_U_primary[circuit_index].is_none() {
      debug!(
        "r_primary[{:?}]: instance/witness pair is missing",
        circuit_index
      );
      return Err(SuperNovaError::NovaError(NovaError::ProofVerifyError));
    }

    // check the (relaxed) R1CS instances public outputs.
    {
      for (i, r_U_primary_i) in self.r_U_primary.iter().enumerate() {
        if let Some(u) = r_U_primary_i {
          if u.X.len() != 2 {
            debug!(
              "r_U_primary[{:?}] got instance length {:?} != 2",
              i,
              u.X.len(),
            );
            return Err(SuperNovaError::NovaError(NovaError::ProofVerifyError));
          }
        }
      }

      if self.l_u_primary.X.len() != 2 {
        debug!(
          "l_u_primary got instance length {:?} != 2",
          self.l_u_primary.X.len(),
        );
        return Err(SuperNovaError::NovaError(NovaError::ProofVerifyError));
      }
    }

    // Calculate the hashes of the primary running instance and cyclefold running instance
    let (hash_primary, hash_cyclefold) = {
      let mut hasher = <Dual<E1> as Engine>::RO::new(
        pp.ro_consts_primary.clone(),
        2 + 2 * pp[circuit_index].F_arity
          + self.num_augmented_circuits * (2 * NUM_FE_IN_EMULATED_POINT + 3)
          + 1,
      );
      hasher.absorb(pp.digest());
      hasher.absorb(E1::Scalar::from(self.i as u64));
      hasher.absorb(self.program_counter);
      for e in z0_primary {
        hasher.absorb(*e);
      }
      for e in &self.zi_primary {
        hasher.absorb(*e);
      }

      self.r_U_primary.iter().for_each(|U| {
        let r_U_primary_i = U.as_ref().unwrap();

        absorb_primary_relaxed_r1cs::<E1, Dual<E1>>(r_U_primary_i, &mut hasher);
      });
      let hash_primary = hasher.squeeze(NUM_HASH_BITS);

      // hash cyclefold
      let mut hasher = <Dual<E1> as Engine>::RO::new(
        pp.ro_consts_cyclefold.clone(),
        1 + 1 + 3 + 3 + 1 + NIO_CYCLE_FOLD * BN_N_LIMBS,
      );
      hasher.absorb(pp.digest());
      hasher.absorb(E1::Scalar::from(self.i as u64));
      self.r_U_cyclefold.absorb_in_ro(&mut hasher);
      let hash_cyclefold = hasher.squeeze(NUM_HASH_BITS);

      (hash_primary, hash_cyclefold)
    };

    // Verify the hashes equal the public IO for the final primary instance
    if scalar_as_base::<Dual<E1>>(hash_primary) != self.l_u_primary.X[0]
      || scalar_as_base::<Dual<E1>>(hash_cyclefold) != self.l_u_primary.X[1]
    {
      return Err(SuperNovaError::NovaError(NovaError::ProofVerifyError));
    }

    // check the satisfiability of all instance/witness pairs
    let (res_r_primary, (res_l_primary, res_r_cyclefold)) = rayon::join(
      || {
        self
          .r_U_primary
          .par_iter()
          .zip_eq(self.r_W_primary.par_iter())
          .enumerate()
          .try_for_each(|(i, (u, w))| {
            if let (Some(u), Some(w)) = (u, w) {
              pp[i].r1cs_shape.is_sat_relaxed(&pp.ck_primary, u, w)?
            }
            Ok::<(), NovaError>(())
          })
      },
      || {
        rayon::join(
          || {
            pp[circuit_index].r1cs_shape.is_sat(
              &pp.ck_primary,
              &self.l_u_primary,
              &self.l_w_primary,
            )
          },
          || {
            pp.circuit_shape_cyclefold.r1cs_shape.is_sat_relaxed(
              &pp.ck_cyclefold,
              &self.r_U_cyclefold,
              &self.r_W_cyclefold,
            )
          },
        )
      },
    );

    res_r_primary?;
    res_l_primary?;
    res_r_cyclefold?;

    Ok(z0_primary.to_vec())
  }
}
