//! This module defines the public parameters and other supporting structures used by Nova and SuperNova

use once_cell::sync::OnceCell;

use crate::circuit::{AugmentedCircuitParams, NovaAugmentedCircuit};
use crate::constants::{BN_LIMB_WIDTH, BN_N_LIMBS};
use crate::digest::{DigestComputer, SimpleDigestible};
use crate::r1cs::R1CSShape;
use crate::traits::{
  circuit, circuit_supernova, commitment::CommitmentEngineTrait, Group, ROConstants,
  ROConstantsCircuit,
};
use crate::{
  bellpepper::{r1cs::NovaShape, shape_cs::ShapeCS},
  r1cs::{commitment_key_size, CommitmentKeyHint},
  supernova::{circuit::SuperNovaAugmentedCircuit, NonUniformCircuit},
  CommitmentKey,
};
use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use core::marker::PhantomData;
use ff::PrimeField;
use serde::{Deserialize, Serialize};
use std::ops::Index;

/// A type that holds parameters for the primary and secondary circuits of Nova and SuperNova
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(where <G::Scalar as PrimeField>::Repr: Abomonation)]
pub struct CircuitShape<G: Group> {
  pub(crate) F_arity: usize,
  pub(crate) r1cs_shape: R1CSShape<G>,
}

impl<G: Group> SimpleDigestible for CircuitShape<G> {}

impl<G: Group> CircuitShape<G> {
  /// Create a new `CircuitShape`
  pub fn new(r1cs_shape: R1CSShape<G>, F_arity: usize) -> Self {
    Self {
      F_arity,
      r1cs_shape,
    }
  }

  /// Return the [CircuitShape]' digest.
  pub fn digest(&self) -> G::Scalar {
    let dc: DigestComputer<'_, <G as Group>::Scalar, CircuitShape<G>> = DigestComputer::new(self);
    dc.digest().expect("Failure in computing digest")
  }
}

/// A struct that manages all the digests of the primary circuits of a SuperNova instance
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CircuitDigests<G: Group> {
  digests: Vec<G::Scalar>,
}

impl<G: Group> SimpleDigestible for CircuitDigests<G> {}

impl<G: Group> std::ops::Deref for CircuitDigests<G> {
  type Target = Vec<G::Scalar>;

  fn deref(&self) -> &Self::Target {
    &self.digests
  }
}

impl<G: Group> CircuitDigests<G> {
  /// Construct a new [CircuitDigests]
  pub fn new(digests: Vec<G::Scalar>) -> Self {
    CircuitDigests { digests }
  }

  /// Return the [CircuitDigests]' digest.
  pub fn digest(&self) -> G::Scalar {
    let dc: DigestComputer<'_, <G as Group>::Scalar, CircuitDigests<G>> = DigestComputer::new(self);
    dc.digest().expect("Failure in computing digest")
  }
}

/// A vector of [CircuitParams] corresponding to a set of [PublicParams]
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  /// The internal circuit shapes
  pub circuit_shapes: Vec<CircuitShape<G1>>,

  pub(crate) ro_consts_primary: ROConstants<G1>,
  pub(crate) ro_consts_circuit_primary: ROConstantsCircuit<G2>,
  pub(crate) ck_primary: CommitmentKey<G1>, // This is shared between all circuit params
  pub(crate) augmented_circuit_params_primary: AugmentedCircuitParams,

  pub(crate) ro_consts_secondary: ROConstants<G2>,
  pub(crate) ro_consts_circuit_secondary: ROConstantsCircuit<G1>,
  pub(crate) ck_secondary: CommitmentKey<G2>,
  pub(crate) circuit_shape_secondary: CircuitShape<G2>,
  pub(crate) augmented_circuit_params_secondary: AugmentedCircuitParams,

  /// Digest constructed from this `PublicParams`' parameters
  #[serde(skip, default = "OnceCell::new")]
  pub(crate) digest: OnceCell<G1::Scalar>,
  _p: PhantomData<(C1, C2)>,
}

/// Auxilliary [PublicParams] information about the commitment keys and
/// secondary circuit. This is used as a helper struct when reconstructing
/// [PublicParams] downstream in lurk.
#[derive(Clone, PartialEq, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  <G1::Scalar as PrimeField>::Repr: Abomonation,
  <G2::Scalar as PrimeField>::Repr: Abomonation,
)]
pub struct AuxParams<G1, G2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  ro_consts_primary: ROConstants<G1>,
  ro_consts_circuit_primary: ROConstantsCircuit<G2>,
  ck_primary: CommitmentKey<G1>, // This is shared between all circuit params
  augmented_circuit_params_primary: AugmentedCircuitParams,

  ro_consts_secondary: ROConstants<G2>,
  ro_consts_circuit_secondary: ROConstantsCircuit<G1>,
  ck_secondary: CommitmentKey<G2>,
  circuit_shape_secondary: CircuitShape<G2>,
  augmented_circuit_params_secondary: AugmentedCircuitParams,

  #[abomonate_with(<G1::Scalar as PrimeField>::Repr)]
  digest: G1::Scalar,
}

impl<G1, G2, C1, C2> Index<usize> for PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  type Output = CircuitShape<G1>;

  fn index(&self, index: usize) -> &Self::Output {
    &self.circuit_shapes[index]
  }
}

impl<G1, G2, C1, C2> SimpleDigestible for PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
}

impl<G1, G2, C1, C2> PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
{
  /// Create [PublicParams] for Nova from a pair of circuits `C1` and `C2`.
  ///
  /// # Note
  ///
  /// Some SNARKs, like variants of Spartan, use computation commitments that require
  /// larger sizes for some parameters. These SNARKs provide a hint for these values by
  /// implementing `RelaxedR1CSSNARKTrait::commitment_key_floor()`, which can be passed to this function.
  /// If you're not using such a SNARK, pass `None` instead.
  ///
  /// # Arguments
  ///
  /// * `c_primary`: The primary circuit of type `C1`.
  /// * `c_secondary`: The secondary circuit of type `C2`.
  /// * `optfn1`: An optional `CommitmentKeyHint` for `G1`, which is a function that provides a hint
  ///   for the number of generators required in the commitment scheme for the primary circuit.
  /// * `optfn2`: An optional `CommitmentKeyHint` for `G2`, similar to `optfn1`, but for the secondary circuit.
  ///
  /// # Example
  ///
  /// ```rust
  /// # use pasta_curves::{vesta, pallas};
  /// # use nova_snark::spartan::ppsnark::RelaxedR1CSSNARK;
  /// # use nova_snark::provider::ipa_pc::EvaluationEngine;
  /// # use nova_snark::traits::{circuit::TrivialTestCircuit, Group, snark::RelaxedR1CSSNARKTrait};
  /// use nova_snark::parameters::PublicParams;
  ///
  /// type G1 = pallas::Point;
  /// type G2 = vesta::Point;
  /// type EE<G> = EvaluationEngine<G>;
  /// type SPrime<G> = RelaxedR1CSSNARK<G, EE<G>>;
  ///
  /// let circuit1 = TrivialTestCircuit::<<G1 as Group>::Scalar>::default();
  /// let circuit2 = TrivialTestCircuit::<<G2 as Group>::Scalar>::default();
  /// // Only relevant for a SNARK using computational commitments, pass None otherwise.
  /// let pp_hint1 = Some(SPrime::<G1>::commitment_key_floor());
  /// let pp_hint2 = Some(SPrime::<G2>::commitment_key_floor());
  ///
  /// let pp = PublicParams::new(&circuit1, &circuit2, pp_hint1, pp_hint2);
  /// ```
  pub fn new(
    c_primary: &C1,
    c_secondary: &C2,
    optfn1: Option<CommitmentKeyHint<G1>>,
    optfn2: Option<CommitmentKeyHint<G2>>,
  ) -> Self
  where
    C1: circuit::StepCircuit<G1::Scalar>,
    C2: circuit::StepCircuit<G2::Scalar>,
  {
    let augmented_circuit_params_primary =
      AugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let augmented_circuit_params_secondary =
      AugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);

    let ro_consts_primary: ROConstants<G1> = ROConstants::<G1>::default();
    let ro_consts_secondary: ROConstants<G2> = ROConstants::<G2>::default();

    let F_arity_primary = c_primary.arity();
    let F_arity_secondary = c_secondary.arity();

    // ro_consts_circuit_primary are parameterized by G2 because the type alias uses G2::Base = G1::Scalar
    let ro_consts_circuit_primary: ROConstantsCircuit<G2> = ROConstantsCircuit::<G2>::default();
    let ro_consts_circuit_secondary: ROConstantsCircuit<G1> = ROConstantsCircuit::<G1>::default();

    // Initialize ck for the primary
    let circuit_primary: NovaAugmentedCircuit<'_, G2, C1> = NovaAugmentedCircuit::new(
      &augmented_circuit_params_primary,
      None,
      c_primary,
      ro_consts_circuit_primary.clone(),
    );
    let mut cs: ShapeCS<G1> = ShapeCS::new();
    let _ = circuit_primary.synthesize(&mut cs);
    let (r1cs_shape_primary, ck_primary) = cs.r1cs_shape_and_key(optfn1);
    let circuit_shape_primary = CircuitShape::new(r1cs_shape_primary, F_arity_primary);

    // Initialize ck for the secondary
    let circuit_secondary: NovaAugmentedCircuit<'_, G1, C2> = NovaAugmentedCircuit::new(
      &augmented_circuit_params_secondary,
      None,
      c_secondary,
      ro_consts_circuit_secondary.clone(),
    );
    let mut cs: ShapeCS<G2> = ShapeCS::new();
    let _ = circuit_secondary.synthesize(&mut cs);
    let (r1cs_shape_secondary, ck_secondary) = cs.r1cs_shape_and_key(optfn2);
    let circuit_shape_secondary = CircuitShape::new(r1cs_shape_secondary, F_arity_secondary);

    PublicParams {
      circuit_shapes: vec![circuit_shape_primary],
      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary,
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

  /// Create [PublicParams] for Nova from a pair of circuits `C1` and `C2`.
  ///
  /// # Note
  ///
  /// Some SNARKs, like variants of Spartan, use computation commitments that require
  /// larger sizes for some parameters. These SNARKs provide a hint for these values by
  /// implementing `RelaxedR1CSSNARKTrait::commitment_key_floor()`, which can be passed to this function.
  /// If you're not using such a SNARK, pass `None` instead.
  ///
  /// # Arguments
  ///
  /// * `non_unifrom_circuit`: The sets of sub-circuits of type `C1` to be proved via NIVC.
  /// * `optfn1`: An optional `CommitmentKeyHint` for `G1`, which is a function that provides a hint
  ///   for the number of generators required in the commitment scheme for all the sub-circuits.
  /// * `optfn2`: An optional `CommitmentKeyHint` for `G2`, similar to `optfn1`, but for the secondary circuit.
  pub fn new_supernova<NC: NonUniformCircuit<G1, G2, C1, C2>>(
    non_unifrom_circuit: &NC,
    optfn1: Option<CommitmentKeyHint<G1>>,
    optfn2: Option<CommitmentKeyHint<G2>>,
  ) -> Self
  where
    C1: circuit_supernova::StepCircuit<G1::Scalar>,
    C2: circuit_supernova::StepCircuit<G2::Scalar>,
  {
    let num_circuits = non_unifrom_circuit.num_circuits();

    let augmented_circuit_params_primary =
      AugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let ro_consts_primary: ROConstants<G1> = ROConstants::<G1>::default();
    // ro_consts_circuit_primary are parameterized by G2 because the type alias uses G2::Base = G1::Scalar
    let ro_consts_circuit_primary: ROConstantsCircuit<G2> = ROConstantsCircuit::<G2>::default();

    let circuit_shapes = (0..num_circuits)
      .map(|i| {
        let c_primary = non_unifrom_circuit.primary_circuit(i);
        let F_arity = c_primary.arity();
        // Initialize ck for the primary
        let circuit_primary: SuperNovaAugmentedCircuit<'_, G2, C1> = SuperNovaAugmentedCircuit::new(
          &augmented_circuit_params_primary,
          None,
          &c_primary,
          ro_consts_circuit_primary.clone(),
          num_circuits,
        );
        let mut cs: ShapeCS<G1> = ShapeCS::new();
        let _ = circuit_primary.synthesize(&mut cs);
        // We use the largest commitment_key for all instances
        let r1cs_shape_primary = cs.r1cs_shape();
        CircuitShape::new(r1cs_shape_primary, F_arity)
      })
      .collect::<Vec<_>>();

    let ck_primary = Self::compute_primary_ck(&circuit_shapes, optfn1);

    let augmented_circuit_params_secondary =
      AugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);
    let ro_consts_secondary: ROConstants<G2> = ROConstants::<G2>::default();
    let c_secondary = non_unifrom_circuit.secondary_circuit();
    let F_arity_secondary = c_secondary.arity();
    let ro_consts_circuit_secondary: ROConstantsCircuit<G1> = ROConstantsCircuit::<G1>::default();

    let circuit_secondary: SuperNovaAugmentedCircuit<'_, G1, C2> = SuperNovaAugmentedCircuit::new(
      &augmented_circuit_params_secondary,
      None,
      &c_secondary,
      ro_consts_circuit_secondary.clone(),
      num_circuits,
    );
    let mut cs: ShapeCS<G2> = ShapeCS::new();
    let _ = circuit_secondary.synthesize(&mut cs);
    let (r1cs_shape_secondary, ck_secondary) = cs.r1cs_shape_and_key(optfn2);
    let circuit_shape_secondary = CircuitShape::new(r1cs_shape_secondary, F_arity_secondary);

    let pp = PublicParams {
      circuit_shapes,
      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary,
      augmented_circuit_params_primary,
      ro_consts_secondary,
      ro_consts_circuit_secondary,
      ck_secondary,
      circuit_shape_secondary,
      augmented_circuit_params_secondary,
      digest: OnceCell::new(),
      _p: PhantomData,
    };

    // make sure to initialize the `OnceCell` and compute the digest
    // and avoid paying for unexpected performance costs later
    pp.digest();
    pp
  }

  /// Breaks down an instance of [PublicParams] into the circuit params and auxilliary params.
  pub fn into_parts(self) -> (Vec<CircuitShape<G1>>, AuxParams<G1, G2>) {
    let digest = self.digest();

    let PublicParams {
      circuit_shapes,
      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary,
      augmented_circuit_params_primary,
      ro_consts_secondary,
      ro_consts_circuit_secondary,
      ck_secondary,
      circuit_shape_secondary,
      augmented_circuit_params_secondary,
      digest: _digest,
      _p,
    } = self;

    let aux_params = AuxParams {
      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary,
      augmented_circuit_params_primary,
      ro_consts_secondary,
      ro_consts_circuit_secondary,
      ck_secondary,
      circuit_shape_secondary,
      augmented_circuit_params_secondary,
      digest,
    };

    (circuit_shapes, aux_params)
  }

  /// Create a [PublicParams] from a vector of raw [CircuitShape] and auxilliary params.
  pub fn from_parts(circuit_shapes: Vec<CircuitShape<G1>>, aux_params: AuxParams<G1, G2>) -> Self {
    let pp = PublicParams {
      circuit_shapes,
      ro_consts_primary: aux_params.ro_consts_primary,
      ro_consts_circuit_primary: aux_params.ro_consts_circuit_primary,
      ck_primary: aux_params.ck_primary,
      augmented_circuit_params_primary: aux_params.augmented_circuit_params_primary,
      ro_consts_secondary: aux_params.ro_consts_secondary,
      ro_consts_circuit_secondary: aux_params.ro_consts_circuit_secondary,
      ck_secondary: aux_params.ck_secondary,
      circuit_shape_secondary: aux_params.circuit_shape_secondary,
      augmented_circuit_params_secondary: aux_params.augmented_circuit_params_secondary,
      digest: OnceCell::new(),
      _p: PhantomData,
    };
    assert_eq!(
      aux_params.digest,
      pp.digest(),
      "param data is invalid; aux_params contained the incorrect digest"
    );
    pp
  }

  /// Create a [PublicParams] from a vector of raw [CircuitShape] and auxilliary params.
  /// We don't check that the `aux_params.digest` is a valid digest for the created params.
  pub fn from_parts_unchecked(
    circuit_shapes: Vec<CircuitShape<G1>>,
    aux_params: AuxParams<G1, G2>,
  ) -> Self {
    PublicParams {
      circuit_shapes,
      ro_consts_primary: aux_params.ro_consts_primary,
      ro_consts_circuit_primary: aux_params.ro_consts_circuit_primary,
      ck_primary: aux_params.ck_primary,
      augmented_circuit_params_primary: aux_params.augmented_circuit_params_primary,
      ro_consts_secondary: aux_params.ro_consts_secondary,
      ro_consts_circuit_secondary: aux_params.ro_consts_circuit_secondary,
      ck_secondary: aux_params.ck_secondary,
      circuit_shape_secondary: aux_params.circuit_shape_secondary,
      augmented_circuit_params_secondary: aux_params.augmented_circuit_params_secondary,
      digest: aux_params.digest.into(),
      _p: PhantomData,
    }
  }

  /// Compute primary and secondary commitment keys sized to handle the largest of the circuits in the provided
  /// `CircuitShape`.
  fn compute_primary_ck(
    circuit_params: &[CircuitShape<G1>],
    optfn1: Option<CommitmentKeyHint<G1>>,
  ) -> CommitmentKey<G1> {
    let size_primary = circuit_params
      .iter()
      .map(|circuit| commitment_key_size(&circuit.r1cs_shape, optfn1.clone()))
      .max()
      .unwrap();

    G1::CE::setup(b"ck", size_primary)
  }

  /// Return the [PublicParams]' digest.
  pub fn digest(&self) -> G1::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc: DigestComputer<'_, <G1 as Group>::Scalar, PublicParams<G1, G2, C1, C2>> =
          DigestComputer::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure in retrieving digest")
  }

  /// All of the primary circuit digests of this [PublicParams]
  pub fn circuit_param_digests(&self) -> CircuitDigests<G1> {
    let digests = self
      .circuit_shapes
      .iter()
      .map(|cp| cp.digest())
      .collect::<Vec<_>>();
    CircuitDigests { digests }
  }

  /// Returns the number of constraints in the primary and secondary circuits
  pub fn num_constraints(&self) -> (usize, usize) {
    (
      self.circuit_shapes[0].r1cs_shape.num_cons,
      self.circuit_shape_secondary.r1cs_shape.num_cons,
    )
  }

  /// Returns the number of variables in the primary and secondary circuits
  pub fn num_variables(&self) -> (usize, usize) {
    (
      self.circuit_shapes[0].r1cs_shape.num_vars,
      self.circuit_shape_secondary.r1cs_shape.num_vars,
    )
  }

  /// Returns the number of constraints in the primary and secondary circuits
  pub fn r1cs_shape_secondary(&self) -> &R1CSShape<G2> {
    &self.circuit_shape_secondary.r1cs_shape
  }

  /// Returns the number of variables in the primary and secondary circuits
  pub fn F_arity_secondary(&self) -> usize {
    self.circuit_shape_secondary.F_arity
  }
}
