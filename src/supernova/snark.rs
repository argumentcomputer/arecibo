//! This module defines a final compressing SNARK for supernova proofs

use super::{error::SuperNovaError, PublicParams, RecursiveSNARK};
use crate::traits::{
  circuit_supernova::StepCircuit,
  snark::{BatchedRelaxedR1CSSNARKTrait, RelaxedR1CSSNARKTrait},
  Group,
};

use ff::PrimeField;
use std::marker::PhantomData;

/// TODO: Doc
pub struct ProverKey<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: BatchedRelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  _p: PhantomData<(G1, G2, C1, C2, S1, S2)>,
}

/// TODO: Doc
pub struct VerifierKey<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: BatchedRelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  _p: PhantomData<(G1, G2, C1, C2, S1, S2)>,
}

/// TODO: Doc
#[derive(Debug, Clone)]
pub struct CompressedSNARK<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: BatchedRelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  _p: PhantomData<(G1, G2, C1, C2, S1, S2)>,
}

impl<G1, G2, C1, C2, S1, S2> CompressedSNARK<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: BatchedRelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  /// TODO: Doc
  pub fn setup(
    pp: &PublicParams<G1, G2, C1, C2>,
  ) -> Result<
    (
      ProverKey<G1, G2, C1, C2, S1, S2>,
      VerifierKey<G1, G2, C1, C2, S1, S2>,
    ),
    SuperNovaError,
  > {
    todo!()
  }

  /// TODO: Doc
  pub fn prove(
    pp: &PublicParams<G1, G2, C1, C2>,
    pk: &ProverKey<G1, G2, C1, C2, S1, S2>,
    recursive_snark: &RecursiveSNARK<G1, G2>,
  ) -> Result<Self, SuperNovaError> {
    todo!()
  }

  /// TODO: Doc
  pub fn verify(
    &self,
    pp: &PublicParams<G1, G2, C1, C2>,
    vk: &VerifierKey<G1, G2, C1, C2, S1, S2>,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<(Vec<G1::Scalar>, Vec<G2::Scalar>), SuperNovaError> {
    todo!()
  }
}

// TODO: change tests so they don't use this (though I think it's needed in `verify`)
fn field_as_usize<F: PrimeField>(x: F) -> usize {
  u32::from_le_bytes(x.to_repr().as_ref()[0..4].try_into().unwrap()) as usize
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    provider::{
      bn256_grumpkin::{bn256, grumpkin},
      ipa_pc::EvaluationEngine,
      secp_secq::{secp256k1, secq256k1},
    },
    spartan::snark::RelaxedR1CSSNARK,
    supernova::NonUniformCircuit,
    traits::{
      circuit_supernova::TrivialSecondaryCircuit, evaluation::EvaluationEngineTrait,
      snark::default_commitment_key_hint,
    },
  };

  use abomonation::Abomonation;
  use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
  use ff::{Field, PrimeField};
  use pasta_curves::{pallas, vesta};

  type EE<G> = EvaluationEngine<G>;
  type S<G, EE> = RelaxedR1CSSNARK<G, EE>;

  #[derive(Clone)]
  struct SquareCircuit<G: Group> {
    _p: PhantomData<G>,
  }

  impl<G: Group> StepCircuit<G::Scalar> for SquareCircuit<G> {
    fn arity(&self) -> usize {
      1
    }

    fn circuit_index(&self) -> usize {
      0
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
      &self,
      cs: &mut CS,
      _pc: Option<&AllocatedNum<G::Scalar>>,
      z: &[AllocatedNum<G::Scalar>],
    ) -> Result<
      (
        Option<AllocatedNum<G::Scalar>>,
        Vec<AllocatedNum<G::Scalar>>,
      ),
      SynthesisError,
    > {
      let z_i = &z[0];

      let z_next = z_i.square(cs.namespace(|| "z_i^2"))?;

      let next_pc = AllocatedNum::alloc(cs.namespace(|| "next_pc"), || Ok(G::Scalar::from(1u64)))?;

      cs.enforce(
        || "next_pc = 1",
        |lc| lc + CS::one(),
        |lc| lc + next_pc.get_variable(),
        |lc| lc + CS::one(),
      );

      Ok((Some(next_pc), vec![z_next]))
    }
  }

  #[derive(Clone)]
  struct CubeCircuit<G: Group> {
    _p: PhantomData<G>,
  }

  impl<G: Group> StepCircuit<G::Scalar> for CubeCircuit<G> {
    fn arity(&self) -> usize {
      1
    }

    fn circuit_index(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
      &self,
      cs: &mut CS,
      _pc: Option<&AllocatedNum<G::Scalar>>,
      z: &[AllocatedNum<G::Scalar>],
    ) -> Result<
      (
        Option<AllocatedNum<G::Scalar>>,
        Vec<AllocatedNum<G::Scalar>>,
      ),
      SynthesisError,
    > {
      let z_i = &z[0];

      let z_sq = z_i.square(cs.namespace(|| "z_i^2"))?;
      let z_cu = z_sq.mul(cs.namespace(|| "z_i^3"), z_i)?;

      let next_pc = AllocatedNum::alloc(cs.namespace(|| "next_pc"), || Ok(G::Scalar::from(0u64)))?;

      cs.enforce(
        || "next_pc = 0",
        |lc| lc + CS::one(),
        |lc| lc + next_pc.get_variable(),
        |lc| lc,
      );

      Ok((Some(next_pc), vec![z_cu]))
    }
  }

  #[derive(Clone)]
  enum TestCircuit<G: Group> {
    Square(SquareCircuit<G>),
    Cube(CubeCircuit<G>),
  }

  impl<G: Group> StepCircuit<G::Scalar> for TestCircuit<G> {
    fn arity(&self) -> usize {
      1
    }

    fn circuit_index(&self) -> usize {
      match self {
        TestCircuit::Square(c) => c.circuit_index(),
        TestCircuit::Cube(c) => c.circuit_index(),
      }
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
      &self,
      cs: &mut CS,
      pc: Option<&AllocatedNum<G::Scalar>>,
      z: &[AllocatedNum<G::Scalar>],
    ) -> Result<
      (
        Option<AllocatedNum<G::Scalar>>,
        Vec<AllocatedNum<G::Scalar>>,
      ),
      SynthesisError,
    > {
      match self {
        TestCircuit::Square(c) => c.synthesize(cs, pc, z),
        TestCircuit::Cube(c) => c.synthesize(cs, pc, z),
      }
    }
  }

  struct TestNIVC<G1, G2> {
    _p: PhantomData<(G1, G2)>,
  }

  impl<G1, G2> TestNIVC<G1, G2> {
    fn new() -> Self {
      TestNIVC { _p: PhantomData }
    }
  }

  impl<G1, G2> NonUniformCircuit<G1, G2, TestCircuit<G1>, TrivialSecondaryCircuit<G2::Scalar>>
    for TestNIVC<G1, G2>
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
  {
    fn initial_program_counter(&self) -> <G1 as Group>::Scalar {
      G1::Scalar::from(0u64)
    }

    fn num_circuits(&self) -> usize {
      2
    }

    fn primary_circuit(&self, circuit_index: usize) -> TestCircuit<G1> {
      match circuit_index {
        0 => TestCircuit::Square(SquareCircuit { _p: PhantomData }),
        1 => TestCircuit::Cube(CubeCircuit { _p: PhantomData }),
        _ => panic!("Invalid circuit index"),
      }
    }

    fn secondary_circuit(&self) -> TrivialSecondaryCircuit<G2::Scalar> {
      Default::default()
    }
  }

  fn test_nivc_trivial_with_compression_with<G1, G2, E1, E2>()
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
    E1: EvaluationEngineTrait<G1>,
    E2: EvaluationEngineTrait<G2>,
    <G1::Scalar as PrimeField>::Repr: Abomonation,
    <G2::Scalar as PrimeField>::Repr: Abomonation,
  {
    const NUM_STEPS: usize = 6;

    let test_nivc = TestNIVC::<G1, G2>::new();

    let pp = PublicParams::new(
      &test_nivc,
      &*default_commitment_key_hint(),
      &*default_commitment_key_hint(),
    );

    let initial_pc = test_nivc.initial_program_counter();
    let mut augmented_circuit_index = field_as_usize(initial_pc);

    let z0_primary = vec![G1::Scalar::from(17u64)];
    let z0_secondary = vec![<G2 as Group>::Scalar::ZERO];

    let mut recursive_snark = RecursiveSNARK::iter_base_step(
      &pp,
      augmented_circuit_index,
      &test_nivc.primary_circuit(augmented_circuit_index),
      &test_nivc.secondary_circuit(),
      Some(initial_pc),
      augmented_circuit_index,
      2,
      &z0_primary,
      &z0_secondary,
    )
    .unwrap();

    for _ in 0..NUM_STEPS {
      let prove_res = recursive_snark.prove_step(
        &pp,
        augmented_circuit_index,
        &test_nivc.primary_circuit(augmented_circuit_index),
        &test_nivc.secondary_circuit(),
      );

      let verify_res =
        recursive_snark.verify(&pp, augmented_circuit_index, &z0_primary, &z0_secondary);

      assert!(prove_res.is_ok());
      assert!(verify_res.is_ok());

      let program_counter = recursive_snark.get_program_counter();
      augmented_circuit_index = field_as_usize(program_counter);
    }

    let (prover_key, verifier_key) =
      CompressedSNARK::<_, _, _, _, S<G1, E1>, S<G2, E2>>::setup(&pp).unwrap();

    let compressed_prove_res = CompressedSNARK::prove(&pp, &prover_key, &recursive_snark);

    assert!(compressed_prove_res.is_ok());

    let compressed_snark = compressed_prove_res.unwrap();

    let compressed_verify_res =
      compressed_snark.verify(&pp, &verifier_key, z0_primary, z0_secondary);

    assert!(compressed_verify_res.is_ok());
  }

  #[test]
  fn test_nivc_trivial_with_compression() {
    test_nivc_trivial_with_compression_with::<pallas::Point, vesta::Point, EE<_>, EE<_>>();
    test_nivc_trivial_with_compression_with::<bn256::Point, grumpkin::Point, EE<_>, EE<_>>();
    test_nivc_trivial_with_compression_with::<secp256k1::Point, secq256k1::Point, EE<_>, EE<_>>();
  }

  fn test_compression_detects_circuit_num_with<G1, G2, E1, E2>()
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
    E1: EvaluationEngineTrait<G1>,
    E2: EvaluationEngineTrait<G2>,
    <G1::Scalar as PrimeField>::Repr: Abomonation,
    <G2::Scalar as PrimeField>::Repr: Abomonation,
  {
    const NUM_STEPS: usize = 6;

    let test_nivc = TestNIVC::<G1, G2>::new();

    let pp = PublicParams::new(
      &test_nivc,
      &*default_commitment_key_hint(),
      &*default_commitment_key_hint(),
    );

    let initial_pc = test_nivc.initial_program_counter();
    let mut augmented_circuit_index = field_as_usize(initial_pc);

    let z0_primary = vec![G1::Scalar::from(17u64)];
    let z0_secondary = vec![G2::Scalar::ZERO];

    let mut recursive_snark = RecursiveSNARK::iter_base_step(
      &pp,
      augmented_circuit_index,
      &test_nivc.primary_circuit(augmented_circuit_index),
      &test_nivc.secondary_circuit(),
      Some(initial_pc),
      augmented_circuit_index,
      2,
      &z0_primary,
      &z0_secondary,
    )
    .unwrap();

    for _ in 0..NUM_STEPS {
      let prove_res = recursive_snark.prove_step(
        &pp,
        augmented_circuit_index,
        &test_nivc.primary_circuit(augmented_circuit_index),
        &test_nivc.secondary_circuit(),
      );

      let verify_res =
        recursive_snark.verify(&pp, augmented_circuit_index, &z0_primary, &z0_secondary);

      assert!(prove_res.is_ok());
      assert!(verify_res.is_ok());

      let program_counter = recursive_snark.get_program_counter();
      augmented_circuit_index = field_as_usize(program_counter);
    }

    let (prover_key, verifier_key) =
      CompressedSNARK::<_, _, _, _, S<G1, E1>, S<G2, E2>>::setup(&pp).unwrap();

    let mut recursive_snark_truncated = recursive_snark.clone();

    recursive_snark_truncated.r_U_primary.pop();
    recursive_snark_truncated.r_W_primary.pop();

    let bad_proof = CompressedSNARK::prove(&pp, &prover_key, &recursive_snark_truncated);
    assert!(bad_proof.is_err());

    let compressed_snark = CompressedSNARK::prove(&pp, &prover_key, &recursive_snark).unwrap();

    let mut bad_compressed_snark = compressed_snark.clone();

    bad_compressed_snark.r_U_primary.pop();
    bad_compressed_snark.r_W_snark_primary.pop();

    let bad_verification =
      bad_compressed_snark.verify(&pp, &verifier_key, z0_primary, z0_secondary);
    assert!(bad_verification.is_err());
  }

  #[test]
  #[should_panic]
  fn test_compression_detects_circuit_num() {
    test_compression_detects_circuit_num_with::<pallas::Point, vesta::Point, EE<_>, EE<_>>();
    test_compression_detects_circuit_num_with::<bn256::Point, grumpkin::Point, EE<_>, EE<_>>();
    test_compression_detects_circuit_num_with::<secp256k1::Point, secq256k1::Point, EE<_>, EE<_>>();
  }
}
