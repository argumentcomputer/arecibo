//! In this module we define a compressing SNARK for Supernova proofs

use std::marker::PhantomData;

use crate::traits::{circuit_supernova::StepCircuit, snark::RelaxedR1CSSNARKTrait, Group};

use super::{error::SuperNovaError, PublicParams, RecursiveSNARK};

/// The prover key for the Supernova CompressedSNARK
pub struct ProverKey<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  pks_primary: Vec<S1::ProverKey>,
  pk_secondary: S2::ProverKey,
  _p: PhantomData<(C1, C2)>,
}

/// The verifier key for the Supernova CompressedSNARK
pub struct VerifierKey<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  vks_primary: Vec<S1::VerifierKey>,
  vk_secondary: S2::VerifierKey,
  _p: PhantomData<(C1, C2)>,
}

/// The SNARK that proves the knowledge of a valid Supernova `RecursiveSNARK`
pub struct CompressedSNARK<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  primary_proofs: Vec<S1>,
  secondary_proof: S2,
  _p: PhantomData<(C1, C2)>,
}

impl<G1, G2, C1, C2, S1, S2> CompressedSNARK<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  /// Generate the prover and verifier keys for the `CompressedSNARK` prover and verifier
  pub fn setup(
    pp: &PublicParams<G1, G2, C1, C2>,
  ) -> Result<
    (
      ProverKey<G1, G2, C1, C2, S1, S2>,
      VerifierKey<G1, G2, C1, C2, S1, S2>,
    ),
    SuperNovaError,
  > {
    let (pks_primary, vks_primary) = pp
      .circuit_shapes
      .iter()
      .map(|c| S1::setup(&pp.ck_primary, &c.r1cs_shape))
      .collect::<Result<Vec<_>, _>>()?
      .into_iter()
      .unzip();

    let (pk_secondary, vk_secondary) =
      S2::setup(&pp.ck_secondary, &pp.circuit_shape_secondary.r1cs_shape)?;

    let prover_key = ProverKey {
      pks_primary,
      pk_secondary,
      _p: PhantomData,
    };
    let verifier_key = VerifierKey {
      vks_primary,
      vk_secondary,
      _p: PhantomData,
    };

    Ok((prover_key, verifier_key))
  }

  /// create a new `CompressedSNARK` proof
  pub fn prove(
    pp: &PublicParams<G1, G2, C1, C2>,
    pk: &ProverKey<G1, G2, C1, C2, S1, S2>,
    recursive_snark: &RecursiveSNARK<G1, G2>,
  ) -> Result<Self, SuperNovaError> {
    // TODO: Check if there's any pre-processing that needs to be done

    let primary_proofs = pk
      .pks_primary
      .iter()
      .zip(recursive_snark.r_W_primary.clone())
      .zip(recursive_snark.r_U_primary.clone())
      .map(|((pk, r_W), r_U)| {
        let r_W = r_W.unwrap_or_else(|| panic!("Wrong number of circuits"));
        let r_U = r_U.unwrap_or_else(|| panic!("Wrong number of circuits"));
        S1::prove(&pp.ck_primary, pk, &r_U, &r_W)
      })
      .collect::<Result<Vec<S1>, _>>()?;

    let secondary_proof = S2::prove(
      &pp.ck_secondary,
      &pk.pk_secondary,
      &recursive_snark.r_U_secondary[0].clone().unwrap(),
      &recursive_snark.r_W_secondary[0].clone().unwrap(),
    )?;

    let compressed_snark = CompressedSNARK {
      primary_proofs,
      secondary_proof,
      _p: PhantomData,
    };

    Ok(compressed_snark)
  }

  /// verify a `CompressedSNARK` proof
  pub fn verify(&self, vk: &VerifierKey<G1, G2, C1, C2, S1, S2>) -> () {
    todo!()
  }
}

#[cfg(test)]
mod test {

  use super::*;
  use crate::provider::bn256_grumpkin::{bn256, grumpkin};
  use crate::provider::secp_secq::{secp256k1, secq256k1};
  use pasta_curves::{pallas, vesta};

  fn test_nivc_nontrivial_with_compression_with<G1, G2>()
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
  {
    assert!(true)
  }

  #[test]
  fn test_nivc_nontrivial_with_compression() {
    test_nivc_nontrivial_with_compression_with::<pallas::Point, vesta::Point>();
    test_nivc_nontrivial_with_compression_with::<bn256::Point, grumpkin::Point>();
    test_nivc_nontrivial_with_compression_with::<secp256k1::Point, secq256k1::Point>();
  }
}
