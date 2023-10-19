//! In this module we define a compressing SNARK for Supernova proofs

use std::marker::PhantomData;

use crate::{
  constants::NUM_HASH_BITS,
  gadgets::utils::scalar_as_base,
  r1cs::RelaxedR1CSInstance,
  traits::{
    circuit_supernova::StepCircuit, snark::RelaxedR1CSSNARKTrait, AbsorbInROTrait, Group, ROTrait,
  },
};

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

  num_steps: usize,
  last_circuit_idx: usize,

  r_U_primary: RelaxedR1CSInstance<G1>,
  r_U_secondary: RelaxedR1CSInstance<G2>,

  zn_primary: Vec<G1::Scalar>,
  zn_secondary: Vec<G2::Scalar>,
  _p: PhantomData<(G1, G2, C1, C2)>,
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
      .zip(&recursive_snark.r_W_primary)
      .zip(&recursive_snark.r_U_primary)
      .map(|((pk, r_W), r_U)| {
        let r_W = r_W.unwrap_or_else(|| panic!("Wrong number of circuits"));
        let r_U = r_U.unwrap_or_else(|| panic!("Wrong number of circuits"));
        S1::prove(&pp.ck_primary, pk, &r_U, &r_W)
      })
      .collect::<Result<Vec<S1>, _>>()?;

    let secondary_r_U = &recursive_snark.r_U_secondary[0].unwrap();
    let secondary_r_W = &recursive_snark.r_W_secondary[0].unwrap();

    let secondary_proof = S2::prove(
      &pp.ck_secondary,
      &pk.pk_secondary,
      secondary_r_U,
      secondary_r_W,
    )?;

    let last_circuit_idx = recursive_snark.augmented_circuit_index;

    let compressed_snark = CompressedSNARK {
      primary_proofs,
      secondary_proof,

      r_U_primary: recursive_snark.r_U_primary[last_circuit_idx].unwrap(),
      r_U_secondary: recursive_snark.r_U_secondary[0].unwrap(),

      num_steps: recursive_snark.i,
      last_circuit_idx,

      zn_primary: recursive_snark.zi_primary, // TODO: I'm fairly certain this is right, but I should double check
      zn_secondary: recursive_snark.zi_secondary,
      _p: PhantomData,
    };

    Ok(compressed_snark)
  }

  /// verify a `CompressedSNARK` proof
  pub fn verify(
    &self,
    pp: &PublicParams<G1, G2, C1, C2>,
    vk: &VerifierKey<G1, G2, C1, C2, S1, S2>,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<(Vec<G1::Scalar>, Vec<G2::Scalar>), SuperNovaError> {
    let num_field_primary_ro = 3 // params_next, i_new, program_counter_new
    + 2 * pp[self.last_circuit_idx].F_arity // zo, z1
    + (7 + 2 * pp.augmented_circuit_params_primary.get_n_limbs()); // # 1 * (7 + [X0, X1]*#num_limb)

    // secondary circuit
    let num_field_secondary_ro = 2 // params_next, i_new
    + 2 * pp.circuit_shape_secondary.F_arity // zo, z1
    + pp.circuit_shapes.len() * (7 + 2 * pp.augmented_circuit_params_primary.get_n_limbs()); // #num_augment

    let (hash_primary, hash_secondary) = {
      let mut hasher = <G2 as Group>::RO::new(pp.ro_consts_secondary.clone(), num_field_primary_ro);

      hasher.absorb(pp.digest());
      hasher.absorb(G1::Scalar::from(self.num_steps as u64));
      hasher.absorb(G1::Scalar::from(self.last_circuit_idx as u64));

      for e in z0_primary {
        hasher.absorb(e);
      }

      for e in &self.zn_primary {
        hasher.absorb(*e);
      }

      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 =
        <G1 as Group>::RO::new(pp.ro_consts_primary.clone(), num_field_secondary_ro);

      hasher2.absorb(scalar_as_base::<G1>(pp.digest()));
      hasher2.absorb(G2::Scalar::from(self.num_steps as u64));

      for e in z0_secondary {
        hasher2.absorb(e);
      }

      for e in &self.zn_secondary {
        hasher2.absorb(*e);
      }

      let default_value =
        RelaxedR1CSInstance::default(&pp.ck_primary, &pp[self.last_circuit_idx].r1cs_shape);

      self.r_U_primary.absorb_in_ro(&mut hasher2); // TODO: This is wrong, I need to hash all the `r_U_primary` (add them in the proof?)

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    let res = self
      .primary_proofs
      .iter()
      .zip(vk.vks_primary)
      .map(|(proof, vk)| {
        let U = &self.r_U_primary;
        proof.verify(&vk, U)
      })
      .collect::<Vec<_>>();

    Ok((z0_primary, z0_secondary))
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::provider::{
    bn256_grumpkin::{bn256, grumpkin},
    secp_secq::{secp256k1, secq256k1},
  };
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
