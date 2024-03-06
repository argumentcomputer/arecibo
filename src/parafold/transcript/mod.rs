use generic_array::typenum::U24;
use neptune::poseidon::PoseidonConstants;

use crate::Commitment;
use crate::parafold::cycle_fold::gadgets::emulated::BaseParams;
use crate::parafold::cycle_fold::hash_commitment;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::CurveCycleEquipped;

pub mod circuit;
pub mod prover;

/// Poseidon constants for hashing used for the Fiat-Shamir transcript
pub type TranscriptConstants<F> = PoseidonConstants<F, U24>;

#[derive(Clone, Debug, PartialEq)]
pub enum TranscriptElement<E: CurveCycleEquipped> {
  /// Serialized as self
  Scalar(E::Scalar),
  /// Serialized as `[Scalar(limb_0), Scalar(limb_1), ...]`,
  /// where the limbs are given by the [BaseParams] definition.
  Base(E::Base),
  /// Serialized as `Base(hash)`, where `hash = Poseidon<E::Base, U2>(self.x, self.y)`
  CommitmentPrimary(Commitment<E>),
  /// Serialized as `[Scalar(self.x), Scalar(self.y)]`
  CommitmentSecondary(Commitment<E::Secondary>),
}

impl<E: CurveCycleEquipped> TranscriptElement<E> {
  pub fn to_field(&self) -> impl IntoIterator<Item = E::Scalar> {
    // TODO: figure out if we can avoid Vec
    match self {
      Self::Scalar(scalar) => vec![*scalar],
      Self::Base(base) => BaseParams::<E>::base_to_limbs(base),
      Self::CommitmentPrimary(c) => {
        let hash = hash_commitment::<E>(c);
        Self::Base(hash).to_field()
      }
      Self::CommitmentSecondary(c) => {
        let (x, y, _) = c.to_coordinates();
        [x, y].to_vec()
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use std::iter::zip;

  use bellpepper_core::ConstraintSystem;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use neptune::hash_type::HashType;
  use neptune::Strength;

  use crate::parafold::transcript::circuit::AllocatedTranscript;
  use crate::parafold::transcript::prover::Transcript;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::commitment::CommitmentEngineTrait;
  use crate::traits::Engine;

  use super::*;

  type ESecondary = <E as CurveCycleEquipped>::Secondary;
  type Scalar = <E as Engine>::Scalar;
  type Base = <E as Engine>::Base;

  type CE = <E as Engine>::CE;

  type CS = TestConstraintSystem<Scalar>;
  type TE = TranscriptElement<E>;
  type CommP = Commitment<E>;
  type CommS = Commitment<ESecondary>;

  #[test]
  fn test_hash() {
    let mut cs = CS::new();

    // TODO: Ugh
    let ckP = <CE as CommitmentEngineTrait<E>>::setup(b"1", 1);
    let idP = CE::commit(&ckP, &[Scalar::one()]);
    let neg_idP = <E as Engine>::CE::commit(&ckP, &[-Scalar::one()]);
    let ckS = <ESecondary as Engine>::CE::setup(b"1", 1);
    let idS = <ESecondary as Engine>::CE::commit(&ckS, &[Base::one()]);
    let neg_idS = <ESecondary as Engine>::CE::commit(&ckS, &[-Base::one()]);

    let elements = [
      TE::Scalar(Scalar::zero()),
      TE::Scalar(Scalar::one()),
      TE::Scalar(Scalar::zero() - Scalar::one()),
      // We currently don't support the verifier reading any Base elements, but
      // this is implicitly tested through PrimaryCommitment
      // TE::Base(Base::zero()),
      // TE::Base(Base::one()),
      // TE::Base(Base::zero() - Base::one()),
      TE::CommitmentPrimary(CommP::default()),
      TE::CommitmentPrimary(idP),
      TE::CommitmentPrimary(neg_idP),
      TE::CommitmentSecondary(CommS::default()),
      TE::CommitmentSecondary(idS),
      TE::CommitmentSecondary(neg_idS),
    ];

    let constants = TranscriptConstants::<Scalar>::new_with_strength_and_type(
      Strength::Standard,
      HashType::Sponge,
    );

    let mut txP = Transcript::new(constants.clone(), []);
    for e in &elements {
      txP.absorb(e.clone());
    }

    let (state, buffer) = txP.seal();
    assert_eq!(elements.to_vec(), buffer);

    let mut txV = AllocatedTranscript::<E>::new(constants, [], buffer);

    // Check that each element is properly deserialized in the circuit
    for (i, e) in elements.iter().enumerate() {
      match e {
        TranscriptElement::Scalar(e_expected) => {
          let e = txV
            .read_scalar(cs.namespace(|| format!("read scalar {i}")))
            .unwrap();
          assert_eq!(*e_expected, e.get_value().unwrap());
        }
        TranscriptElement::Base(_e_expected) => {
          panic!("read base not used and not implemented")
        }
        TranscriptElement::CommitmentPrimary(e_expected) => {
          let e = txV
            .read_commitment_primary(cs.namespace(|| format!("read commP {i}")))
            .unwrap();
          assert!(e.eq_native(e_expected));
        }
        TranscriptElement::CommitmentSecondary(e_expected) => {
          let e = txV
            .read_commitment_secondary(cs.namespace(|| format!("read commS {i}")))
            .unwrap();
          assert!(e.eq_native(e_expected).unwrap())
        }
      }
    }

    // check that the internal state contains all serialized elements
    let mut internal_state = txV.state().into_iter();
    for e in elements {
      for (f_expected, f) in zip(e.to_field(), &mut internal_state) {
        assert_eq!(f_expected, f.val().unwrap());
      }
    }

    // Check that both transcripts produce the same hash
    let state_alloc = txV.seal(cs.namespace(|| "seal")).unwrap();
    assert_eq!(state, state_alloc.get_value().unwrap());

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
