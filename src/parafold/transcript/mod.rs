use generic_array::typenum::U24;
use neptune::hash_type::HashType;
use neptune::poseidon::PoseidonConstants;
use neptune::Strength;

use crate::traits::Engine;

pub mod circuit;
pub mod prover;

/// Poseidon constants for hashing used for the Fiat-Shamir transcript
pub type TranscriptConstants<E> = PoseidonConstants<<E as Engine>::Scalar, U24>;

pub fn new_transcript_constants<E: Engine>() -> TranscriptConstants<E> {
  TranscriptConstants::<E>::new_with_strength_and_type(Strength::Standard, HashType::Sponge)
}

#[cfg(test)]
mod tests {
  use bellpepper_core::ConstraintSystem;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use ff::Field;

  use crate::Commitment;
  use crate::gadgets::utils::alloc_zero;
  use crate::parafold::hash::HashElement;
  use crate::parafold::transcript::circuit::AllocatedTranscript;
  use crate::parafold::transcript::new_transcript_constants;
  use crate::parafold::transcript::prover::Transcript;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::{CurveCycleEquipped, Engine};
  use crate::traits::commitment::CommitmentEngineTrait;

  type ESecondary = <E as CurveCycleEquipped>::Secondary;
  type Scalar = <E as Engine>::Scalar;
  type Base = <E as Engine>::Base;

  type CE = <E as Engine>::CE;

  type CS = TestConstraintSystem<Scalar>;
  type HE = HashElement<E>;
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
      HE::Scalar(Scalar::zero()),
      HE::Scalar(Scalar::one()),
      HE::Scalar(Scalar::zero() - Scalar::one()),
      HE::CommitmentPrimary(CommP::default()),
      HE::CommitmentPrimary(idP),
      HE::CommitmentPrimary(neg_idP),
      HE::CommitmentSecondary(CommS::default()),
      HE::CommitmentSecondary(idS),
      HE::CommitmentSecondary(neg_idS),
    ];

    let constants = new_transcript_constants::<E>();

    let mut txP = Transcript::new(constants.clone(), [Scalar::ZERO]);
    for e in &elements {
      txP.absorb(e.clone());
    }

    let (state, buffer) = txP.seal();
    assert_eq!(elements.to_vec(), buffer);

    let zero_alloc = alloc_zero(cs.namespace(|| "alloc zero"));
    let mut txV = AllocatedTranscript::<E>::new(constants, [zero_alloc], Some(buffer));

    // Check that each element is properly deserialized in the circuit
    for (i, e) in elements.iter().enumerate() {
      match e {
        HashElement::Scalar(_) => {
          let _ = txV
            .read_scalar(cs.namespace(|| format!("read scalar {i}")))
            .unwrap();
        }
        HashElement::Base(_) => {
          unreachable!("read base not used and not implemented")
        }
        HashElement::CommitmentPrimary(_) => {
          let _ = txV
            .read_commitment_primary(cs.namespace(|| format!("read commP {i}")))
            .unwrap();
        }
        HashElement::CommitmentSecondary(_) => {
          let _ = txV
            .read_commitment_secondary(cs.namespace(|| format!("read commS {i}")))
            .unwrap();
        }
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
