use bellpepper_core::num::{AllocatedNum, Num};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use neptune::circuit2::{poseidon_hash_allocated, Elt};
use neptune::hash_type::HashType;
use neptune::poseidon::PoseidonConstants;
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::circuit::SpongeCircuit;
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Poseidon};

use crate::parafold::cycle_fold::hash_commitment;
use crate::parafold::gadgets::emulated::BaseParams;
use crate::traits::commitment::CommitmentTrait;
use crate::traits::CurveCycleEquipped;
use crate::Commitment;

#[derive(Clone, Debug, PartialEq)]
pub enum HashElement<E: CurveCycleEquipped> {
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

pub trait HashWriter<E: CurveCycleEquipped> {
  fn write<H: Hasher<E>>(&self, hasher: &mut H);

  fn hash<A>(&self, constants: &PoseidonConstants<E::Scalar, A>) -> E::Scalar
  where
    A: Arity<E::Scalar>,
  {
    let len = A::to_usize();
    let mut buffer = Vec::<E::Scalar>::with_capacity(len);
    self.write(&mut buffer);
    <Vec<E::Scalar> as Hasher<E>>::hash(&buffer, constants)
  }
}

pub trait Hasher<E: CurveCycleEquipped> {
  fn absorb(&mut self, element: HashElement<E>);

  fn absorb_scalar(&mut self, element: E::Scalar) {
    self.absorb(HashElement::Scalar(element))
  }
  fn absorb_base(&mut self, element: E::Base) {
    self.absorb(HashElement::Base(element))
  }
  fn absorb_commitment_primary(&mut self, element: Commitment<E>) {
    self.absorb(HashElement::CommitmentPrimary(element))
  }
  fn absorb_commitment_secondary(&mut self, element: Commitment<E::Secondary>) {
    self.absorb(HashElement::CommitmentSecondary(element))
  }

  fn hash<A: Arity<E::Scalar>>(&self, constants: &PoseidonConstants<E::Scalar, A>) -> E::Scalar;
}

impl<E: CurveCycleEquipped> Hasher<E> for Vec<E::Scalar> {
  fn absorb(&mut self, element: HashElement<E>) {
    match &element {
      HashElement::Scalar(scalar) => self.push(*scalar),
      HashElement::Base(base) => self.extend(BaseParams::<E>::base_to_limbs(base)),
      HashElement::CommitmentPrimary(c) => {
        let hash = hash_commitment::<E>(c);
        self.absorb(HashElement::<E>::Base(hash));
      }
      HashElement::CommitmentSecondary(c) => {
        let (x, y, _) = c.to_coordinates();
        self.extend([x, y])
      }
    }
  }

  fn hash<A: Arity<E::Scalar>>(&self, constants: &PoseidonConstants<E::Scalar, A>) -> E::Scalar {
    match constants.hash_type {
      HashType::ConstantLength(len) => {
        assert_eq!(self.len(), len);
        Poseidon::new_with_preimage(self, constants).hash()
      }
      HashType::Sponge => {
        let num_absorbs = self.len() as u32;
        let acc = &mut ();
        let mut sponge = Sponge::new_with_constants(constants, Simplex);
        let parameter = IOPattern(vec![SpongeOp::Absorb(num_absorbs), SpongeOp::Squeeze(1u32)]);
        sponge.start(parameter, None, acc);
        SpongeAPI::absorb(&mut sponge, num_absorbs, self, acc);
        let hash = SpongeAPI::squeeze(&mut sponge, 1, acc);
        SpongeAPI::finish(&mut sponge, acc).expect("no error");
        hash[0]
      }
      _ => {
        panic!("unsupported")
      }
    }
  }
}

//-------------------------

pub trait AllocatedHashWriter<F: PrimeField> {
  fn write<H: AllocatedHasher<F>>(&self, hasher: &mut H);

  fn hash<CS, A>(
    &self,
    cs: CS,
    constants: &PoseidonConstants<F, A>,
  ) -> Result<AllocatedNum<F>, SynthesisError>
  where
    CS: ConstraintSystem<F>,
    A: Arity<F>,
  {
    let mut buffer = Vec::<Elt<F>>::new();
    self.write(&mut buffer);
    <Vec<Elt<F>> as AllocatedHasher<F>>::hash(&buffer, cs, constants)
  }
}

impl<F: PrimeField> AllocatedHashWriter<F> for AllocatedNum<F> {
  fn write<H: AllocatedHasher<F>>(&self, hasher: &mut H) {
    hasher.absorb(Elt::Allocated(self.clone()))
  }
}

impl<F: PrimeField> AllocatedHashWriter<F> for Num<F> {
  fn write<H: AllocatedHasher<F>>(&self, hasher: &mut H) {
    hasher.absorb(Elt::Num(self.clone()))
  }
}
impl<F: PrimeField, T: AllocatedHashWriter<F>> AllocatedHashWriter<F> for Vec<T> {
  fn write<H: AllocatedHasher<F>>(&self, hasher: &mut H) {
    for element in self {
      element.write(hasher);
    }
  }
}

pub trait AllocatedHasher<F: PrimeField> {
  fn absorb(&mut self, element: Elt<F>);

  fn hash<A: Arity<F>, CS: ConstraintSystem<F>>(
    &self,
    cs: CS,
    constants: &PoseidonConstants<F, A>,
  ) -> Result<AllocatedNum<F>, SynthesisError>;
}

impl<F: PrimeField> AllocatedHasher<F> for Vec<Elt<F>> {
  fn absorb(&mut self, element: Elt<F>) {
    self.push(element);
  }
  fn hash<A: Arity<F>, CS: ConstraintSystem<F>>(
    &self,
    mut cs: CS,
    constants: &PoseidonConstants<F, A>,
  ) -> Result<AllocatedNum<F>, SynthesisError> {
    match constants.hash_type {
      HashType::ConstantLength(len) => {
        let mut buffer = Vec::with_capacity(len);
        for (i, element) in self.iter().enumerate() {
          let element =
            element.ensure_allocated(&mut cs.namespace(|| format!("ensure alloc {i}")), true)?;
          buffer.push(element)
        }
        assert_eq!(buffer.len(), len);

        poseidon_hash_allocated(cs.namespace(|| "hash"), buffer, constants)
      }
      HashType::Sponge => {
        let num_absorbs = self.len() as u32;

        let pattern = IOPattern(vec![SpongeOp::Absorb(num_absorbs), SpongeOp::Squeeze(1u32)]);
        let acc = &mut cs.namespace(|| "squeeze");
        let mut sponge = SpongeCircuit::new_with_constants(constants, Simplex);
        sponge.start(pattern, None, acc);
        SpongeAPI::absorb(&mut sponge, num_absorbs, self, acc);
        let state_out = SpongeAPI::squeeze(&mut sponge, 1, acc);
        SpongeAPI::finish(&mut sponge, acc).expect("no error");

        state_out[0].ensure_allocated(acc, true)
      }
      _ => {
        panic!("unsupported")
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use bellpepper_core::num::AllocatedNum;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use bellpepper_core::ConstraintSystem;

  use crate::parafold::gadgets::emulated::AllocatedBase;
  use crate::parafold::gadgets::primary_commitment::AllocatedPrimaryCommitment;
  use crate::parafold::gadgets::secondary_commitment::AllocatedSecondaryCommitment;
  use crate::provider::Bn256EngineKZG as E;
  use crate::traits::commitment::CommitmentEngineTrait;
  use crate::traits::Engine;

  use super::*;

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
      HE::Base(Base::zero()),
      HE::Base(Base::one()),
      HE::Base(Base::zero() - Base::one()),
      HE::CommitmentPrimary(CommP::default()),
      HE::CommitmentPrimary(idP),
      HE::CommitmentPrimary(neg_idP),
      HE::CommitmentSecondary(CommS::default()),
      HE::CommitmentSecondary(idS),
      HE::CommitmentSecondary(neg_idS),
    ];

    for (i, e) in elements.into_iter().enumerate() {
      let cs = &mut cs.namespace(|| i.to_string());
      match e {
        HashElement::Scalar(e) => {
          let e_alloc = AllocatedNum::alloc_infallible(cs, || e);
          assert_eq!(e, e_alloc.get_value().unwrap());
        }
        HashElement::Base(e) => {
          let e_alloc = AllocatedBase::<E>::alloc(cs.namespace(|| "alloc"), &e);
          assert_eq!(e, e_alloc.get_value());
          let e_alloc = AllocatedBase::<E>::alloc_unchecked(cs.namespace(|| "alloc unchecked"), e);
          assert_eq!(e, e_alloc.get_value());
        }
        HashElement::CommitmentPrimary(e) => {
          let e_alloc = AllocatedPrimaryCommitment::<E>::alloc(cs, e);
          assert_eq!(e, e_alloc.get_value());
        }
        HashElement::CommitmentSecondary(e) => {
          let e_alloc = AllocatedSecondaryCommitment::<E>::alloc(cs.namespace(|| "alloc"), e);
          assert_eq!(e, e_alloc.get_value().unwrap());
          let e_alloc = AllocatedSecondaryCommitment::<E>::alloc_unchecked(
            cs.namespace(|| "alloc unchecked"),
            e,
          );
          assert_eq!(e, e_alloc.get_value().unwrap());
        }
      }
    }

    if !cs.is_satisfied() {
      println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
  }
}
