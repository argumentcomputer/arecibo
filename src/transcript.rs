use ff::PrimeField;
use smallvec::{Array, SmallVec};
use std::{io, marker::PhantomData};

/// This encodes the translation between field elements through limbing:
/// `Self` can be represented as an array of limbs, where each limb is a `F`.
// The API uses SmallVec to cheapen the allocation w.r.t a full Vec.
pub trait Limbable<F: PrimeField> {
  type A: Array<Item = F>;

  fn limb(self) -> SmallVec<Self::A>;
}

/// There is a blanket reflexive implementation for `Limbable<F, 1>`
impl<F: PrimeField> Limbable<F> for F {
  type A = [F; 1];

  fn limb(self) -> SmallVec<Self::A> {
    SmallVec::from_elem(self, 1)
  }
}

/// This is a simple proxy of std::io::Write that exposes writing field elements, rather than bytes.
// The claim is there should be one and only one `FieldWriter<F>` for each algebraic transcript, using its
// native field.
pub trait FieldWriter {
  type NativeField: PrimeField;
  fn write(&mut self, field_elts: &[Self::NativeField]) -> Result<(), io::Error>;
  fn flush(&mut self) -> Result<(), io::Error>;
}

/// This expresses that `Self` is writable as a sequence of field elements given a `FieldWriter` with a compatible (equal) native field type.
pub trait FieldWritable {
  /// The natural field type for this `FieldWritable`.
  /// The associated type forces Self to pick a *single* `<Self as FieldWritable>::NativeField`,
  type NativeField: PrimeField;

  /// Write the representation of `Self` as `NativeField` elements to a compatible sink
  fn write_natively<W: Sized + FieldWriter<NativeField = Self::NativeField>>(
    &self,
    field_sink: &mut W,
  ) -> Result<(), io::Error>;
}

// We can create a translating FieldWriter using this generic struct
pub struct FieldEncodingWriter<'a, F: PrimeField, W: FieldWriter> {
  writer: &'a mut W,
  _phantom: PhantomData<F>,
}

// It's a valid FieldWriter, for the field F instead of W's native field
impl<'a, F, W> FieldWriter for FieldEncodingWriter<'a, F, W>
where
  // F is a field limbable in the native field of W
  F: PrimeField + Limbable<<W as FieldWriter>::NativeField>,
  W: FieldWriter,
{
  type NativeField = F;

  fn write(&mut self, field_elts: &[F]) -> Result<(), io::Error> {
    for origin_elt in field_elts.iter() {
      self.writer.write(&origin_elt.limb())?;
    }
    Ok(())
  }

  fn flush(&mut self) -> Result<(), io::Error> {
    self.writer.flush()
  }
}

/// This is the functionality we want: we can write `Self` as a sequence of field elements, even if the chosen target type does
/// not match the native field type of `Self`. We don't want to let folks chose how to implement this, so we'll make this an extension trait.
pub trait FieldWritableExt: FieldWritable {
  /// this indicates how to write `Self` as a sequence of `TargetField` field elements,
  /// as long as the NativeField of `Self`'s `FieldWritable` is Limbable into `TargetField`.
  fn write<W>(&self, field_sink: &mut W) -> Result<(), io::Error>
  where
    W: FieldWriter,
    <Self as FieldWritable>::NativeField: Limbable<<W as FieldWriter>::NativeField>,
  {
    self.write_natively(&mut FieldEncodingWriter {
      writer: field_sink,
      _phantom: PhantomData,
    })
  }
}

/// This is a blanket implementation: the only requirements are having a `FieldWritable` for the
/// native field of `Self`, and that this native field is Limbable into `TargetField`.
impl<T: FieldWritable> FieldWritableExt for T {}

#[cfg(test)]
mod tests {

  use ff::PrimeField;
  use num_bigint::BigUint;
  use num_traits::Num;

  pub use halo2curves::bn256::{Fq as Base, Fr as Scalar};

  use super::{FieldWritable, FieldWritableExt, FieldWriter, Limbable};
  use crate::{
    provider::{Bn256EngineKZG, GrumpkinEngine},
    traits::{commitment::CommitmentTrait, Dual},
    Commitment,
  };

  #[test]
  fn sanity_check() {
    let bmod = BigUint::from_str_radix(&Base::MODULUS[2..], 16).unwrap();
    let smod = BigUint::from_str_radix(&Scalar::MODULUS[2..], 16).unwrap();

    assert!(smod < bmod);
  }

  // *** For demo purposes only ***
  // TODO: move out of this test module, since any competing implementaiton in the main code will make
  // compilation under test fail for duplicate implementations of the same trait
  impl Limbable<Scalar> for Base {
    type A = [Scalar; 2];

    fn limb(self) -> smallvec::SmallVec<Self::A> {
      let mut bytes = self.to_repr();
      let (bytes_low, bytes_high) = bytes.split_at_mut(16);
      let arr_low: [u8; 16] = bytes_low.try_into().unwrap();
      let arr_high: [u8; 16] = bytes_high.try_into().unwrap();
      let f1 = Scalar::from_u128(u128::from_le_bytes(arr_low));
      let f2 = Scalar::from_u128(u128::from_le_bytes(arr_high));
      smallvec::smallvec![f1, f2]
    }
  }

  // We don't need to define Limbable<Base> for Base, since it's part of the blanket implementation

  // Commitments from an Engine are natively writeable as E::Base elements
  // but if we attempt to write a generic `impl<E: Engine> FieldWritable for Commitment<E>``
  // (with NativeField = E::Base), the compiler will complain that the type parameter `E` is not constrained.
  //
  // This is because the commitment type Commitment<E> could be involved in another engine (and in fact is, if
  // you consider e.g. Bn256EngineZM vs. Bn256EngineKZG, which share the same <E as Engine>::CE). Two instances
  // would apply for the same concrete type:
  // - impl FieldWritable for Commitment<Bn256EngineZM>
  // - impl FieldWritable for Commitment<Bn256EngineKZG>
  //
  // But we can still define the monomorphized instances!
  impl FieldWritable for Commitment<Bn256EngineKZG> {
    type NativeField = Base;

    // *** For demo purposes only ***
    fn write_natively<W: Sized + FieldWriter<NativeField = Base>>(
      &self,
      field_sink: &mut W,
    ) -> Result<(), std::io::Error> {
      let (x, y, _) = self.to_coordinates();
      field_sink.write(&[x, y])
    }
  }
  impl FieldWritable for Commitment<GrumpkinEngine> {
    type NativeField = Scalar;

    // *** For demo purposes only ***
    fn write_natively<W: Sized + FieldWriter<NativeField = Scalar>>(
      &self,
      field_sink: &mut W,
    ) -> Result<(), std::io::Error> {
      let (x, y, _) = self.to_coordinates();
      field_sink.write(&[x, y])
    }
  }

  // Let's build a trivial MockWriter
  struct MockWriter {
    written: Vec<Scalar>,
  }

  impl FieldWriter for MockWriter {
    type NativeField = Scalar;

    fn write(&mut self, field_elts: &[Self::NativeField]) -> Result<(), std::io::Error> {
      self.written.extend(field_elts.iter().cloned());
      Ok(())
    }

    fn flush(&mut self) -> Result<(), std::io::Error> {
      Ok(())
    }
  }

  #[test]
  fn it_works() {
    let commitment_native_base = Commitment::<Bn256EngineKZG>::default(); // identity element with coordinates in bn256::Base,
    let commitment_dual_base = Commitment::<Dual<Bn256EngineKZG>>::default(); // identity element with coordinates in GrumpkinEngine::Base,
    let mut writer = MockWriter {
      written: Vec::new(),
    }; // note: this works natively only on bn256::Scalar

    commitment_native_base.write(&mut writer).unwrap(); // the instance above fires, this writes 2 x 2 = 4 elements
    commitment_dual_base.write(&mut writer).unwrap(); // the blanket reflexive instance of Limbable fires, this writes 2 elements
    assert_eq!(writer.written.len(), 6);
  }
}
