use digest::{typenum::Unsigned, OutputSizeUser};
use ff::PrimeField;
use serde::Serialize;
use sha3::{Digest, Sha3_256};
use std::io;
use std::marker::PhantomData;

use crate::constants::NUM_HASH_BITS;

/// For building digests
#[derive(Clone)]
pub struct DigestBuilder<F: PrimeField, T: HasDigest<F>> {
  inner: T,
  _phantom: PhantomData<(F, T)>,
}

/// Trait to be implemented by types whose digests can be built with `DigestBuilder`.
pub trait HasDigest<F: PrimeField> {
  /// Extend `bytes` with raw bytes or digest summarizing `Digestible`.
  fn set_digest(&mut self, digest: F);
}

/// Trait for components with potentially discrete digests to be included in their container's digest.
pub trait Digestible {
  /// Write the byte representation of Self in a byte buffer
  fn write_bytes<W: Sized + io::Write>(&self, byte_sink: &mut W) -> Result<(), io::Error>;
}

/// Marker trait to be implemented for types that implement `Digestible` and `Serialize`.
/// Their instances will be serialized to bytes then digested.
pub trait SimpleDigestible: Serialize {}

impl<T: SimpleDigestible> Digestible for T {
  fn write_bytes<W: Sized + io::Write>(&self, byte_sink: &mut W) -> Result<(), io::Error> {
    bincode::serialize_into(byte_sink, self)
      .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
  }
}

impl<F: PrimeField, T: HasDigest<F> + Digestible> DigestBuilder<F, T> {
  /// Return a new `DigestBuilder` for a value
  pub fn new(value: T) -> Self {
    assert!(
      NUM_HASH_BITS <= <Sha3_256 as OutputSizeUser>::OutputSize::to_usize() * 8,
      "DigestBuilder only supports hashes with output over {NUM_HASH_BITS} bits"
    );
    Self {
      inner: value,
      _phantom: Default::default(),
    }
  }

  fn hasher() -> Sha3_256 {
    Sha3_256::new()
  }

  fn map_to_field(digest: &mut [u8]) -> F {
    let bv = (0..NUM_HASH_BITS).map(|i| {
      let (byte_pos, bit_pos) = (i / 8, i % 8);
      let bit = (digest[byte_pos] >> bit_pos) & 1;
      bit == 1
    });

    // turn the bit vector into a scalar
    let mut digest = F::ZERO;
    let mut coeff = F::ONE;
    for bit in bv {
      if bit {
        digest += coeff;
      }
      coeff += coeff;
    }
    digest
  }

  /// Build and return inner `Digestible`.
  pub fn build(mut self) -> Result<T, io::Error> {
    let mut hasher = Self::hasher();
    self.inner.write_bytes(&mut hasher)?;
    let mut bytes: [u8; 32] = hasher.finalize().into();
    self.inner.set_digest(Self::map_to_field(&mut bytes));

    Ok(self.inner)
  }
}
