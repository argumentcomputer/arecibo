use ff::PrimeField;
use serde::Serialize;
use sha3::{Digest, Sha3_256};
use std::iter::Extend;
use std::marker::PhantomData;

use crate::constants::NUM_HASH_BITS;

/// For building digests
#[derive(Clone)]
pub struct DigestBuilder<F: PrimeField, T: HasDigest<F>> {
  bytes: Vec<u8>,
  hasher: Option<Sha3_256>,
  bytes_digest: [u8; 32],
  inner: Option<T>,
  _p: PhantomData<(F, T)>,
}

/// Trait to be implemented by types whose digests can be built with `DigestBuilder`.
pub trait HasDigest<F: PrimeField> {
  /// Extend `bytes` with raw bytes or digest summarizing `Digestible`.
  fn set_digest(&mut self, digest: F);
  fn set_bytes_digest(&mut self, _bytes_digest: [u8; 32]) {
    unimplemented!()
  }
}

/// Trait for components with potentially discrete digests to be included in their container's digest.
pub trait Digestible {
  /// Extend a byte sink with the bytes to be digested.
  fn extend_bytes<X: Extend<u8>>(&self, bytes: &mut X);
}

/// Marker trait to be implemented for types that implement `Digestible` and `Serialize`.
/// Their instances will be serialized to bytes then digested.
pub trait SimpleDigestible: Serialize {}

impl<T: SimpleDigestible> Digestible for T {
  fn extend_bytes<X: Extend<u8>>(&self, bytes: &mut X) {
    (*bytes).extend(bincode::serialize(self).unwrap());
  }
}

impl<F: PrimeField, T: HasDigest<F> + Digestible> DigestBuilder<F, T> {
  /// Return a new `DigestBuilder`.
  pub fn new() -> Self {
    Self {
      bytes: Default::default(),
      hasher: Some(Sha3_256::new()),
      bytes_digest: [0; 32],
      inner: None,
      _p: Default::default(),
    }
  }

  /// Initialize `DigestBuilder` with `inner`.
  pub fn init(&mut self, inner: T) {
    self.inner = Some(inner)
  }

  /// Update builder's hasher.
  pub fn update(&mut self) {
    if let Some(hasher) = self.hasher.as_mut() {
      hasher.update(&self.bytes);
    } else {
      panic!("hasher missing");
    };

    self.bytes.truncate(0);
  }

  pub fn finalize_bytes_digest(&mut self) {
    self.update();

    let Some(hasher) = self.hasher.take() else {panic!("hasher missing");};
    self.bytes_digest = hasher.finalize().into();
  }

  /// Finalize digest.
  pub fn finalize(&mut self) -> F {
    self.finalize_bytes_digest();

    let digest = self.bytes_digest;
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

  /// Extend `DigestBuilder` with the bytes provided by the underlying inner `HasDigest`.
  pub fn compute_digest(&mut self) -> F {
    let o = self.inner.as_ref().expect("inner Digestible missing");
    o.extend_bytes(&mut self.bytes);

    self.finalize()
  }

  /// Build and return inner `Digestible`.
  pub fn build(&mut self) -> T {
    let digest = self.compute_digest();

    if let Some(d) = self.inner.as_mut() {
      d.set_digest(digest)
    }
    self.inner.take().expect("inner Digestible missing")
  }
}
