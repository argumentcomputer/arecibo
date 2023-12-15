//! This module implements the Nova traits for `bn256::Point`, `bn256::Scalar`, `grumpkin::Point`, `grumpkin::Scalar`.
use crate::{
  provider::{
    traits::{CompressedGroup, DlogGroup},
    util::msm::cpu_best_msm,
  },
  traits::{Group, PrimeFieldExt, TranscriptReprTrait},
};
use digest::{ExtendableOutput, Update};
use ff::{FromUniformBytes, PrimeField};
use group::{cofactor::CofactorCurveAffine, Curve, Group as AnotherGroup, GroupEncoding};
use num_bigint::BigInt;
use num_traits::Num;
// Remove this when https://github.com/zcash/pasta_curves/issues/41 resolves
use pasta_curves::arithmetic::{CurveAffine, CurveExt};
use rayon::prelude::*;
use sha3::Shake256;
use std::io::Read;

use halo2curves::bn256::{
  G1Affine as Bn256Affine, G1Compressed as Bn256Compressed, G1 as Bn256Point,
};
use halo2curves::grumpkin::{
  G1Affine as GrumpkinAffine, G1Compressed as GrumpkinCompressed, G1 as GrumpkinPoint,
};

/// Re-exports that give access to the standard aliases used in the code base, for bn256
pub mod bn256 {
  pub use halo2curves::bn256::{Fq as Base, Fr as Scalar, G1Affine as Affine, G1 as Point};
}

/// Re-exports that give access to the standard aliases used in the code base, for grumpkin
pub mod grumpkin {
  pub use halo2curves::grumpkin::{Fq as Base, Fr as Scalar, G1Affine as Affine, G1 as Point};
}

macro_rules! impl_traits {
  (
    $name:ident,
    $name_compressed:ident,
    $name_curve:ident,
    $name_curve_affine:ident,
    $order_str:literal,
    $base_str:literal
  ) => {
    impl Group for $name::Point {
      type Base = $name::Base;
      type Scalar = $name::Scalar;

      fn group_params() -> (Self::Base, Self::Base, BigInt, BigInt) {
        let A = $name::Point::a();
        let B = $name::Point::b();
        let order = BigInt::from_str_radix($order_str, 16).unwrap();
        let base = BigInt::from_str_radix($base_str, 16).unwrap();

        (A, B, order, base)
      }
    }

    impl DlogGroup for $name::Point {
      type CompressedGroupElement = $name_compressed;
      type PreprocessedGroupElement = $name::Affine;

      #[tracing::instrument(
        skip_all,
        level = "trace",
        name = "<_ as Group>::vartime_multiscalar_mul"
      )]
      fn vartime_multiscalar_mul(
        scalars: &[Self::Scalar],
        bases: &[Self::PreprocessedGroupElement],
      ) -> Self {
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        if scalars.len() >= 128 {
          grumpkin_msm::$name(bases, scalars)
        } else {
          cpu_best_msm(scalars, bases)
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        cpu_best_msm(scalars, bases)
      }

      fn preprocessed(&self) -> Self::PreprocessedGroupElement {
        self.to_affine()
      }

      fn compress(&self) -> Self::CompressedGroupElement {
        self.to_bytes()
      }

      fn from_label(label: &'static [u8], n: usize) -> Vec<Self::PreprocessedGroupElement> {
        let mut shake = Shake256::default();
        shake.update(label);
        let mut reader = shake.finalize_xof();
        let mut uniform_bytes_vec = Vec::new();
        for _ in 0..n {
          let mut uniform_bytes = [0u8; 32];
          reader.read_exact(&mut uniform_bytes).unwrap();
          uniform_bytes_vec.push(uniform_bytes);
        }
        let ck_proj: Vec<$name_curve> = (0..n)
          .into_par_iter()
          .map(|i| {
            let hash = $name_curve::hash_to_curve("from_uniform_bytes");
            hash(&uniform_bytes_vec[i])
          })
          .collect();

        let num_threads = rayon::current_num_threads();
        if ck_proj.len() > num_threads {
          let chunk = (ck_proj.len() as f64 / num_threads as f64).ceil() as usize;
          (0..num_threads)
            .into_par_iter()
            .flat_map(|i| {
              let start = i * chunk;
              let end = if i == num_threads - 1 {
                ck_proj.len()
              } else {
                core::cmp::min((i + 1) * chunk, ck_proj.len())
              };
              if end > start {
                let mut ck = vec![$name_curve_affine::identity(); end - start];
                <Self as Curve>::batch_normalize(&ck_proj[start..end], &mut ck);
                ck
              } else {
                vec![]
              }
            })
            .collect()
        } else {
          let mut ck = vec![$name_curve_affine::identity(); n];
          <Self as Curve>::batch_normalize(&ck_proj, &mut ck);
          ck
        }
      }

      fn zero() -> Self {
        $name::Point::identity()
      }

      fn to_coordinates(&self) -> (Self::Base, Self::Base, bool) {
        let coordinates = self.to_affine().coordinates();
        if coordinates.is_some().unwrap_u8() == 1 {
          (*coordinates.unwrap().x(), *coordinates.unwrap().y(), false)
        } else {
          (Self::Base::zero(), Self::Base::zero(), true)
        }
      }
    }

    impl PrimeFieldExt for $name::Scalar {
      fn from_uniform(bytes: &[u8]) -> Self {
        let bytes_arr: [u8; 64] = bytes.try_into().unwrap();
        $name::Scalar::from_uniform_bytes(&bytes_arr)
      }
    }

    impl CompressedGroup for $name_compressed {
      type GroupElement = $name::Point;

      fn decompress(&self) -> Option<$name::Point> {
        Some($name_curve::from_bytes(&self).unwrap())
      }
    }

    impl<G: DlogGroup> TranscriptReprTrait<G> for $name_compressed {
      fn to_transcript_bytes(&self) -> Vec<u8> {
        self.as_ref().to_vec()
      }
    }

    impl<G: Group> TranscriptReprTrait<G> for $name::Scalar {
      fn to_transcript_bytes(&self) -> Vec<u8> {
        self.to_repr().to_vec()
      }
    }
  };
}

impl_traits!(
  bn256,
  Bn256Compressed,
  Bn256Point,
  Bn256Affine,
  "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"
);

impl_traits!(
  grumpkin,
  GrumpkinCompressed,
  GrumpkinPoint,
  GrumpkinAffine,
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47",
  "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"
);
