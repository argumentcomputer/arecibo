//! This module implements the Nova traits for `bn256::Point`, `bn256::Scalar`, `grumpkin::Point`, `grumpkin::Scalar`.
use crate::{
  provider::{
    traits::{DlogGroup, FixedBaseMSM, VariableBaseMSM},
    util::msm::cpu_best_msm,
  },
  traits::{Group, PrimeFieldExt, TranscriptReprTrait},
};
use digest::{ExtendableOutput, Update};
use ff::{FromUniformBytes, PrimeField};
use group::{cofactor::CofactorCurveAffine, Curve, Group as AnotherGroup};
// Remove this when https://github.com/zcash/pasta_curves/issues/41 resolves
use halo2curves::{CurveAffine, CurveExt};
use num_bigint::BigInt;
use num_traits::Num;
use rayon::prelude::*;
use sha3::Shake256;
use std::io::Read;

/// Re-exports that give access to the standard aliases used in the code base, for bn256
pub mod bn256 {
  pub use halo2curves::bn256::{
    Fq as Base, Fr as Scalar, G1Affine as Affine, G1Compressed as Compressed, G1 as Point,
  };
}

/// Re-exports that give access to the standard aliases used in the code base, for grumpkin
pub mod grumpkin {
  pub use halo2curves::grumpkin::{
    Fq as Base, Fr as Scalar, G1Affine as Affine, G1Compressed as Compressed, G1 as Point,
  };
}

macro_rules! impl_traits {
  (
    $name:ident,
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
      type ScalarExt = $name::Scalar;
      type AffineExt = $name::Affine;
      // note: for halo2curves implementations, $name::Compressed == <$name::Point as GroupEncoding>::Repr
      // so the blanket impl<T> From<T> for T and impl<T> Into<T> apply.
      type Compressed = $name::Compressed;

      fn from_label(label: &'static [u8], n: usize) -> Vec<Self::Affine> {
        let mut shake = Shake256::default();
        shake.update(label);
        let mut reader = shake.finalize_xof();
        let mut uniform_bytes_vec = Vec::new();
        for _ in 0..n {
          let mut uniform_bytes = [0u8; 32];
          reader.read_exact(&mut uniform_bytes).unwrap();
          uniform_bytes_vec.push(uniform_bytes);
        }
        let gens_proj: Vec<$name::Point> = (0..n)
          .into_par_iter()
          .map(|i| {
            let hash = $name::Point::hash_to_curve("from_uniform_bytes");
            hash(&uniform_bytes_vec[i])
          })
          .collect();

        let num_threads = rayon::current_num_threads();
        if gens_proj.len() > num_threads {
          let chunk = (gens_proj.len() as f64 / num_threads as f64).ceil() as usize;
          (0..num_threads)
            .into_par_iter()
            .flat_map(|i| {
              let start = i * chunk;
              let end = if i == num_threads - 1 {
                gens_proj.len()
              } else {
                core::cmp::min((i + 1) * chunk, gens_proj.len())
              };
              if end > start {
                let mut gens = vec![$name::Affine::identity(); end - start];
                <Self as Curve>::batch_normalize(&gens_proj[start..end], &mut gens);
                gens
              } else {
                vec![]
              }
            })
            .collect()
        } else {
          let mut gens = vec![$name::Affine::identity(); n];
          <Self as Curve>::batch_normalize(&gens_proj, &mut gens);
          gens
        }
      }

      fn to_coordinates(&self) -> (Self::Base, Self::Base, bool) {
        let coordinates = self.to_affine().coordinates();
        if coordinates.is_some().unwrap_u8() == 1 && ($name::Point::identity() != *self) {
          (*coordinates.unwrap().x(), *coordinates.unwrap().y(), false)
        } else {
          (Self::Base::zero(), Self::Base::zero(), true)
        }
      }
    }

    impl VariableBaseMSM for $name::Point {
      #[tracing::instrument(skip_all, name = "vartime_multiscalar_mul")]
      fn vartime_multiscalar_mul(scalars: &[Self::ScalarExt], bases: &[Self::Affine]) -> Self {
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        if scalars.len() >= 128 {
          grumpkin_msm::$name::msm(bases, scalars)
        } else {
          cpu_best_msm(bases, scalars)
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        cpu_best_msm(bases, scalars)
      }
    }

    impl FixedBaseMSM for $name::Point {
      type MSMContext<'a> = grumpkin_msm::$name::MSMContext<'a>;

      fn init_context<'a>(bases: &'a [Self::AffineExt]) -> Self::MSMContext<'a> {
        cfg_if::cfg_if! {
          if #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))] {
            grumpkin_msm::$name::init(bases)
          } else {
            Self::MSMContext::new_cpu(bases)
          }
        }
      }

      #[tracing::instrument(skip_all, name = "fixed_multiscalar_mul")]
      fn fixed_multiscalar_mul<'a>(scalars: &[Self::ScalarExt], context: &Self::MSMContext<'a>) -> Self {
        cfg_if::cfg_if! {
          if #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))] {
            grumpkin_msm::$name::with(context, scalars)
          } else {
            cpu_best_msm(context.points(), scalars)
          }
        }
      }
    }

    impl PrimeFieldExt for $name::Scalar {
      fn from_uniform(bytes: &[u8]) -> Self {
        let bytes_arr: [u8; 64] = bytes.try_into().unwrap();
        $name::Scalar::from_uniform_bytes(&bytes_arr)
      }
    }

    impl<G: DlogGroup> TranscriptReprTrait<G> for $name::Compressed {
      fn to_transcript_bytes(&self) -> Vec<u8> {
        self.as_ref().to_vec()
      }
    }

    impl<G: Group> TranscriptReprTrait<G> for $name::Scalar {
      fn to_transcript_bytes(&self) -> Vec<u8> {
        self.to_repr().to_vec()
      }
    }

    impl<G: DlogGroup> TranscriptReprTrait<G> for $name::Affine {
      fn to_transcript_bytes(&self) -> Vec<u8> {
        let (x, y, is_infinity_byte) = {
          let coordinates = self.coordinates();
          if coordinates.is_some().unwrap_u8() == 1 && ($name::Affine::identity() != *self) {
            let c = coordinates.unwrap();
            (*c.x(), *c.y(), u8::from(false))
          } else {
            ($name::Base::zero(), $name::Base::zero(), u8::from(false))
          }
        };

        x.to_repr()
          .into_iter()
          .chain(y.to_repr().into_iter())
          .chain(std::iter::once(is_infinity_byte))
          .collect()
      }
    }
  };
}

impl_traits!(
  bn256,
  "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"
);

impl_traits!(
  grumpkin,
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47",
  "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"
);

#[cfg(test)]
mod tests {
  use ff::Field;
  use rand::thread_rng;

  use crate::provider::{
    bn256_grumpkin::{bn256, grumpkin},
    traits::{DlogGroup, VariableBaseMSM},
    util::msm::cpu_best_msm,
  };

  #[test]
  fn test_bn256_msm_correctness() {
    let npoints = 1usize << 16;
    let points = bn256::Point::from_label(b"test", npoints);

    let mut rng = thread_rng();
    let scalars = (0..npoints)
      .map(|_| bn256::Scalar::random(&mut rng))
      .collect::<Vec<_>>();

    let cpu_msm = cpu_best_msm(&points, &scalars);
    let gpu_msm = bn256::Point::vartime_multiscalar_mul(&scalars, &points);

    assert_eq!(cpu_msm, gpu_msm);
  }

  #[test]
  fn test_grumpkin_msm_correctness() {
    let npoints = 1usize << 16;
    let points = grumpkin::Point::from_label(b"test", npoints);

    let mut rng = thread_rng();
    let scalars = (0..npoints)
      .map(|_| grumpkin::Scalar::random(&mut rng))
      .collect::<Vec<_>>();

    let cpu_msm = cpu_best_msm(&points, &scalars);
    let gpu_msm = grumpkin::Point::vartime_multiscalar_mul(&scalars, &points);

    assert_eq!(cpu_msm, gpu_msm);
  }
}
