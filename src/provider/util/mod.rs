/// Utilities for provider module
pub(in crate::provider) mod fb_msm;
pub mod msm {
  use halo2curves::msm::best_multiexp;
  use halo2curves::CurveAffine;

  // this argument swap is useful until Rust gets named arguments
  // and saves significant complexity in macro code
  pub fn cpu_best_msm<C: CurveAffine>(bases: &[C], scalars: &[C::Scalar]) -> C::Curve {
    best_multiexp(scalars, bases)
  }
}
