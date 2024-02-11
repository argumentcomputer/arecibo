use ff::PrimeField;
use group::Group;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

/// Wrapper struct around a field element that implements additional traits
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FWrap<F>(pub F);

impl<F: PrimeField> Copy for FWrap<F> {}

#[cfg(not(target_arch = "wasm32"))]
/// Trait implementation for generating `FWrap<F>` instances with proptest
impl<F: PrimeField> Arbitrary for FWrap<F> {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
    use rand::rngs::StdRng;
    use rand_core::SeedableRng;

    let strategy = any::<[u8; 32]>()
      .prop_map(|seed| Self(F::random(StdRng::from_seed(seed))))
      .no_shrink();
    strategy.boxed()
  }
}

/// Wrapper struct around a Group element that implements additional traits
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GWrap<G>(pub G);

impl<G: Group> Copy for GWrap<G> {}

#[cfg(not(target_arch = "wasm32"))]
/// Trait implementation for generating `GWrap<F>` instances with proptest
impl<G: Group> Arbitrary for GWrap<G> {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
    use rand::rngs::StdRng;
    use rand_core::SeedableRng;

    let strategy = any::<[u8; 32]>()
      .prop_map(|seed| Self(G::random(StdRng::from_seed(seed))))
      .no_shrink();
    strategy.boxed()
  }
}
