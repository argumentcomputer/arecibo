// use crate::gadgets::nonnative::bignat::BigNat;
// use crate::parafold::ecc::AllocatedPoint;
// use crate::traits::{Engine, Group};

// #[derive(Debug, Clone)]
// pub struct AllocatedSecondaryRelaxedR1CSInstance<E, G>
// where
//   E: Engine,
//   G: Group<Base = E::Scalar, Scalar = E::Base>,
// {
//   u: BigNat<E::Scalar>,
//   X: Vec<BigNat<E::Scalar>>,
//   W: AllocatedPoint<G>,
//   E: AllocatedPoint<G>,
// }

// #[derive(Debug, Clone)]
// pub struct AllocatedSecondaryFoldProof<E, G>
// where
//   E: Engine,
//   G: Group<Base = E::Scalar, Scalar = E::Base>,
// {
//   W: AllocatedPoint<E>,
//   T: AllocatedPoint<E>,
// }
