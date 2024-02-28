//! This module implements various gadgets necessary for Nova and applications built with Nova.
mod ecc;
pub(crate) use ecc::AllocatedPoint;

mod nonnative;
pub(crate) use nonnative::{bignat::nat_to_limbs, util::f_to_nat};

pub(crate) mod r1cs;
pub(crate) mod utils;
