//! Global Nova constants

pub(crate) const NUM_CHALLENGE_BITS: usize = 128;
pub(crate) const BN_LIMB_WIDTH: usize = 64;
pub(crate) const BN_N_LIMBS: usize = 4;
pub(crate) const NUM_FE_WITHOUT_IO_FOR_CRHF: usize = 9 + NIO_NOVA_FOLD * BN_N_LIMBS;
pub(crate) const NUM_FE_FOR_RO: usize = 9;
pub(crate) const NIO_NOVA_FOLD: usize = 2;

/// Bit size of Nova field element hashes
pub const NUM_HASH_BITS: usize = 250;
