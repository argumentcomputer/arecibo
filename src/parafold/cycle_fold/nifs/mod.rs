pub mod circuit;
pub mod prover;

/// The IO of the secondary circuit is always composed of 4 base field elements
/// `[hash_A, hash_B, scalar, hash_C]`
pub const NUM_IO_SECONDARY: usize = 4;


