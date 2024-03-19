use crate::bellpepper::test_shape_cs::TestShapeCS;
use crate::provider::Bn256EngineKZG;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::ConstraintSystem;
use digest::consts::U24;
use halo2curves::bn256::Fr;
use neptune::circuit2::Elt;
use neptune::poseidon::PoseidonConstants;
use neptune::sponge::api::{IOPattern, SpongeAPI, SpongeOp};
use neptune::sponge::circuit::SpongeCircuit;
use neptune::sponge::vanilla::Mode::Simplex;
use neptune::sponge::vanilla::SpongeTrait;

#[test]
fn test_neptune_absorb() {
  let mut cs: TestShapeCS<Bn256EngineKZG> = TestShapeCS::new();
  let constant = PoseidonConstants::<Fr, U24>::default();
  let mut sponge = SpongeCircuit::new_with_constants(&constant, Simplex);
  let inputs = (0..2)
    .map(|i| {
      AllocatedNum::alloc(cs.namespace(|| format!("input {}", i)), || Ok(Fr::from(1))).unwrap()
    })
    .collect::<Vec<AllocatedNum<Fr>>>();

  let mut ns = cs.namespace(|| "ns");

  let acc = &mut ns;
  let parameter = IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1u32)]);
  sponge.start(parameter, None, acc);

  neptune::sponge::api::SpongeAPI::absorb(
    &mut sponge,
    2,
    &inputs
      .iter()
      .map(|alloc| Elt::Allocated(alloc.clone()))
      .collect::<Vec<Elt<Fr>>>(),
    acc,
  );
}
