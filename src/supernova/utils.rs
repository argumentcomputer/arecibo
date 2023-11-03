use bellpepper_core::{
  boolean::Boolean, num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::Field;

use crate::{
  gadgets::{
    r1cs::{conditionally_select_alloc_relaxed_r1cs, AllocatedRelaxedR1CSInstance},
    utils::{alloc_const, alloc_num_equals, conditionally_select},
  },
  traits::Group,
};

/// Return the element of `a` at `target_index`.
///
/// If `target_index` is out of bounds, the circuit will be unsatisified.
//
// NOTE: When `a` is greater than 5 (estimated), it will be cheaper to use a multicase gadget.
//
// We should plan to rely on a well-designed gadget offering a common interface but that adapts its implementation based
// on the size of inputs (known at synthesis time). The threshold size depends on the size of the elements of `a`. The
// larger the elements, the fewer are needed before multicase becomes cost-effective.
pub fn get_from_vec_alloc_relaxed_r1cs<G: Group, CS: ConstraintSystem<<G as Group>::Base>>(
  mut cs: CS,
  a: &[AllocatedRelaxedR1CSInstance<G>],
  target_index: &AllocatedNum<G::Base>,
) -> Result<(AllocatedNum<G::Base>, AllocatedRelaxedR1CSInstance<G>), SynthesisError> {
  let mut a = a.iter().enumerate();

  let zero_index = alloc_const(cs.namespace(|| "i_const 0 allocated"), G::Base::from(0u64))?;
  let first_selected = alloc_num_equals(
    cs.namespace(|| "check 0 equal bit".to_string()),
    &zero_index,
    target_index,
  )?;

  let first = (
    zero_index,
    a.next()
      .ok_or_else(|| SynthesisError::IncompatibleLengthVector("empty vec length".to_string()))?
      .1
      .clone(),
  );

  let initial_sum = Boolean::from(first_selected).lc(CS::one(), G::Base::ONE);

  let (selected, selected_sum) = a.try_fold(
    (first, initial_sum),
    |(matched, mut selected_sum), (i, candidate)| {
      let i_const = alloc_const(
        cs.namespace(|| format!("i_const {:?} allocated", i)),
        G::Base::from(i as u64),
      )?;
      let equal_bit = Boolean::from(alloc_num_equals(
        cs.namespace(|| format!("check {:?} equal bit", i_const.get_value().unwrap())),
        &i_const,
        target_index,
      )?);
      selected_sum = selected_sum + &equal_bit.lc(CS::one(), G::Base::ONE);
      let next_matched_index = conditionally_select(
        cs.namespace(|| format!("next_matched_index-{:?}", i_const.get_value().unwrap())),
        &i_const,
        &matched.0,
        &equal_bit,
      )?;
      let next_matched_allocated = conditionally_select_alloc_relaxed_r1cs(
        cs.namespace(|| format!("next_matched_allocated-{:?}", i_const.get_value().unwrap())),
        candidate,
        &matched.1,
        &equal_bit,
      )?;

      Ok::<
        (
          (AllocatedNum<G::Base>, AllocatedRelaxedR1CSInstance<G>),
          LinearCombination<G::Base>,
        ),
        SynthesisError,
      >(((next_matched_index, next_matched_allocated), selected_sum))
    },
  )?;

  cs.enforce(
    || "exactly-one-selection",
    |_| selected_sum,
    |lc| lc + CS::one(),
    |lc| lc + CS::one(),
  );

  Ok(selected)
}

#[cfg(test)]
mod test {
  use super::*;
  use bellpepper_core::test_cs::TestConstraintSystem;
  use pasta_curves::pallas::{Base, Point};

  #[test]
  fn test_get_from_vec_alloc_relaxed_r1cs_bounds() {
    let n = 3;
    for selected in 0..(2 * n) {
      let mut cs = TestConstraintSystem::<Base>::new();

      let vec = (0..n)
        .map(|i| {
          AllocatedRelaxedR1CSInstance::<Point>::default(
            &mut cs.namespace(|| format!("elt-{i}")),
            4,
            64,
          )
          .unwrap()
        })
        .collect::<Vec<_>>();

      let allocated_target =
        alloc_const(&mut cs.namespace(|| "target"), Base::from(selected as u64)).unwrap();

      let (checked_target, _selected_instance) =
        get_from_vec_alloc_relaxed_r1cs(&mut cs.namespace(|| "test-fn"), &vec, &allocated_target)
          .unwrap();

      if selected < n {
        assert_eq!(allocated_target.get_value(), checked_target.get_value());
        assert!(cs.is_satisfied())
      } else {
        // If selected is out of range, the circuit must be unsatisfied.
        assert!(!cs.is_satisfied())
      }
    }
  }
}
