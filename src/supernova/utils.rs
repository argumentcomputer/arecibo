use bellpepper_core::{
  boolean::Boolean, num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::Field;

use crate::{
  gadgets::{
    r1cs::{conditionally_select_alloc_relaxed_r1cs, AllocatedRelaxedR1CSInstance},
    utils::alloc_num_equals_const,
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
) -> Result<(Vec<Boolean>, AllocatedRelaxedR1CSInstance<G>), SynthesisError> {
  let mut a = a.iter().enumerate();
  let mut selector: Vec<Boolean> = Vec::with_capacity(a.len());

  let first_selected = alloc_num_equals_const(
    cs.namespace(|| "check 0 equal bit".to_string()),
    target_index,
    G::Base::from(0),
  )?;

  selector.push(Boolean::Is(first_selected.clone()));

  let first = a
    .next()
    .ok_or_else(|| SynthesisError::IncompatibleLengthVector("empty vec length".to_string()))?
    .1
    .clone();

  let initial_sum = Boolean::from(first_selected).lc(CS::one(), G::Base::ONE);

  let (selected, selected_sum) = a.try_fold(
    (first, initial_sum),
    |(matched, mut selected_sum), (i, candidate)| {
      let equal_bit = Boolean::Is(alloc_num_equals_const(
        cs.namespace(|| format!("check {:?} equal bit", i)),
        target_index,
        G::Base::from(i as u64),
      )?);

      selector.push(equal_bit.clone());
      selected_sum = selected_sum + &equal_bit.lc(CS::one(), G::Base::ONE);
      let next_matched_allocated = conditionally_select_alloc_relaxed_r1cs(
        cs.namespace(|| format!("next_matched_allocated-{:?}", i)),
        candidate,
        &matched,
        &equal_bit,
      )?;

      Ok::<(AllocatedRelaxedR1CSInstance<G>, LinearCombination<G::Base>), SynthesisError>((
        next_matched_allocated,
        selected_sum,
      ))
    },
  )?;

  cs.enforce(
    || "exactly-one-selection",
    |_| selected_sum,
    |lc| lc + CS::one(),
    |lc| lc + CS::one(),
  );

  Ok((selector, selected))
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::gadgets::utils::alloc_const;
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

      get_from_vec_alloc_relaxed_r1cs(&mut cs.namespace(|| "test-fn"), &vec, &allocated_target)
        .unwrap();

      if selected < n {
        assert!(cs.is_satisfied())
      } else {
        // If selected is out of range, the circuit must be unsatisfied.
        assert!(!cs.is_satisfied())
      }
    }
  }
}
