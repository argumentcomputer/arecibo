//! This module implements lookup gadget for applications built with Nova.
use std::cmp::max;
use std::collections::btree_map::Iter;
use std::collections::btree_map::Values;
use std::collections::BTreeMap;

use crate::Engine;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError};
use std::cmp::Ord;

use crate::constants::NUM_CHALLENGE_BITS;
use crate::gadgets::nonnative::util::Num;
use crate::spartan::math::Math;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::AbsorbInROTrait;
use crate::traits::ROCircuitTrait;
use crate::traits::ROConstants;
use crate::traits::ROConstantsCircuit;
use crate::traits::ROTrait;
use ff::{Field, PrimeField};

use super::utils::scalar_as_base;
use super::utils::{alloc_one, conditionally_select2, le_bits_to_num};
use bellpepper_core::boolean::Boolean;

/// alloc a field as a constant
/// implemented refer from <https://github.com/lurk-lab/lurk-rs/blob/4335fbb3290ed1a1176e29428f7daacb47f8033d/src/circuit/gadgets/data.rs#L387-L402>
pub fn alloc_const<F: PrimeField, CS: ConstraintSystem<F>>(mut cs: CS, val: F) -> AllocatedNum<F> {
  let allocated = AllocatedNum::<F>::alloc_infallible(cs.namespace(|| "allocate const"), || val);

  // allocated * 1 = val
  cs.enforce(
    || "enforce constant",
    |lc| lc + allocated.get_variable(),
    |lc| lc + CS::one(),
    |_| Boolean::Constant(true).lc(CS::one(), val),
  );

  allocated
}

/// rw trace
#[derive(Clone, Debug)]
pub enum RWTrace<T> {
  /// read
  Read(T, T, T), // addr, read_value, read_counter
  /// write
  Write(T, T, T, T), // addr, read_value, write_value, read_counter
}

/// Lookup in R1CS
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TableType {
  /// read only
  ReadOnly,
  /// write
  ReadWrite,
}

/// for build up a lookup trace
#[derive(Clone)]
pub struct LookupTrace<E: Engine> {
  expected_rw_trace: Vec<RWTrace<E::Scalar>>,
  rw_trace_allocated_num: Vec<RWTrace<AllocatedNum<E::Scalar>>>,
  max_cap_rwcounter_log2: usize,
  table_type: TableType,
  cursor: usize,
}

impl<E: Engine> LookupTrace<E> {
  /// read value from table
  pub fn read<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &mut self,
    mut cs: CS,
    addr: &AllocatedNum<E::Scalar>,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError>
  where
    <E as Engine>::Scalar: Ord + PartialEq + Eq,
  {
    assert!(
      self.cursor < self.expected_rw_trace.len(),
      "cursor {} out of range with expected length {}",
      self.cursor,
      self.expected_rw_trace.len()
    );
    let RWTrace::Read(expected_addr, expected_read_value, expected_read_counter) =
      self.expected_rw_trace[self.cursor]
    else {
      Err(SynthesisError::AssignmentMissing)?
    };

    if let Some(key) = addr.get_value() {
      assert!(
        key == expected_addr,
        "read address {:?} mismatch with expected {:?}",
        key,
        expected_addr
      );
    }
    let read_value =
      AllocatedNum::alloc(cs.namespace(|| "read_value"), || Ok(expected_read_value))?;
    let read_counter = AllocatedNum::alloc(cs.namespace(|| "read_counter"), || {
      Ok(expected_read_counter)
    })?;
    self
      .rw_trace_allocated_num
      .push(RWTrace::Read::<AllocatedNum<E::Scalar>>(
        addr.clone(),
        read_value.clone(),
        read_counter,
      )); // append read trace

    self.cursor += 1;
    Ok(read_value)
  }

  /// write value to lookup table
  pub fn write<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &mut self,
    mut cs: CS,
    addr: &AllocatedNum<E::Scalar>,
    value: &AllocatedNum<E::Scalar>,
  ) -> Result<(), SynthesisError>
  where
    <E as Engine>::Scalar: Ord,
  {
    assert!(
      self.cursor < self.expected_rw_trace.len(),
      "cursor {} out of range with expected length {}",
      self.cursor,
      self.expected_rw_trace.len()
    );
    let RWTrace::Write(
      expected_addr,
      expected_read_value,
      expected_write_value,
      expected_read_counter,
    ) = self.expected_rw_trace[self.cursor]
    else {
      Err(SynthesisError::AssignmentMissing)?
    };

    if let Some((addr, value)) = addr.get_value().zip(value.get_value()) {
      assert!(
        addr == expected_addr,
        "write address {:?} mismatch with expected {:?}",
        addr,
        expected_addr
      );
      assert!(
        value == expected_write_value,
        "write value {:?} mismatch with expected {:?}",
        value,
        expected_write_value
      );
    }

    let expected_read_value =
      AllocatedNum::alloc(cs.namespace(|| "read_value"), || Ok(expected_read_value))?;
    let expected_read_counter = AllocatedNum::alloc(cs.namespace(|| "read_counter"), || {
      Ok(expected_read_counter)
    })?;
    self.rw_trace_allocated_num.push(RWTrace::Write(
      addr.clone(),
      expected_read_value,
      value.clone(),
      expected_read_counter,
    )); // append write trace
    self.cursor += 1;
    Ok(())
  }

  /// commit rw_trace to lookup
  #[allow(clippy::too_many_arguments)]
  pub fn commit<E2: Engine, CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &mut self,
    mut cs: CS,
    ro_const: ROConstantsCircuit<E2>,
    prev_intermediate_gamma: &AllocatedNum<E::Scalar>,
    challenges: &(AllocatedNum<E::Scalar>, AllocatedNum<E::Scalar>),
    prev_R: &AllocatedNum<E::Scalar>,
    prev_W: &AllocatedNum<E::Scalar>,
    prev_rw_counter: &AllocatedNum<E::Scalar>,
  ) -> Result<
    (
      AllocatedNum<E::Scalar>,
      AllocatedNum<E::Scalar>,
      AllocatedNum<E::Scalar>,
      AllocatedNum<E::Scalar>,
    ),
    SynthesisError,
  >
  where
    <E as Engine>::Scalar: Ord,
    E: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E as Engine>::Scalar>,
  {
    let mut ro = E2::ROCircuit::new(
      ro_const,
      1 + 3 * self.expected_rw_trace.len(), // prev_challenge + [(address, value, counter)]
    );
    ro.absorb(prev_intermediate_gamma);
    let rw_trace_allocated_num = &self.rw_trace_allocated_num;
    let (next_R, next_W, next_rw_counter) = rw_trace_allocated_num.iter().enumerate().try_fold(
      (prev_R.clone(), prev_W.clone(), prev_rw_counter.clone()),
      |(prev_R, prev_W, prev_rw_counter), (i, rwtrace)| match rwtrace {
        RWTrace::Read(addr, read_value, expected_read_counter) => {
          let (next_R, next_W, next_rw_counter) = self.rw_operation_circuit(
            cs.namespace(|| format!("{}th read ", i)),
            addr,
            challenges,
            read_value,
            read_value,
            &prev_R,
            &prev_W,
            expected_read_counter,
            &prev_rw_counter,
          )?;
          ro.absorb(addr);
          ro.absorb(read_value);
          ro.absorb(expected_read_counter);
          Ok::<
            (
              AllocatedNum<E::Scalar>,
              AllocatedNum<E::Scalar>,
              AllocatedNum<E::Scalar>,
            ),
            SynthesisError,
          >((next_R, next_W, next_rw_counter))
        }
        RWTrace::Write(addr, read_value, write_value, read_counter) => {
          let (next_R, next_W, next_rw_counter) = self.rw_operation_circuit(
            cs.namespace(|| format!("{}th write ", i)),
            addr,
            challenges,
            read_value,
            write_value,
            &prev_R,
            &prev_W,
            read_counter,
            &prev_rw_counter,
          )?;
          ro.absorb(addr);
          ro.absorb(read_value);
          ro.absorb(read_counter);
          Ok::<
            (
              AllocatedNum<E::Scalar>,
              AllocatedNum<E::Scalar>,
              AllocatedNum<E::Scalar>,
            ),
            SynthesisError,
          >((next_R, next_W, next_rw_counter))
        }
      },
    )?;
    let hash_bits = ro.squeeze(cs.namespace(|| "challenge"), NUM_CHALLENGE_BITS)?;
    let hash = le_bits_to_num(cs.namespace(|| "bits to hash"), &hash_bits)?;
    Ok((next_R, next_W, next_rw_counter, hash))
  }

  #[allow(clippy::too_many_arguments)]
  fn rw_operation_circuit<F: PrimeField, CS: ConstraintSystem<F>>(
    &self,
    mut cs: CS,
    addr: &AllocatedNum<F>,
    challenges: &(AllocatedNum<F>, AllocatedNum<F>),
    read_value: &AllocatedNum<F>,
    write_value: &AllocatedNum<F>,
    prev_R: &AllocatedNum<F>,
    prev_W: &AllocatedNum<F>,
    read_counter: &AllocatedNum<F>,
    prev_rw_counter: &AllocatedNum<F>,
  ) -> Result<(AllocatedNum<F>, AllocatedNum<F>, AllocatedNum<F>), SynthesisError>
  where
    F: Ord,
  {
    let (alpha, gamma) = challenges;
    // update R
    let gamma_square = gamma.mul(cs.namespace(|| "gamme^2"), gamma)?;
    // read_value_term = gamma * value
    let read_value_term = gamma.mul(cs.namespace(|| "read_value_term"), read_value)?;
    // counter_term = gamma^2 * counter
    let read_counter_term = gamma_square.mul(cs.namespace(|| "read_counter_term"), read_counter)?;
    // new_R = R + 1 / (alpha + (addr + gamma * value + gamma^2 * counter))
    let new_R = AllocatedNum::alloc(cs.namespace(|| "new_R"), || {
      prev_R
        .get_value()
        .zip(alpha.get_value())
        .zip(addr.get_value())
        .zip(read_value_term.get_value())
        .zip(read_counter_term.get_value())
        .map(|((((R, alpha), addr), value_term), counter_term)| {
          R + (alpha + (addr + value_term + counter_term))
            .invert()
            .expect("invert failed due to read term is 0") // negilible probability for invert failed
        })
        .ok_or(SynthesisError::AssignmentMissing)
    })?;
    let mut r_blc = LinearCombination::<F>::zero();
    r_blc = r_blc
      + alpha.get_variable()
      + addr.get_variable()
      + read_value_term.get_variable()
      + read_counter_term.get_variable();
    cs.enforce(
      || "R update",
      |lc| lc + new_R.get_variable() - prev_R.get_variable(),
      |_| r_blc,
      |lc| lc + CS::one(),
    );

    let alloc_num_one = alloc_one(cs.namespace(|| "one"));
    // max{read_counter, rw_counter} logic on read-write lookup
    // read_counter on read-only
    // - max{read_counter, rw_counter} if read-write table
    // - read_counter if read-only table
    // +1 will be hadle later
    let (write_counter, write_counter_term) = if self.table_type == TableType::ReadWrite {
      // write_counter = read_counter < prev_rw_counter ? prev_rw_counter: read_counter
      // TODO optimise with `max` table lookup to save more constraints
      let lt = less_than(
        cs.namespace(|| "read_counter < a"),
        read_counter,
        prev_rw_counter,
        self.max_cap_rwcounter_log2,
      )?;
      let write_counter = conditionally_select2(
        cs.namespace(|| {
          "write_counter = read_counter < prev_rw_counter ? prev_rw_counter: read_counter"
        }),
        prev_rw_counter,
        read_counter,
        &lt,
      )?;
      let write_counter_term =
        gamma_square.mul(cs.namespace(|| "write_counter_term"), &write_counter)?;
      (write_counter, write_counter_term)
    } else {
      (read_counter.clone(), read_counter_term)
    };

    // update W
    // write_value_term = gamma * value
    let write_value_term = gamma.mul(cs.namespace(|| "write_value_term"), write_value)?;
    let new_W = AllocatedNum::alloc(cs.namespace(|| "new_W"), || {
      prev_W
        .get_value()
        .zip(alpha.get_value())
        .zip(addr.get_value())
        .zip(write_value_term.get_value())
        .zip(write_counter_term.get_value())
        .zip(gamma_square.get_value())
        .map(
          |(((((W, alpha), addr), value_term), write_counter_term), gamma_square)| {
            W + (alpha + (addr + value_term + write_counter_term + gamma_square))
              .invert()
              .expect("invert failed due to write term is 0") // negilible probability for invert failed
          },
        )
        .ok_or(SynthesisError::AssignmentMissing)
    })?;
    // new_W = W + 1 / (alpha - (addr + gamma * value + gamma^2 * counter))
    let mut w_blc = LinearCombination::<F>::zero();
    w_blc = w_blc
      + alpha.get_variable()
      + addr.get_variable()
      + write_value_term.get_variable()
      + write_counter_term.get_variable()
      + gamma_square.get_variable();
    cs.enforce(
      || "W update",
      |lc| lc + new_W.get_variable() - prev_W.get_variable(),
      |_| w_blc,
      |lc| lc + CS::one(),
    );

    let new_rw_counter = add_allocated_num(
      cs.namespace(|| "new_rw_counter"),
      &write_counter,
      &alloc_num_one,
    )?;

    // update accu
    Ok((new_R, new_W, new_rw_counter))
  }
}

/// for build up a lookup trace
pub struct LookupTraceBuilder<'a, E: Engine> {
  lookup: &'a mut Lookup<E::Scalar>,
  rw_trace: Vec<RWTrace<E::Scalar>>,
  map_aux: BTreeMap<E::Scalar, (E::Scalar, E::Scalar)>,
}

impl<'a, E: Engine> LookupTraceBuilder<'a, E> {
  /// start a new transaction simulated
  pub fn new(lookup: &'a mut Lookup<E::Scalar>) -> LookupTraceBuilder<'a, E> {
    LookupTraceBuilder {
      lookup,
      rw_trace: vec![],
      map_aux: BTreeMap::new(),
    }
  }

  /// read value from table
  pub fn read(&mut self, addr: E::Scalar) -> E::Scalar
  where
    <E as Engine>::Scalar: Ord,
  {
    let key = &addr;
    let (value, _) = self.map_aux.entry(*key).or_insert_with(|| {
      self
        .lookup
        .map_aux
        .get(key)
        .cloned()
        .unwrap_or((E::Scalar::ZERO, E::Scalar::ZERO))
    });
    self
      .rw_trace
      .push(RWTrace::Read(addr, *value, E::Scalar::ZERO));
    *value
  }
  /// write value to lookup table
  pub fn write(&mut self, addr: E::Scalar, value: E::Scalar)
  where
    <E as Engine>::Scalar: Ord,
  {
    let _ = self.map_aux.insert(
      addr,
      (
        value,
        E::Scalar::ZERO, // zero counter doens't matter, real counter will provided in snapshot stage
      ),
    );
    self.rw_trace.push(RWTrace::Write(
      addr,
      E::Scalar::ZERO,
      value,
      E::Scalar::ZERO,
    )); // append read trace
  }

  /// commit rw_trace to lookup
  pub fn snapshot<E2: Engine>(
    &mut self,
    ro_consts: ROConstants<E2>,
    prev_intermediate_gamma: E::Scalar,
  ) -> (E::Scalar, LookupTrace<E>)
  where
    <E as Engine>::Scalar: Ord,
    E: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E as Engine>::Scalar>,
  {
    let mut hasher: <E2 as Engine>::RO =
      <E2 as Engine>::RO::new(ro_consts, 1 + self.rw_trace.len() * 3);
    hasher.absorb(prev_intermediate_gamma);

    let rw_processed = self
      .rw_trace
      .drain(..)
      .map(|rwtrace| {
        let (rw_trace_with_counter, addr, read_value, read_counter) = match rwtrace {
          RWTrace::Read(addr, expected_read_value, _) => {
            let (read_value, read_counter) = self.lookup.rw_operation(addr, None);
            assert_eq!(
              read_value, expected_read_value,
              "expected_read_value {:?} != read_value {:?}",
              expected_read_value, read_value
            );
            (
              RWTrace::Read(addr, expected_read_value, read_counter),
              addr,
              expected_read_value,
              read_counter,
            )
          }
          RWTrace::Write(addr, _, write_value, _) => {
            let (read_value, read_counter) = self.lookup.rw_operation(addr, Some(write_value));
            (
              RWTrace::Write(addr, read_value, write_value, read_counter),
              addr,
              read_value,
              read_counter,
            )
          }
        };
        hasher.absorb(addr);
        hasher.absorb(read_value);
        hasher.absorb(read_counter);

        rw_trace_with_counter
      })
      .collect();
    let hash_bits = hasher.squeeze(NUM_CHALLENGE_BITS);
    let next_intermediate_gamma = scalar_as_base::<E2>(hash_bits);
    (
      next_intermediate_gamma,
      LookupTrace {
        expected_rw_trace: rw_processed,
        rw_trace_allocated_num: vec![],
        cursor: 0,
        max_cap_rwcounter_log2: self.lookup.max_cap_rwcounter_log2,
        table_type: self.lookup.table_type.clone(),
      },
    )
  }

  /// get permutation fingerprints challenge
  pub fn get_challenge<E2: Engine>(
    ck: &<<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey,
    final_table: &Lookup<E::Scalar>,
    intermediate_gamma: E::Scalar,
  ) -> (E::Scalar, E::Scalar)
  where
    E: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E as Engine>::Scalar>,
  {
    let ro_consts =
      <<E as Engine>::RO as ROTrait<<E as Engine>::Base, <E as Engine>::Scalar>>::Constants::default();
    let (final_values, final_counters): (Vec<_>, Vec<_>) =
      final_table.map_aux.values().copied().unzip();

    // final_value and final_counter
    let (comm_final_value, comm_final_counter) = rayon::join(
      || E::CE::commit(ck, &final_values),
      || E::CE::commit(ck, &final_counters),
    );

    // gamma
    let mut hasher = <E as Engine>::RO::new(ro_consts.clone(), 7);
    let intermediate_gamma: E2::Scalar = scalar_as_base::<E>(intermediate_gamma);
    hasher.absorb(intermediate_gamma);
    comm_final_value.absorb_in_ro(&mut hasher);
    comm_final_counter.absorb_in_ro(&mut hasher);
    let gamma = hasher.squeeze(NUM_CHALLENGE_BITS);

    // alpha
    let mut hasher = <E as Engine>::RO::new(ro_consts, 1);
    hasher.absorb(scalar_as_base::<E>(gamma));
    let alpha = hasher.squeeze(NUM_CHALLENGE_BITS);
    (alpha, gamma)
  }
}

/// Lookup in R1CS
#[derive(Clone, Debug)]
pub struct Lookup<F: PrimeField> {
  map_aux: BTreeMap<F, (F, F)>, // (value, counter)
  rw_counter: F,
  pub(crate) table_type: TableType, // read only or read-write
  pub(crate) max_cap_rwcounter_log2: usize, // max cap for rw_counter operation in bits
}

impl<F: PrimeField> Lookup<F> {
  /// new lookup table
  pub fn new(
    max_cap_rwcounter: usize,
    table_type: TableType,
    initial_table: Vec<(F, F)>,
  ) -> Lookup<F>
  where
    F: Ord,
  {
    let max_cap_rwcounter_log2 = max_cap_rwcounter.log_2();
    Self {
      map_aux: initial_table
        .into_iter()
        .enumerate()
        .map(|(i, (addr, value))| {
          assert!(F::from(i as u64) == addr);
          (addr, (value, F::ZERO))
        })
        .collect(),
      rw_counter: F::ZERO,
      table_type,
      max_cap_rwcounter_log2,
    }
  }

  /// table size
  pub fn table_size(&self) -> usize {
    self.map_aux.len()
  }

  /// padding
  pub fn padding(&mut self, N: usize)
  where
    F: Ord,
  {
    assert!(self.map_aux.len() <= N);
    (self.map_aux.len()..N).for_each(|addr| {
      self
        .map_aux
        .insert(F::from(addr as u64), (F::ZERO, F::ZERO));
    });
  }

  /// table values
  pub fn values(&self) -> Values<'_, F, (F, F)> {
    self.map_aux.values()
  }

  fn rw_operation(&mut self, addr: F, external_value: Option<F>) -> (F, F)
  where
    F: Ord,
  {
    // write operations
    if external_value.is_some() {
      debug_assert!(self.table_type == TableType::ReadWrite) // table need to set as rw
    }
    let (read_value, read_counter) = self
      .map_aux
      .get(&addr)
      .cloned()
      .unwrap_or((F::from(0), F::from(0)));

    let (write_value, write_counter) = (
      external_value.unwrap_or(read_value),
      if self.table_type == TableType::ReadOnly {
        read_counter
      } else {
        max(self.rw_counter, read_counter)
      } + F::ONE,
    );
    self.map_aux.insert(addr, (write_value, write_counter));
    self.rw_counter = write_counter;
    (read_value, read_counter)
  }
}

impl<'a, F: PrimeField> IntoIterator for &'a Lookup<F> {
  type Item = (&'a F, &'a (F, F));
  type IntoIter = Iter<'a, F, (F, F)>;

  fn into_iter(self) -> Self::IntoIter {
    self.map_aux.iter()
  }
}

/// c = a + b where a, b is AllocatedNum
pub fn add_allocated_num<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "c"), || {
    a.get_value()
      .zip(b.get_value())
      .map(|(a, b)| a + b)
      .ok_or(SynthesisError::AssignmentMissing)
  })?;
  cs.enforce(
    || "c = a+b",
    |lc| lc + a.get_variable() + b.get_variable(),
    |lc| lc + CS::one(),
    |lc| lc + c.get_variable(),
  );
  Ok(c)
}

/// a < b ? 1 : 0
pub fn less_than<F: PrimeField + PartialOrd, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
  n_bits: usize,
) -> Result<AllocatedNum<F>, SynthesisError> {
  assert!(n_bits < 64, "not support n_bits {n_bits} >= 64");
  let range = alloc_const(cs.namespace(|| "range"), F::from(1u64 << n_bits));
  // diff = (lhs - rhs) + (if lt { range } else { 0 });
  let diff = Num::alloc(cs.namespace(|| "diff"), || {
    a.get_value()
      .zip(b.get_value())
      .zip(range.get_value())
      .map(|((a, b), range)| {
        let lt = a < b;
        (a - b) + (if lt { range } else { F::ZERO })
      })
      .ok_or(SynthesisError::AssignmentMissing)
  })?;
  diff.fits_in_bits(cs.namespace(|| "diff fit in bits"), n_bits)?;
  let diff = diff.as_allocated_num(cs.namespace(|| "diff_alloc_num"))?;
  let lt = AllocatedNum::alloc(cs.namespace(|| "lt"), || {
    a.get_value()
      .zip(b.get_value())
      .map(|(a, b)| F::from(u64::from(a < b)))
      .ok_or(SynthesisError::AssignmentMissing)
  })?;
  cs.enforce(
    || "lt is bit",
    |lc| lc + lt.get_variable(),
    |lc| lc + CS::one() - lt.get_variable(),
    |lc| lc,
  );
  cs.enforce(
    || "lt ⋅ range == diff - lhs + rhs",
    |lc| lc + lt.get_variable(),
    |lc| lc + range.get_variable(),
    |lc| lc + diff.get_variable() - a.get_variable() + b.get_variable(),
  );
  Ok(lt)
}

#[cfg(test)]
mod test {
  use crate::{
    // bellpepper::test_shape_cs::TestShapeCS,
    constants::NUM_CHALLENGE_BITS,
    gadgets::{
      lookup::{LookupTraceBuilder, TableType},
      utils::{alloc_one, alloc_zero, scalar_as_base},
    },
    provider::{poseidon::PoseidonConstantsCircuit, PallasEngine, VestaEngine},
    traits::{Engine, ROConstantsCircuit},
  };
  use ff::Field;

  use super::Lookup;
  use crate::traits::ROTrait;
  use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, ConstraintSystem};

  #[test]
  fn test_lookup_simulation() {
    type E1 = PallasEngine;
    type E2 = VestaEngine;

    let ro_consts: ROConstantsCircuit<E2> = PoseidonConstantsCircuit::default();

    // let mut cs: TestShapeCS<E1> = TestShapeCS::new();
    let initial_table = vec![
      (<E1 as Engine>::Scalar::ZERO, <E1 as Engine>::Scalar::ZERO),
      (<E1 as Engine>::Scalar::ONE, <E1 as Engine>::Scalar::ONE),
    ];
    let mut lookup =
      Lookup::<<E1 as Engine>::Scalar>::new(1024, TableType::ReadWrite, initial_table);
    let mut lookup_trace_builder = LookupTraceBuilder::<E1>::new(&mut lookup);
    let prev_intermediate_gamma = <E1 as Engine>::Scalar::ONE;
    let read_value = lookup_trace_builder.read(<E1 as Engine>::Scalar::ZERO);
    assert_eq!(read_value, <E1 as Engine>::Scalar::ZERO);
    let read_value = lookup_trace_builder.read(<E1 as Engine>::Scalar::ONE);
    assert_eq!(read_value, <E1 as Engine>::Scalar::ONE);
    lookup_trace_builder.write(
      <E1 as Engine>::Scalar::ZERO,
      <E1 as Engine>::Scalar::from(111),
    );
    let read_value = lookup_trace_builder.read(<E1 as Engine>::Scalar::ZERO);
    assert_eq!(read_value, <E1 as Engine>::Scalar::from(111),);

    let (next_intermediate_gamma, _) =
      lookup_trace_builder.snapshot::<E2>(ro_consts.clone(), prev_intermediate_gamma);

    let mut hasher = <E2 as Engine>::RO::new(ro_consts, 1 + 3 * 4);
    hasher.absorb(prev_intermediate_gamma);
    hasher.absorb(<E1 as Engine>::Scalar::ZERO); // addr
    hasher.absorb(<E1 as Engine>::Scalar::ZERO); // value
    hasher.absorb(<E1 as Engine>::Scalar::ZERO); // counter
    hasher.absorb(<E1 as Engine>::Scalar::ONE); // addr
    hasher.absorb(<E1 as Engine>::Scalar::ONE); // value
    hasher.absorb(<E1 as Engine>::Scalar::ZERO); // counter
    hasher.absorb(<E1 as Engine>::Scalar::ZERO); // addr
    hasher.absorb(<E1 as Engine>::Scalar::ZERO); // value
    hasher.absorb(<E1 as Engine>::Scalar::ONE); // counter
    hasher.absorb(<E1 as Engine>::Scalar::ZERO); // addr
    hasher.absorb(<E1 as Engine>::Scalar::from(111)); // value
    hasher.absorb(<E1 as Engine>::Scalar::from(3)); // counter
    let res = hasher.squeeze(NUM_CHALLENGE_BITS);
    assert_eq!(scalar_as_base::<E2>(res), next_intermediate_gamma);
  }

  #[test]
  fn test_read_twice_on_readonly() {
    type E1 = PallasEngine;
    type E2 = VestaEngine;

    let ro_consts: ROConstantsCircuit<E2> = PoseidonConstantsCircuit::default();

    let mut cs = TestConstraintSystem::<<E1 as Engine>::Scalar>::new();
    // let mut cs: TestShapeCS<E1> = TestShapeCS::new();
    let initial_table = vec![
      (
        <E1 as Engine>::Scalar::ZERO,
        <E1 as Engine>::Scalar::from(101),
      ),
      (<E1 as Engine>::Scalar::ONE, <E1 as Engine>::Scalar::ZERO),
    ];
    let mut lookup =
      Lookup::<<E1 as Engine>::Scalar>::new(1024, TableType::ReadOnly, initial_table);
    let mut lookup_trace_builder = LookupTraceBuilder::<E1>::new(&mut lookup);
    let challenges = (
      AllocatedNum::alloc(cs.namespace(|| "alpha"), || {
        Ok(<E1 as Engine>::Scalar::from(5))
      })
      .unwrap(),
      AllocatedNum::alloc(cs.namespace(|| "gamma"), || {
        Ok(<E1 as Engine>::Scalar::from(7))
      })
      .unwrap(),
    );
    let (alpha, gamma) = &challenges;
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let one = alloc_one(cs.namespace(|| "one"));
    let prev_intermediate_gamma = &one;
    let prev_rw_counter = &zero;
    let addr = zero.clone();
    let read_value = lookup_trace_builder.read(addr.get_value().unwrap());
    assert_eq!(read_value, <E1 as Engine>::Scalar::from(101));
    let read_value = lookup_trace_builder.read(addr.get_value().unwrap());
    assert_eq!(read_value, <E1 as Engine>::Scalar::from(101));
    let (_, mut lookup_trace) = lookup_trace_builder.snapshot::<E2>(
      ro_consts.clone(),
      prev_intermediate_gamma.get_value().unwrap(),
    );

    let read_value = lookup_trace
      .read(cs.namespace(|| "read_value1"), &addr)
      .unwrap();
    assert_eq!(
      read_value.get_value(),
      Some(<E1 as Engine>::Scalar::from(101))
    );

    let read_value = lookup_trace
      .read(cs.namespace(|| "read_value2"), &addr)
      .unwrap();
    assert_eq!(
      read_value.get_value(),
      Some(<E1 as Engine>::Scalar::from(101))
    );

    let (prev_W, prev_R) = (&one, &one);
    let (next_R, next_W, next_rw_counter, next_intermediate_gamma) = lookup_trace
      .commit::<E2, _>(
        cs.namespace(|| "commit"),
        ro_consts.clone(),
        prev_intermediate_gamma,
        &challenges,
        prev_W,
        prev_R,
        prev_rw_counter,
      )
      .unwrap();
    assert_eq!(
      next_rw_counter.get_value(),
      Some(<E1 as Engine>::Scalar::from(2))
    );
    // next_R check
    assert_eq!(
      next_R.get_value(),
      prev_R
        .get_value()
        .zip(alpha.get_value())
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|((((prev_R, alpha), gamma), addr), read_value)| prev_R
          + (alpha + (addr + gamma * read_value + gamma * gamma * <E1 as Engine>::Scalar::ZERO))
            .invert()
            .unwrap()
          + (alpha + (addr + gamma * read_value + gamma * gamma * <E1 as Engine>::Scalar::ONE))
            .invert()
            .unwrap())
    );
    // next_W check
    assert_eq!(
      next_W.get_value(),
      prev_W
        .get_value()
        .zip(alpha.get_value())
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|((((prev_W, alpha), gamma), addr), read_value)| {
          prev_W
            + (alpha + (addr + gamma * read_value + gamma * gamma * (<E1 as Engine>::Scalar::ONE)))
              .invert()
              .unwrap()
            + (alpha
              + (addr + gamma * read_value + gamma * gamma * (<E1 as Engine>::Scalar::from(2))))
            .invert()
            .unwrap()
        }),
    );

    let mut hasher = <E2 as Engine>::RO::new(ro_consts, 7);
    hasher.absorb(prev_intermediate_gamma.get_value().unwrap());
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(read_value.get_value().unwrap());
    hasher.absorb(<E1 as Engine>::Scalar::ZERO);
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(read_value.get_value().unwrap());
    hasher.absorb(<E1 as Engine>::Scalar::ONE);
    let res = hasher.squeeze(NUM_CHALLENGE_BITS);
    assert_eq!(
      scalar_as_base::<E2>(res),
      next_intermediate_gamma.get_value().unwrap()
    );
  }

  #[test]
  fn test_write_read_on_rwlookup() {
    type E1 = PallasEngine;
    type E2 = VestaEngine;

    let ro_consts: ROConstantsCircuit<E2> = PoseidonConstantsCircuit::default();

    let mut cs = TestConstraintSystem::<<E1 as Engine>::Scalar>::new();
    // let mut cs: TestShapeCS<E1> = TestShapeCS::new();
    let initial_table = vec![
      (<E1 as Engine>::Scalar::ZERO, <E1 as Engine>::Scalar::ZERO),
      (<E1 as Engine>::Scalar::ONE, <E1 as Engine>::Scalar::ZERO),
    ];
    let mut lookup =
      Lookup::<<E1 as Engine>::Scalar>::new(1024, TableType::ReadWrite, initial_table);
    let mut lookup_trace_builder = LookupTraceBuilder::<E1>::new(&mut lookup);
    let challenges = (
      AllocatedNum::alloc(cs.namespace(|| "alpha"), || {
        Ok(<E1 as Engine>::Scalar::from(5))
      })
      .unwrap(),
      AllocatedNum::alloc(cs.namespace(|| "gamma"), || {
        Ok(<E1 as Engine>::Scalar::from(7))
      })
      .unwrap(),
    );
    let (alpha, gamma) = &challenges;
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let one = alloc_one(cs.namespace(|| "one"));
    let prev_intermediate_gamma = &one;
    let prev_rw_counter = &zero;
    let addr = zero.clone();
    let write_value_1 = AllocatedNum::alloc(cs.namespace(|| "write value 1"), || {
      Ok(<E1 as Engine>::Scalar::from(101))
    })
    .unwrap();
    lookup_trace_builder.write(
      addr.get_value().unwrap(),
      write_value_1.get_value().unwrap(),
    );
    let read_value = lookup_trace_builder.read(addr.get_value().unwrap());
    assert_eq!(read_value, <E1 as Engine>::Scalar::from(101));
    let (_, mut lookup_trace) = lookup_trace_builder.snapshot::<E2>(
      ro_consts.clone(),
      prev_intermediate_gamma.get_value().unwrap(),
    );
    lookup_trace
      .write(cs.namespace(|| "write_value 1"), &addr, &write_value_1)
      .unwrap();
    let read_value = lookup_trace
      .read(cs.namespace(|| "read_value 1"), &addr)
      .unwrap();
    assert_eq!(
      read_value.get_value(),
      Some(<E1 as Engine>::Scalar::from(101))
    );

    let (prev_W, prev_R) = (&one, &one);
    let (next_R, next_W, next_rw_counter, next_intermediate_gamma) = lookup_trace
      .commit::<E2, _>(
        cs.namespace(|| "commit"),
        ro_consts.clone(),
        prev_intermediate_gamma,
        &challenges,
        prev_W,
        prev_R,
        prev_rw_counter,
      )
      .unwrap();
    assert_eq!(
      next_rw_counter.get_value(),
      Some(<E1 as Engine>::Scalar::from(2))
    );
    // next_R check
    assert_eq!(
      next_R.get_value(),
      prev_R
        .get_value()
        .zip(alpha.get_value())
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|((((prev_R, alpha), gamma), addr), read_value)| prev_R
          + (alpha
            + (addr
              + gamma * <E1 as Engine>::Scalar::ZERO
              + gamma * gamma * <E1 as Engine>::Scalar::ZERO))
            .invert()
            .unwrap()
          + (alpha + (addr + gamma * read_value + gamma * gamma * <E1 as Engine>::Scalar::ONE))
            .invert()
            .unwrap())
    );
    // next_W check
    assert_eq!(
      next_W.get_value(),
      prev_W
        .get_value()
        .zip(alpha.get_value())
        .zip(gamma.get_value())
        .zip(addr.get_value())
        .zip(read_value.get_value())
        .map(|((((prev_W, alpha), gamma), addr), read_value)| {
          prev_W
            + (alpha + (addr + gamma * read_value + gamma * gamma * (<E1 as Engine>::Scalar::ONE)))
              .invert()
              .unwrap()
            + (alpha
              + (addr + gamma * read_value + gamma * gamma * (<E1 as Engine>::Scalar::from(2))))
            .invert()
            .unwrap()
        }),
    );

    let mut hasher = <E2 as Engine>::RO::new(ro_consts, 7);
    hasher.absorb(prev_intermediate_gamma.get_value().unwrap());
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(<E1 as Engine>::Scalar::ZERO);
    hasher.absorb(<E1 as Engine>::Scalar::ZERO);
    hasher.absorb(addr.get_value().unwrap());
    hasher.absorb(read_value.get_value().unwrap());
    hasher.absorb(<E1 as Engine>::Scalar::ONE);
    let res = hasher.squeeze(NUM_CHALLENGE_BITS);
    assert_eq!(
      scalar_as_base::<E2>(res),
      next_intermediate_gamma.get_value().unwrap()
    );
    // TODO check rics is_sat
    // let (_, _) = cs.r1cs_shape_with_commitmentkey();
    // let (U1, W1) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();

    // // Make sure that the first instance is satisfiable
    // assert!(shape.is_sat(&ck, &U1, &W1).is_ok());
  }
}
