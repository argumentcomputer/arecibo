//! There are two augmented circuits: the primary and the secondary.
//! Each of them is over a curve in a 2-cycle of elliptic curves.
//! We have two running instances. Each circuit takes as input 2 hashes: one for each
//! of the running instances. Each of these hashes is H(params = H(shape, ck), i, z0, zi, U).
//! Each circuit folds the last invocation of the other into the running instance

use abomonation_derive::Abomonation;
use bellpepper::gadgets::Assignment;
use bellpepper_core::{
  boolean::{AllocatedBit, Boolean},
  num::AllocatedNum,
  ConstraintSystem, SynthesisError,
};
use ff::{Field, PrimeField};
use itertools::chain;
use serde::{Deserialize, Serialize};

use crate::bellpepper::r1cs::NovaWitness;
use crate::bellpepper::solver::SatisfyingAssignment;
use crate::errors::NovaError;
use crate::nifs::NIFS;
use crate::r1cs::R1CSShape;
use crate::traits::ROConstants;
use crate::{
  constants::{NIO_NOVA_FOLD, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS},
  gadgets::{
    ecc::AllocatedPoint,
    r1cs::{AllocatedR1CSInstance, AllocatedRelaxedR1CSInstance},
    utils::{
      alloc_num_equals, alloc_scalar_as_base, alloc_zero, conditionally_select_vec, le_bits_to_num,
    },
  },
  r1cs::{R1CSInstance, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{
    circuit::StepCircuit, commitment::CommitmentTrait, Engine, ROCircuitTrait, ROConstantsCircuit,
  },
  Commitment, CommitmentKey,
};

struct SelfProvingKey<E: Engine> {
  pp: E::Scalar,
  shape: R1CSShape<E>,
  nivc: Vec<IVCProvingKey<E>>,
  ck: CommitmentKey<E>,
  ro_consts: ROConstants<E>,
}

struct IVCProvingKey<E: Engine> {
  pp: E::Scalar,
  shape: R1CSShape<E>,
}

struct RelaxedR1CSAccumulator<E: Engine> {
  instance: RelaxedR1CSInstance<E>,
  witness: RelaxedR1CSWitness<E>,
}

impl<E: Engine> RelaxedR1CSAccumulator<E> {
  fn default(shape: &R1CSShape<E>) -> Self {
    let witness = RelaxedR1CSWitness::default(shape);
    let instance = RelaxedR1CSInstance::default(shape);
    Self { instance, witness }
  }
}

#[derive(Clone)]
struct FoldProof<E: Engine> {
  witness: Commitment<E>,
  proof: Commitment<E>,
  // TODO: add CycleFold proof
}

#[derive(Clone)]
struct NIVCState<F: PrimeField> {
  pc: usize,
  z: Vec<F>,
}
//
// #[derive(Clone)]
// struct NIVCIO<F: PrimeField> {
//   init: NIVCState<F>,
//   curr: NIVCState<F>,
// }

impl<F: PrimeField> NIVCState<F> {
  pub fn io_vec(input: &Self, output: &Self) -> Vec<F> {
    let NIVCState { pc: pc_in, z: z_in } = input;
    let NIVCState {
      pc: pc_out,
      z: z_out,
    } = output;
    chain!(
      [F::from(*pc_in as u64)],
      z_in.iter().cloned(),
      [F::from(*pc_out as u64)],
      z_out.iter().cloned()
    )
    .collect()
  }
}

#[derive(Clone)]
struct SelfProof<E: Engine> {
  witness: R1CSWitness<E>,
  instance: Commitment<E>,
}

#[derive(Clone)]
struct NIVCProof<E: Engine> {
  output: NIVCState<E::Scalar>,
  witness: R1CSWitness<E>,
  instance: Commitment<E>,
}

pub struct SelfState<E: Engine> {
  pk: SelfProvingKey<E>,

  self_acc_curr: RelaxedR1CSAccumulator<E>,
  nivc_acc_curr: Vec<Option<RelaxedR1CSAccumulator<E>>>,

  nivc_state_init: NIVCState<E::Scalar>,
  nivc_state_curr: NIVCState<E::Scalar>,

  self_io_hash_prev: E::Scalar,
  self_proof_curr: SelfProof<E>,
}

impl<E: Engine> SelfState<E> {
  fn fold_proofs(self, nivc_proofs: Vec<NIVCProof<E>>) -> Self {
    // Get hash of the current state
    let self_io_hash_curr: E::Scalar = self.io_hash();

    // Destructure current state
    let Self {
      pk,
      self_acc_curr,
      nivc_acc_curr,
      nivc_state_init,
      nivc_state_curr,
      self_io_hash_prev,
      self_proof_curr,
    } = self;

    // Keep track of accumulator instances to be given to the recursive verifier circuit
    let self_acc_instance_curr = self_acc_curr.instance.clone();
    let nivc_acc_instance_curr = nivc_acc_curr
      .iter()
      .map(|acc| acc.as_ref().map(|acc| acc.instance.clone()))
      .collect();

    // Fold the proof of the current state into the accumulator for `Self`
    // Generate a proof adding the witness of the current accumulator
    let (self_acc_next, self_fold_proof_next): (RelaxedR1CSAccumulator<E>, FoldProof<E>) =
      Self::fold_self(
        &pk,
        self_acc_curr,
        self_io_hash_prev,
        self_io_hash_curr,
        self_proof_curr,
      );

    // Fold a list of `m` proofs into the current NIVC accumulator.
    // Generate the outputs of each NIVC circuit, and a folding proof
    let (nivc_acc_next, nivc_state_trace, nivc_folding_proofs): (
      Vec<Option<RelaxedR1CSAccumulator<E>>>,
      Vec<NIVCState<E::Scalar>>,
      Vec<FoldProof<E>>,
    ) = Self::fold_many_nivc(&pk, nivc_acc_curr, nivc_state_curr.clone(), nivc_proofs);

    let nivc_state_next = nivc_state_trace.last().cloned().unwrap();

    // Initialize inputs for the circuit verifying this state transition.
    let self_circuit = StateTransitionCircuit {
      pp_self: pk.pp,
      pp_nivc: pk.nivc.iter().map(|pk_nivc| pk_nivc.pp).collect(),
      self_acc_instance_curr,
      nivc_acc_instance_curr,
      self_io_hash_prev,
      self_fold_proof_next,
      nivc_state_init: nivc_state_init.clone(),
      nivc_state_curr,

      nivc_state_trace,
      nivc_folding_proofs,
    };

    let self_proof_next: SelfProof<E> = Self::prove_transition(&pk, self_circuit);

    Self {
      pk,
      self_acc_curr: self_acc_next,
      nivc_acc_curr: nivc_acc_next,
      nivc_state_init,
      nivc_state_curr: nivc_state_next,
      self_io_hash_prev: self_io_hash_curr,
      self_proof_curr: self_proof_next,
    }
  }

  /// Compute a collision-resistant hash of the circuit's state.
  fn io_hash(&self) -> E::Scalar {
    todo!()
  }

  /// Fold the proof for the previous state transition, producing an accumulator for the current state,
  /// and a proof to be consumed by the verifier.
  fn fold_self(
    pk: &SelfProvingKey<E>,
    acc_curr: RelaxedR1CSAccumulator<E>,
    hash_prev: E::Scalar,
    hash_curr: E::Scalar,
    proof_curr: SelfProof<E>,
  ) -> (RelaxedR1CSAccumulator<E>, FoldProof<E>) {
    let SelfProof {
      instance: proof_witness_commitment_curr,
      witness: proof_witness_curr,
    } = proof_curr;
    let RelaxedR1CSAccumulator {
      instance: acc_instance_curr,
      witness: acc_witness_curr,
    } = acc_curr;

    let proof_instance_curr = R1CSInstance {
      comm_W: proof_witness_commitment_curr,
      X: vec![hash_prev, hash_curr],
    };

    let (fold_proof_T, (acc_instance_next, acc_witness_next)) = NIFS::prove(
      &pk.ck,
      &pk.ro_consts,
      &pk.pp,
      &pk.shape,
      &acc_instance_curr,
      &acc_witness_curr,
      &proof_instance_curr,
      &proof_witness_curr,
    )
    .unwrap();

    let fold_proof = FoldProof {
      witness: proof_witness_commitment_curr,
      proof: Commitment::<E>::decompress(&fold_proof_T.comm_T).unwrap(),
    };

    let acc_next = RelaxedR1CSAccumulator {
      instance: acc_instance_next,
      witness: acc_witness_next,
    };

    (acc_next, fold_proof)
  }

  /// Given a list NIVC accumulators `accs_init` that resulted in the computation of `state_init`,
  /// and a list of NIVC proofs of `m` sequential iterations, this function folds all the proofs into an `accs_init`,
  /// and returns proofs of this folding.   
  fn fold_many_nivc(
    pk: &SelfProvingKey<E>,
    accs_init: Vec<Option<RelaxedR1CSAccumulator<E>>>,
    state_init: NIVCState<E::Scalar>,
    nivc_proofs: Vec<NIVCProof<E>>,
  ) -> (
    Vec<Option<RelaxedR1CSAccumulator<E>>>,
    Vec<NIVCState<<E as Engine>::Scalar>>,
    Vec<FoldProof<E>>,
  ) {
    let num_iters = nivc_proofs.len();

    let mut fold_proofs = Vec::with_capacity(num_iters);

    let (state_trace, accs_next) = nivc_proofs.into_iter().fold(
      (vec![state_init], accs_init),
      |(mut state_trace, accs_curr), proof| {
        let state_curr = state_trace.last().unwrap();
        let (accs_next, state_next, fold_proof_next) =
          Self::fold_nivc(pk, state_curr.clone(), accs_curr, proof);

        state_trace.push(state_next);
        fold_proofs.push(fold_proof_next);

        (state_trace, accs_next)
      },
    );
    (accs_next, state_trace, fold_proofs)
  }

  fn fold_nivc(
    pk: &SelfProvingKey<E>,
    state_curr: NIVCState<E::Scalar>,
    mut accs: Vec<Option<RelaxedR1CSAccumulator<E>>>,
    proof: NIVCProof<E>,
  ) -> (
    Vec<Option<RelaxedR1CSAccumulator<E>>>,
    NIVCState<E::Scalar>,
    FoldProof<E>,
  ) {
    // Unpack the witness of the circuit computing
    //   `(pc_next, z_next) = F_{pc_curr}(z_curr)`
    let NIVCProof {
      output: state_next,
      witness: proof_witness_next,
      instance: proof_witness_commitment_next,
    } = proof;

    // Get the `io = {pc_curr, z_curr, pc_next, z_next}`, and the proving key for `F_{pc_curr}`

    let pc_curr = state_curr.pc;
    let pk_curr = &pk.nivc[pc_curr];

    // let pk_curr = pk.pp_nivc[pc_curr];

    // Convert witness commitment and io into Nova instance
    let proof_instance_next = R1CSInstance {
      comm_W: proof_witness_commitment_next,
      X: NIVCState::io_vec(&state_curr, &state_next),
    };

    // Load the existing accumulator for `pc_curr`, or load a default one.
    let acc_curr =
      accs[pc_curr].get_or_insert_with(|| RelaxedR1CSAccumulator::default(&pk_curr.shape));

    let RelaxedR1CSAccumulator {
      instance: acc_instance_curr,
      witness: acc_witness_curr,
    } = acc_curr;

    // Fold the proof for io into `acc_curr`, along with a folding proof for the verifier.
    let (fold_proof_T, (acc_instance_next, acc_witness_next)) = NIFS::prove(
      &pk.ck,
      &pk.ro_consts,
      &pk_curr.pp,
      &pk_curr.shape,
      &acc_instance_curr,
      &acc_witness_curr,
      &proof_instance_next,
      &proof_witness_next,
    )
    .unwrap();

    // Update the accumulator at the index of the folded NIVC circuit
    accs[pc_curr] = Some(RelaxedR1CSAccumulator {
      instance: acc_instance_next,
      witness: acc_witness_next,
    });

    let fold_proof_next = FoldProof {
      witness: proof_witness_commitment_next,
      proof: Commitment::<E>::decompress(&fold_proof_T.comm_T).unwrap(),
    };

    // Return the output state, and a folding proof of the folding
    (accs, state_next, fold_proof_next)
  }

  /// Create a proof for the circuit verifying the current state transition.
  fn prove_transition(pk: &SelfProvingKey<E>, circuit: StateTransitionCircuit<E>) -> SelfProof<E> {
    let mut cs = SatisfyingAssignment::<E>::with_capacity(pk.shape.num_io + 1, pk.shape.num_vars);

    circuit.synthesize(&mut cs).unwrap();

    let (instance, witness) = cs
      .r1cs_instance_and_witness(&pk.shape, &pk.ck)
      .map_err(|_e| NovaError::UnSat)
      .expect("Nova error unsat");

    SelfProof {
      witness,
      instance: instance.comm_W,
    }
  }
}

/// Given the state transition over the io
///   `self_state = (vk_self, vk_nivc, self_acc, nivc_acc, nivc_io)`
/// self_io = {self_state_curr, self_state_next}
///
///
#[derive(Clone)]
struct StateTransitionCircuit<E: Engine> {
  pp_self: E::Scalar,
  pp_nivc: Vec<E::Scalar>,

  self_acc_instance_curr: RelaxedR1CSInstance<E>,
  nivc_acc_instance_curr: Vec<Option<RelaxedR1CSInstance<E>>>,
  self_io_hash_prev: E::Scalar,
  self_fold_proof_next: FoldProof<E>,

  nivc_state_init: NIVCState<E::Scalar>,
  nivc_state_curr: NIVCState<E::Scalar>,

  nivc_state_trace: Vec<NIVCState<E::Scalar>>,
  nivc_folding_proofs: Vec<FoldProof<E>>,
}

impl<E: Engine> StateTransitionCircuit<E> {
  fn synthesize<CS: ConstraintSystem<E::Scalar>>(
    &self,
    _cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    todo!()
  }
}

impl<E: Engine> StateTransitionCircuit<E> {}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
pub struct NovaAugmentedCircuitParams {
  limb_width: usize,
  n_limbs: usize,
  is_primary_circuit: bool, // A boolean indicating if this is the primary circuit
}

impl NovaAugmentedCircuitParams {
  pub const fn new(limb_width: usize, n_limbs: usize, is_primary_circuit: bool) -> Self {
    Self {
      limb_width,
      n_limbs,
      is_primary_circuit,
    }
  }
}

#[derive(Debug, Serialize)]
#[serde(bound = "")]
pub struct NovaAugmentedCircuitInputs<E: Engine> {
  params: E::Scalar,
  i: E::Base,
  z0: Vec<E::Base>,
  zi: Option<Vec<E::Base>>,
  U: Option<RelaxedR1CSInstance<E>>,
  u: Option<R1CSInstance<E>>,
  T: Option<Commitment<E>>,
}

impl<E: Engine> NovaAugmentedCircuitInputs<E> {
  /// Create new inputs/witness for the verification circuit
  pub fn new(
    params: E::Scalar,
    i: E::Base,
    z0: Vec<E::Base>,
    zi: Option<Vec<E::Base>>,
    U: Option<RelaxedR1CSInstance<E>>,
    u: Option<R1CSInstance<E>>,
    T: Option<Commitment<E>>,
  ) -> Self {
    Self {
      params,
      i,
      z0,
      zi,
      U,
      u,
      T,
    }
  }
}

/// The augmented circuit F' in Nova that includes a step circuit F
/// and the circuit for the verifier in Nova's non-interactive folding scheme
pub struct NovaAugmentedCircuit<'a, E: Engine, SC: StepCircuit<E::Base>> {
  params: &'a NovaAugmentedCircuitParams,
  ro_consts: ROConstantsCircuit<E>,
  inputs: Option<NovaAugmentedCircuitInputs<E>>,
  step_circuit: &'a SC, // The function that is applied for each step
}

impl<'a, E: Engine, SC: StepCircuit<E::Base>> NovaAugmentedCircuit<'a, E, SC> {
  /// Create a new verification circuit for the input relaxed r1cs instances
  pub const fn new(
    params: &'a NovaAugmentedCircuitParams,
    inputs: Option<NovaAugmentedCircuitInputs<E>>,
    step_circuit: &'a SC,
    ro_consts: ROConstantsCircuit<E>,
  ) -> Self {
    Self {
      params,
      inputs,
      step_circuit,
      ro_consts,
    }
  }

  /// Allocate all witnesses and return
  fn alloc_witness<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
    arity: usize,
  ) -> Result<
    (
      AllocatedNum<E::Base>,
      AllocatedNum<E::Base>,
      Vec<AllocatedNum<E::Base>>,
      Vec<AllocatedNum<E::Base>>,
      AllocatedRelaxedR1CSInstance<E, NIO_NOVA_FOLD>,
      AllocatedR1CSInstance<E, NIO_NOVA_FOLD>,
      AllocatedPoint<E::GE>,
    ),
    SynthesisError,
  > {
    // Allocate the params
    let params = alloc_scalar_as_base::<E, _>(
      cs.namespace(|| "params"),
      self.inputs.as_ref().map(|inputs| inputs.params),
    )?;

    // Allocate i
    let i = AllocatedNum::alloc(cs.namespace(|| "i"), || Ok(self.inputs.get()?.i))?;

    // Allocate z0
    let z_0 = (0..arity)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("z0_{i}")), || {
          Ok(self.inputs.get()?.z0[i])
        })
      })
      .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

    // Allocate zi. If inputs.zi is not provided (base case) allocate default value 0
    let zero = vec![E::Base::ZERO; arity];
    let z_i = (0..arity)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
          Ok(self.inputs.get()?.zi.as_ref().unwrap_or(&zero)[i])
        })
      })
      .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

    // Allocate the running instance
    let U: AllocatedRelaxedR1CSInstance<E, NIO_NOVA_FOLD> = AllocatedRelaxedR1CSInstance::alloc(
      cs.namespace(|| "Allocate U"),
      self.inputs.as_ref().and_then(|inputs| inputs.U.as_ref()),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    // Allocate the instance to be folded in
    let u = AllocatedR1CSInstance::alloc(
      cs.namespace(|| "allocate instance u to fold"),
      self.inputs.as_ref().and_then(|inputs| inputs.u.as_ref()),
    )?;

    // Allocate T
    let T = AllocatedPoint::alloc(
      cs.namespace(|| "allocate T"),
      self
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.T.map(|T| T.to_coordinates())),
    )?;
    T.check_on_curve(cs.namespace(|| "check T on curve"))?;

    Ok((params, i, z_0, z_i, U, u, T))
  }

  /// Synthesizes base case and returns the new relaxed `R1CSInstance`
  fn synthesize_base_case<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
    u: AllocatedR1CSInstance<E, NIO_NOVA_FOLD>,
  ) -> Result<AllocatedRelaxedR1CSInstance<E, NIO_NOVA_FOLD>, SynthesisError> {
    let U_default: AllocatedRelaxedR1CSInstance<E, NIO_NOVA_FOLD> =
      if self.params.is_primary_circuit {
        // The primary circuit just returns the default R1CS instance
        AllocatedRelaxedR1CSInstance::default(
          cs.namespace(|| "Allocate U_default"),
          self.params.limb_width,
          self.params.n_limbs,
        )?
      } else {
        // The secondary circuit returns the incoming R1CS instance
        AllocatedRelaxedR1CSInstance::from_r1cs_instance(
          cs.namespace(|| "Allocate U_default"),
          u,
          self.params.limb_width,
          self.params.n_limbs,
        )?
      };
    Ok(U_default)
  }

  /// Synthesizes non base case and returns the new relaxed `R1CSInstance`
  /// And a boolean indicating if all checks pass
  fn synthesize_non_base_case<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<E::Base>,
    i: &AllocatedNum<E::Base>,
    z_0: &[AllocatedNum<E::Base>],
    z_i: &[AllocatedNum<E::Base>],
    U: &AllocatedRelaxedR1CSInstance<E, NIO_NOVA_FOLD>,
    u: &AllocatedR1CSInstance<E, NIO_NOVA_FOLD>,
    T: &AllocatedPoint<E::GE>,
    arity: usize,
  ) -> Result<(AllocatedRelaxedR1CSInstance<E, NIO_NOVA_FOLD>, AllocatedBit), SynthesisError> {
    // Check that u.x[0] = Hash(params, U, i, z0, zi)
    let mut ro = E::ROCircuit::new(
      self.ro_consts.clone(),
      NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity,
    );
    ro.absorb(params);
    ro.absorb(i);
    for e in z_0 {
      ro.absorb(e);
    }
    for e in z_i {
      ro.absorb(e);
    }
    U.absorb_in_ro(cs.namespace(|| "absorb U"), &mut ro)?;

    let hash_bits = ro.squeeze(cs.namespace(|| "Input hash"), NUM_HASH_BITS)?;
    let hash = le_bits_to_num(cs.namespace(|| "bits to hash"), &hash_bits)?;
    let check_pass = alloc_num_equals(
      cs.namespace(|| "check consistency of u.X[0] with H(params, U, i, z0, zi)"),
      &u.X[0],
      &hash,
    )?;

    // Run NIFS Verifier
    let U_fold = U.fold_with_r1cs(
      cs.namespace(|| "compute fold of U and u"),
      params,
      u,
      T,
      self.ro_consts.clone(),
      self.params.limb_width,
      self.params.n_limbs,
    )?;

    Ok((U_fold, check_pass))
  }
}

impl<'a, E: Engine, SC: StepCircuit<E::Base>> NovaAugmentedCircuit<'a, E, SC> {
  /// synthesize circuit giving constraint system
  pub fn synthesize<CS: ConstraintSystem<<E as Engine>::Base>>(
    self,
    cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<E::Base>>, SynthesisError> {
    let arity = self.step_circuit.arity();

    // Allocate all witnesses
    let (params, i, z_0, z_i, U, u, T) =
      self.alloc_witness(cs.namespace(|| "allocate the circuit witness"), arity)?;

    // Compute variable indicating if this is the base case
    let zero = alloc_zero(cs.namespace(|| "zero"));
    let is_base_case = alloc_num_equals(cs.namespace(|| "Check if base case"), &i.clone(), &zero)?;

    // Synthesize the circuit for the base case and get the new running instance
    let Unew_base = self.synthesize_base_case(cs.namespace(|| "base case"), u.clone())?;

    // Synthesize the circuit for the non-base case and get the new running
    // instance along with a boolean indicating if all checks have passed
    let (Unew_non_base, check_non_base_pass) = self.synthesize_non_base_case(
      cs.namespace(|| "synthesize non base case"),
      &params,
      &i,
      &z_0,
      &z_i,
      &U,
      &u,
      &T,
      arity,
    )?;

    // Either check_non_base_pass=true or we are in the base case
    let should_be_false = AllocatedBit::nor(
      cs.namespace(|| "check_non_base_pass nor base_case"),
      &check_non_base_pass,
      &is_base_case,
    )?;
    cs.enforce(
      || "check_non_base_pass nor base_case = false",
      |lc| lc + should_be_false.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );

    // Compute the U_new
    let Unew = Unew_base.conditionally_select(
      cs.namespace(|| "compute U_new"),
      &Unew_non_base,
      &Boolean::from(is_base_case.clone()),
    )?;

    // Compute i + 1
    let i_new = AllocatedNum::alloc(cs.namespace(|| "i + 1"), || {
      Ok(*i.get_value().get()? + E::Base::ONE)
    })?;
    cs.enforce(
      || "check i + 1",
      |lc| lc,
      |lc| lc,
      |lc| lc + i_new.get_variable() - CS::one() - i.get_variable(),
    );

    // Compute z_{i+1}
    let z_input = conditionally_select_vec(
      cs.namespace(|| "select input to F"),
      &z_0,
      &z_i,
      &Boolean::from(is_base_case),
    )?;

    let z_next = self
      .step_circuit
      .synthesize(&mut cs.namespace(|| "F"), &z_input)?;

    if z_next.len() != arity {
      return Err(SynthesisError::IncompatibleLengthVector(
        "z_next".to_string(),
      ));
    }

    // Compute the new hash H(params, Unew, i+1, z0, z_{i+1})
    let mut ro = E::ROCircuit::new(self.ro_consts, NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * arity);
    ro.absorb(&params);
    ro.absorb(&i_new);
    for e in &z_0 {
      ro.absorb(e);
    }
    for e in &z_next {
      ro.absorb(e);
    }
    Unew.absorb_in_ro(cs.namespace(|| "absorb U_new"), &mut ro)?;
    let hash_bits = ro.squeeze(cs.namespace(|| "output hash bits"), NUM_HASH_BITS)?;
    let hash = le_bits_to_num(cs.namespace(|| "convert hash to num"), &hash_bits)?;

    // Outputs the computed hash and u.X[1] that corresponds to the hash of the other circuit
    u.X[1].inputize(cs.namespace(|| "Output unmodified hash of the other circuit"))?;
    hash.inputize(cs.namespace(|| "output new hash of this circuit"))?;

    Ok(z_next)
  }
}

#[cfg(test)]
mod tests {
  use expect_test::{expect, Expect};

  use crate::{
    bellpepper::{
      r1cs::{NovaShape, NovaWitness},
      solver::SatisfyingAssignment,
      test_shape_cs::TestShapeCS,
    },
    constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
    gadgets::utils::scalar_as_base,
    provider::{
      poseidon::PoseidonConstantsCircuit, Bn256EngineKZG, GrumpkinEngine, PallasEngine,
      Secp256k1Engine, Secq256k1Engine, VestaEngine,
    },
    traits::{circuit::TrivialCircuit, snark::default_ck_hint, CurveCycleEquipped, Dual},
  };

  use super::*;

  // In the following we use 1 to refer to the primary, and 2 to refer to the secondary circuit
  fn test_recursive_circuit_with<E1>(
    primary_params: &NovaAugmentedCircuitParams,
    secondary_params: &NovaAugmentedCircuitParams,
    ro_consts1: ROConstantsCircuit<Dual<E1>>,
    ro_consts2: ROConstantsCircuit<E1>,
    expected_num_constraints_primary: &Expect,
    expected_num_constraints_secondary: &Expect,
  ) where
    E1: CurveCycleEquipped,
  {
    let tc1 = TrivialCircuit::default();
    // Initialize the shape and ck for the primary
    let circuit1: NovaAugmentedCircuit<'_, Dual<E1>, TrivialCircuit<<Dual<E1> as Engine>::Base>> =
      NovaAugmentedCircuit::new(primary_params, None, &tc1, ro_consts1.clone());
    let mut cs: TestShapeCS<E1> = TestShapeCS::new();
    let _ = circuit1.synthesize(&mut cs);
    let (shape1, ck1) = cs.r1cs_shape_and_key(&*default_ck_hint());

    expected_num_constraints_primary.assert_eq(&cs.num_constraints().to_string());

    let tc2 = TrivialCircuit::default();
    // Initialize the shape and ck for the secondary
    let circuit2: NovaAugmentedCircuit<'_, E1, TrivialCircuit<<E1 as Engine>::Base>> =
      NovaAugmentedCircuit::new(secondary_params, None, &tc2, ro_consts2.clone());
    let mut cs: TestShapeCS<Dual<E1>> = TestShapeCS::new();
    let _ = circuit2.synthesize(&mut cs);
    let (shape2, ck2) = cs.r1cs_shape_and_key(&*default_ck_hint());

    expected_num_constraints_secondary.assert_eq(&cs.num_constraints().to_string());

    // Execute the base case for the primary
    let zero1 = <<Dual<E1> as Engine>::Base as Field>::ZERO;
    let mut cs1 = SatisfyingAssignment::<E1>::new();
    let inputs1: NovaAugmentedCircuitInputs<Dual<E1>> = NovaAugmentedCircuitInputs::new(
      scalar_as_base::<E1>(zero1), // pass zero for testing
      zero1,
      vec![zero1],
      None,
      None,
      None,
      None,
    );
    let circuit1: NovaAugmentedCircuit<'_, Dual<E1>, TrivialCircuit<<Dual<E1> as Engine>::Base>> =
      NovaAugmentedCircuit::new(primary_params, Some(inputs1), &tc1, ro_consts1);
    let _ = circuit1.synthesize(&mut cs1);
    let (inst1, witness1) = cs1.r1cs_instance_and_witness(&shape1, &ck1).unwrap();
    // Make sure that this is satisfiable
    shape1.is_sat(&ck1, &inst1, &witness1).unwrap();

    // Execute the base case for the secondary
    let zero2 = <<E1 as Engine>::Base as Field>::ZERO;
    let mut cs2 = SatisfyingAssignment::<Dual<E1>>::new();
    let inputs2: NovaAugmentedCircuitInputs<E1> = NovaAugmentedCircuitInputs::new(
      scalar_as_base::<Dual<E1>>(zero2), // pass zero for testing
      zero2,
      vec![zero2],
      None,
      None,
      Some(inst1),
      None,
    );
    let circuit2: NovaAugmentedCircuit<'_, E1, TrivialCircuit<<E1 as Engine>::Base>> =
      NovaAugmentedCircuit::new(secondary_params, Some(inputs2), &tc2, ro_consts2);
    let _ = circuit2.synthesize(&mut cs2);
    let (inst2, witness2) = cs2.r1cs_instance_and_witness(&shape2, &ck2).unwrap();
    // Make sure that it is satisfiable
    shape2.is_sat(&ck2, &inst2, &witness2).unwrap();
  }

  #[test]
  fn test_recursive_circuit_pasta() {
    // this test checks against values that must be replicated in benchmarks if changed here
    let params1 = NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let params2 = NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);
    let ro_consts1: ROConstantsCircuit<VestaEngine> = PoseidonConstantsCircuit::default();
    let ro_consts2: ROConstantsCircuit<PallasEngine> = PoseidonConstantsCircuit::default();

    test_recursive_circuit_with::<PallasEngine>(
      &params1,
      &params2,
      ro_consts1,
      ro_consts2,
      &expect!["9817"],
      &expect!["10349"],
    );
  }

  #[test]
  fn test_recursive_circuit_bn256_grumpkin() {
    let params1 = NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let params2 = NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);
    let ro_consts1: ROConstantsCircuit<GrumpkinEngine> = PoseidonConstantsCircuit::default();
    let ro_consts2: ROConstantsCircuit<Bn256EngineKZG> = PoseidonConstantsCircuit::default();

    test_recursive_circuit_with::<Bn256EngineKZG>(
      &params1,
      &params2,
      ro_consts1,
      ro_consts2,
      &expect!["9985"],
      &expect!["10538"],
    );
  }

  #[test]
  fn test_recursive_circuit_secpq() {
    let params1 = NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let params2 = NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);
    let ro_consts1: ROConstantsCircuit<Secq256k1Engine> = PoseidonConstantsCircuit::default();
    let ro_consts2: ROConstantsCircuit<Secp256k1Engine> = PoseidonConstantsCircuit::default();

    test_recursive_circuit_with::<Secp256k1Engine>(
      &params1,
      &params2,
      ro_consts1,
      ro_consts2,
      &expect!["10264"],
      &expect!["10961"],
    );
  }
}
