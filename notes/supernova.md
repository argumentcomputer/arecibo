# SuperNova Description

This document explains from a high-level how the SuperNova protocol was implemented in Arecibo. We aim to provide a mathematical description of the protocol, as it is implemented, and highlight the differences with the original paper.

The original paper does not provide a description of the augmentation circuit in the case that cycles of curves are used to minimize the recursive overhead from non-native scalar multiplications. The implementation assumes that all computation will be done on the primary curve, and the cycle curve is only used for verification (this limit is hard-coded).

Let $F_0, \ldots, F\_{\ell-1}$ be folding circuits with the same arity $a$. These circuits implement the `circuit_supernova::StepCircuit` trait, where the main differences with the existing `StepCircuit` trait are
- The circuit $F_j$ provides its `circuit_index` $j$
- The `synthesize` function upon input $z_i$ returns the next `program_counter` $\mathsf{pc}\_{i+1}$ alongside the output $z\_{i+1}$. It also accepts the (optional) input program counter $\mathsf{pc}_i$, which can be `None` when $\ell=1$. During circuit synthesis, a constraint enforces $\mathsf{pc}_i \equiv j$. In contrast to the paper, the _predicate_ function $\varphi$ is built into the circuit itself. In other words, we have the signature $(\mathsf{pc}\_{i+1}, z\_{i+1}) \gets F\_{j}(\mathsf{pc}\_{i}, z\_{i})$.

The goal is to efficiently prove the following computation:
```
pc_i = pc_0
z_i = z_0
for i in 0..num_steps
	(pc_i, z_i) = F_{pc_i}(z_i)
return z_i
```

## Prover state 

The prover needs to store data about the previous function iteration. It is defined by the `supernova::RecursiveSNARK` struct. It contains:
- $i$: the number of iterations performed. Note that the `new` constructor actually performs the first iteration, and the first call to `prove_step` simply sets the counter to 1. 
- Primary curve:
	- $(\mathsf{pc}_i, z_0,z_i)$: current program counter and inputs for the primary circuit
	- $U[\ ],W[\ ]$: List of relaxed instance/witness pairs for all the circuits on the primary curve. These can be `None` when the circuit for that pair has not yet been executed. The last updated entry is the result of having folded a proof for the correctness of $z_i$.
- Secondary curve
	- $(z_0', z_i')$: Inputs for the single circuit on the secondary curve. 
	- $u',w'$: Proof for the correctness of the circuit that produced $z_i'$ 
	- $U', W'$: Relaxed instance/witness pair into which $(u', w')$ will be folded into in the next iteration.

## Prove Step

At each step, the prover needs to:
- Create a proof $T'$ for folding $u'$ into $U'$, producing $U'\_{next}$
- Create a proof $(u,w)$ on the primary curve for the statements:
	- $(\mathsf{pc}\_{i+1}, z\_{i+1}) \gets F_\mathsf{pc_i}(z_i)$
	- Verifying the folding of $u'$ into $U'$ with $T'$
- Create a proof $T$ for folding $u$ into $U[\mathsf{pc}_i]$, producing $U\_{next}$ 
- Create a proof $(u'\_{next}, w'\_{next})$ for the verification on the secondary curve
	- Verifying the folding of $u$ into $U[\mathsf{pc}_i]$ with $T$
- Update the state of the claims
	- $U' = U'\_{next}$, $W' = W'\_{next}$
	- $U[\mathsf{pc}_i] = U\_{next}$, $W[\mathsf{pc}_i] = W\_{next}$
	- $(u',w') = (u'\_{next}, w'\_{next})$ 
- Save $z\_{i+1},z'\_{i+1}, \mathsf{pc}\_{i+1}$ as inputs for the next iteration. 



In pseudocode, `prove_step` looks something like:

```
if i = 0 {
	U[] = [ø;l]

	// Create a proof for the first iteration of F on the primary curve
	(pc1, z1), (u1, w1) <- Prove(F_{pc0},
		i=0,
		pc0,
		z0,
		_,   // zi : z0 is the input used
		_,   // U' : Existing accumulator is empty 
		_,   // u' : No proof of the secondary curve to verify
		_,   // T' : Nothing to fold
		0,   // index of u' in U'
	)

	// Create proof on secondary curve
	// verifying the validity of the first proof
	z1', (u1', w1') <- Prove(F',
		i,
		0,   // pc is always 0 on secondary curve
		z0',
		_,   // zi' : z0' is the input used
		_,   // U[]: all accumulators on primary curve are empty
		u0,  // proof for z1
		_,   // T: u0 is directly included into U[pc0]
		pc0, // index of u0 in U[]
	)

	// Update state to reflect first iteration 
	U[pc0] = u1
	W[pc0] = w1
	zi     = z1
	zi'    = z1'
	pc     = pc1
	U'     = ø
	W'     = ø
	u'     = u1'
	w'     = w1'
} else {
	// Create folding proof for u' into U', producing U'_next
	(U'_next, W'_next), T' <- NIFS.Prove(U', W', u', w')

	// Create a proof for the next iteration of F on the primary curve
	(pc_next, z_next), (u_new, w_new) <- Prove(F_{pc},
		i,
		pc,
		z0,
		zi,  
		[U'], 
		u',
		T',
		0,   // index of u' in [U'] is always 0
	)

	// Create folding proof for u_new into U[pci], producing U_next
	(U_next, W_next), T <- NIFS.Prove(U[pci], W[pci], u_new, w_new)

	// Create proof on secondary curve
	// verifying the folding of u_next into 
	z'_next, (u'_next, w'_next) <- Prove(F',
		i,
		pc,
		z0',
		zi', 
		U[], 
		u_new, 
		T,
		0,    // Circuit index is always 0 on secondary curve
	)

	// Update state to reflect first iteration 
	U[pc]  = U_next
	W[pc]  = W_next
	zi     = z_next
	zi'    = z'_next
	pc     = pc_next
	U'     = U'_next
	W'     = W'_next
	u'     = u'_next
	w'     = w'_next
}
```

Each iteration stops when the prover has produced a valid R1CS instance $(u',w')$ for the secondary circuit, just before folding it back into its accumulator $(U',W')$ in the next iteration. This allows us to access the public outputs of the secondary circuit in the next iteration, or when verifying the IVC chain.

### Augmented Circuit

During each proof iteration, the circuits evaluated and proved by the prover need to be *augmented* to include additional constraints which verify that the previous iteration was correctly accumulated. 

To minimize code duplication, there is only a single version of the recursive verification circuit. The circuit is customized depending on whether it is synthesized on the primary/secondary curve. 



#### Input Allocation

The inputs of provided to the augmented step circuit $F'_j$ are:

**Initial inputs**
- $\mathsf{vk}$: a digest of the verification key for the final compressing SNARK (which includes all public parameters of all circuits)
- $i \in \mathbb{Z}\_{\geq 0}$: the number of iteration of the functions before running $F$ 

**Inputs for step circuit**
- $\mathsf{pc} \in [\ell]$: index of the current function being executed
	- **Primary**: The program counter $\mathsf{pc}$ must always be `Some`, and through the `EnforcingStepCircuit` trait, we enforce $\mathsf{pc} \equiv j$.
	- **Secondary**: Always `None`, and interpreted as $\mathsf{pc} \equiv 0$, since there is only a single circuit.
- $z_0 \in \mathbb{F}^a$: inputs for the first iteration of $F$
- $z_i \in \mathbb{F}^a$: inputs for the current iteration of $F$
	- **Base case**: Set to `None`, in which case it is allocated as $[0]$, and $z_0$ is used as $z_i$.

**Inputs for recursive verification of other the curve's circuit**
- $U[\ ] \in \mathbb{R}'^\ell$: list of relaxed R1CS instances on the other curve
	- **Primary**: Since there is only a single circuit on the secondary curve, we have $\ell = 0$ and therefore $U[\ ]$ only contains a single `RelaxedR1CSInstance`. 
	- **Secondary**: The list of input relaxed instances $U[\ ]$ is initialized by passing a slice `[Option<RelaxedR1CSInstance<G>>]`, one for each circuit on the primary curve. Since some of these instances do not exist yet (i.e. for circuits which have not been executed yet), the `None` entries are allocated as a default instance.
- $u \in \mathbb{R}'$: fresh R1CS instance for the previous iteration on the other curve
	- Contains the public outputs of the 2 previous circuits on the different curves.
	- **Base case -- Primary**: Set to `None`, since there is no proof of the secondary curve to fold
- $T \in \mathbb{G}'$: Proof for folding $u$ into $U[\mathsf{pc}']$.
	- **Base case -- Primary**: Set to `None`, since there is no proof of the secondary curve to fold
- $\mathsf{pc}' \in [\ell]$: index of the previously executed function on the other curve. 
	- **Primary**: Always 0 since the program counter on the secondary curve is always 0
	- **Secondary**: Equal to the program counter of the last function proved on the primary curve.
    - 

All these variables are allocated at the beginning of the circuit, though they are initially unconstrained. 


#### Constraints

The circuit has a branching depending on whether it is verifying the first iteration of the IVC chain. Each branch computes the next list of instances $U\_{next}[\ ]$. 

##### Branch: i>0 `synthesize_non_base_case`

The verification circuit first checks that the public output $u.X_0$ is equal to the hash of all outputs of the previous circuit iteration. Note that this value is defined as a public output of the proof $u$ on the other curve. It was simply passed along unverified by the cycle circuit to link the two circuits from the same curve.
Since the base case does not have any previous input, we only check the hash if $i>0$. The circuit produces a bit corresponding to:

$$b\_{X_0} \gets X_0 \stackrel{?}{=} H(\mathsf{vk}, i, \mathsf{pc}_i, z_0, z_i, U[\ ])$$

This bit is checked later on. 

The circuit extracts $U[\mathsf{pc}']$ by using conditional selection on $U[\ ]$. This is done by computing a selector vector $s \in \{0,1\}^\ell$ such that $s\_{\mathsf{pc}'}=1$ and all other entries are 0.

The instance new folding instance $U\_{next}[\mathsf{pc}']$ is produced by running the NIFS folding verifier:

$$
U\_{next}[\mathsf{pc}'] \gets \mathsf{NIFS}.\mathsf{Verify}(\mathsf{vk}, u, U[\mathsf{pc}'], T)
$$

A new list of accumulators $U\_{next}[\ ]$ is then obtained using conditional selection

This branch returns $U\_{next}[\ ]$, $b\_{X_0}$ as well as the selector $s$.

##### Branch: i=0 (`synthesize_base_case`)

If $i \equiv 0$, then the verification circuit must instantiate the inputs as their defaults. Namely, it initializes a list $U[\ ]$ (different from the input list which is given to the previous branch) with "empty instances" (all group elements are set to the identity). 

Since the initial instance is trivial, the folding step is trivial as well so the $U[\mathsf{pc}']$ is replaced with $u$ using conditional selection, resulting in $U\_{next}[\ ]$. 

This branch returns $U\_{next}[\ ]$.

##### Remaining constraints 

Having run both branches, the circuit has computed 
- $U\_{next, i>0}[\ ], b\_{X_0}, s$ from the first branch
- $U\_{next, i=0}[\ ]$ from the second branch

- Using the bit $b\_{i=0} \gets i \stackrel{?}{=} 0$, it needs to conditionally select which list of instance to return. 
	- $U\_{next} \gets b\_{i=0} \ \ ?\ \ U\_{next, i=0}[\ ] \ \  :\ \  U\_{next, i>0}[\ ]$
- Check that $(i\neq 0) \implies b\_{X_0}$, enforcing that the hash is correct when not handling the base case
	- $b\_{i=0} \lor b\_{X_0}$  
- Select 
	- $z_i \gets b\_{i=0} \ \ ?\ \ z_0 \ \  :\ \  z_i$
- Enforce circuit selection
	- $\mathsf{pc}\_{i} \equiv j$
- Compute next output
	- $(\mathsf{pc}\_{i+1}, z\_{i+1}) \gets F_j(z_i)$


#### Public Outputs 

The output at this point would be 

$$
\Big (i+1, \mathsf{pc}\_{i+1}, z_0, z\_{i+1}, U\_{next}\Big)
$$

To keep the number of public outputs small, the outputs of the circuit are hashed into a single field element. We create this hash as $H\_{out} = H\big (\mathsf{vk}, i+1, \mathsf{pc}\_{i+1}, z_0, z\_{i+1}, U\_{next}\big)$. 

We also return the hash resulting from the output on the other curve, $u.X_1$. It will be unpacked at the start of the next iteration of the circuit on the cycle curve, so we swap it and place it first. The actual public output is then. 

$$
[u.X_1, H\_{out}]
$$

We can view output as the shared state between the circuits on the two curve. The list of two elements is a queue, where the last inserted element is popped out to be consumed by the verification circuit, and the resulting output is added to the end of the queue. 

## Verification

After any number of iterations of `prove_step`, we can check that the current prover state is correct. In particular, we want to ensure that $(z_i, z'_i)$ are the correct outputs after having run $i$ iterations of the folding prover.

To verify that $(z_i, z'_i)$ are correct, the verifier needs to recompute the public outputs of the latest proof $u'$. Since this is the output on the secondary curve, the first entry $u'.X_0$ will be the output of the primary curve circuit producing $(\mathsf{pc}_i, z_i)$ and the accumulator $U'$ in which we will fold $u'$. The second entry $u'.X_1$ is the output of the last circuit on the secondary curve, which will have folded the proof for $(\mathsf{pc}_i, z_i)$ into $U[\ ]$.

- $u'.X_0 \stackrel{?}{=} H(\mathsf{vk}, i, \mathsf{pc}_i, z_0, z_i, U')$
- $u'.X_1 \stackrel{?}{=} H'(\mathsf{vk}, i, z'_0, z'_i, U[\ ])$ 

We then verify that $(u',w')$ is a satisfying circuit, which proves that all relaxed instances $U[\ ], U'$ were correctly updated through by folding proof.

We then need to verify that all accumulators $(U[\ ], W[\ ])$ and $(U', W')$ are correct by checking the circuit satisfiability. 