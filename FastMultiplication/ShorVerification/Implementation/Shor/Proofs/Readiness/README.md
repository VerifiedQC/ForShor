# `Readiness/`

This folder proves workspace readiness and dynamic clean-state preservation
for the complete lowered Shor order-finding circuit, split by circuit stage
and chained in dependency order (each file may import all earlier ones):

```
Static < Sequencing < Primitives < Init < Step1 < Step2 < Step5 < IQFT < ModMul < ModExp < Dynamic
```

## `Static.lean`

The static readiness theorem: expands the public Shor reserve budget into
the per-stage `GateWorkspaceOK` facts the full lowered circuit needs.

- **`reserve_le_capacity_sub_one_of_succ_le`** / **`reserve_le_capacity_sub_two_of_two_add_le`**
  *(private)* — trivial `omega` arithmetic bridging a `1 + need ≤ capacity` /
  `2 + need ≤ capacity` hypothesis to `need ≤ capacity - 1`/`- 2`.
- **`gateWorkspaceOK_H_reg`** *(private)* — `H_reg r` (a left fold of `Gate.H`
  over a register's qubits) always satisfies `GateWorkspaceOK`, since
  individual Hadamards carry no recursive lowering obligation.
- **`constArithmeticWorkspace_of_cmpLtNWWorkspace`** *(private)* — derives
  the `ConstArithmeticWorkspace` needed by Step 3's typed comparator/subtract
  gates from a `CmpLtNWWorkspace` (Step 4's concrete comparator layout),
  including the scratch-width/constant-fits side conditions.
- **`gateWorkspaceOK_orderFindingApprox`** — the file's main theorem: given a
  `ShorApproxSetup` and `ShorWorkspaceLargeEnough`, derives `GateWorkspaceOK`
  for the whole `orderFindingApprox` circuit. Unpacks the reserve budget into
  per-step QFT/phase-product bounds (Steps 1, 2, 4, 5), discharges each
  `CmodMulInPlaceCore` invocation (`hCore`), folds that over the exponent
  qubit list via `hSteps` (mirroring `modExpApproxStepsValid`'s recursion),
  and combines with the Hadamard/init/final-IQFT obligations.
- **`LoweredShorReady.workspace`** — packages the theorem above through the
  public `LoweredShorReady` record, exposed as `.workspace` on a readiness
  proof; this is the field `Spec/Assertions.lean`'s
  `ShorCorrectApproxLoweredUniform` inlines.

## `Sequencing.lean`

The two-fact package every later stage is built from, and how to chain it
across `Gate.seq`.

- **`LoweredCleanResult`** — `LoweredCleanResult P G hworkspace ψ` bundles:
  (1) the recursively lowered gate `G` starts with clean local workspace
  (`GateWorkspaceCleanState`), and (2) the resulting state after evaluating
  the lowered `G` satisfies `P`.
- **`LoweredCleanResult.seq`** — the sequencing lemma: given
  `LoweredCleanResult` for `U` ending in `Pmid` and for `V` (starting from
  `U`'s output state) ending in `Pout`, produces `LoweredCleanResult` for
  `U ;; V` ending in `Pout`, by combining the two workspace-clean facts and
  rewriting through `LowerGateClass.evalL_seq`.

## `Primitives.lean`

Two parts: workspace-free gates (no recursive lowerer obligations), and
primitive register-locality/disjointness helpers plus Step 3/4 readiness.

**Workspace-free gates:**

- **`WorkspaceFree`** — an inductive predicate on `Gate`: true for `Gate.id`,
  any `Gate.H`/`Gate.X`, and closed under `;;`. Such gates contain no QFT or
  recursive phase-product nodes.
- **`WorkspaceFree.clean`** — a `WorkspaceFree` gate automatically satisfies
  `GateWorkspaceCleanState` for any workspace-OK proof and any input state,
  by induction on the `WorkspaceFree` derivation.
- **`workspaceFree_H_reg`** / **`workspaceFree_initY1`** — `H_reg r` and
  `initY1 r` are both `WorkspaceFree` (the former by folding `WorkspaceFree.H`
  over the register's qubits, the latter by cases on whether the register is
  empty).

**Primitive locality and Step 3/4 readiness:**

- **`reserve_active_disjoint_of_ownedDisjoint`** — owned-disjoint registers
  have their reserve disjoint from the other's active part.
- **`ownedDisjoint_symm`** — `OwnedDisjoint` is symmetric.
- **`disjoint_qubitReg_of_mem_right`** — a register disjoint from `s` is
  disjoint from any single qubit of `s`.
- **`disjoint_drop_left`** *(private)* — dropping qubits from the left side
  of a disjoint pair preserves disjointness.
- **`reserve_drop_active_disjoint_of_ownedDisjoint`** /
  **`reserve_drop_active_disjoint_self`** — the reserve (after dropping `n`
  qubits) of an owned-disjoint (resp. the same) register stays disjoint from
  the other's (resp. its own) active part.
- **`mem_grow_active_owned`** *(private)* — every active qubit of a grown
  register was already owned before growing.
- **`reserve_grow_active_disjoint_of_ownedDisjoint`** /
  **`reserve_drop_grow_active_disjoint_self`** *(private)* — disjointness
  facts survive growing the register on the other side, resp. the leftover
  reserve after growth stays disjoint from the grown active part.
- **`not_mem_right_of_mem_left_of_disjoint`** — membership on one side of a
  disjoint pair rules out membership on the other.
- **`eval_step3_preserves_lowering_clean`** *(private)* — evaluating the
  concrete Step-3 comparator/subtract gate (`step3`) preserves
  `ShorConcreteCleanState`, by combining the disjointness helpers above with
  `eval_step3_local_ket` (from `ModularExponentiation/Proofs/Core.lean`).
- **`eval_step4_preserves_lowering_clean`** — the analogous preservation fact
  for the concrete Step-4 comparator (`step4`), via `eval_step4_local_ket`.
- **`shorConcreteCleanState_to_constArithmeticCleanState`** *(private)* —
  `ShorConcreteCleanState` implies the `CmpGeConstCleanState` Step 3's lowered
  comparator needs (freshness of the data-carry and scratch registers).
- **`lowered_step3_ready_and_clean`** — the section's headline theorem:
  packages Step 3's `GateWorkspaceCleanState` (from
  `evalL_lowerCmpGeConst_preserves_clean`) and its preservation of
  `ShorConcreteCleanState` into a `LoweredCleanResult`.

## `Init.lean`

Readiness and clean-state preservation for the two workspace-free
initialization gates, `H_reg x.active` and `initY1 data.active`.

- **`eval_H_reg_preserves_threeRegsCleanState`** — a register Hadamard
  preserves `ThreeRegsCleanState` on any three registers disjoint from it,
  by expanding `H_reg` into its basis sum (via `RegisterHadamardSemantics.eval_Hreg_ket`
  from `ModularExponentiation/Proofs/Core.lean`) and checking each term.
- **`eval_X_preserves_threeRegsCleanState`** *(private)* — the analogous fact
  for a single `Gate.X`.
- **`lowered_H_reg_ready_and_full_clean`** — packages the exponent-register
  Hadamard's workspace-freeness (`WorkspaceFree.clean`) and its
  `ShorLoweringCleanState` preservation into a `LoweredCleanResult`.
- **`eval_initY1_preserves_fullShorWorkspaceCleanState`** *(private)* —
  `initY1 data.active` preserves `ShorLoweringCleanState`, by cases on
  whether the data register is empty (identity) or not (a single `X`).
- **`lowered_initY1_ready_and_full_clean`** — the data-initialization
  analogue of `lowered_H_reg_ready_and_full_clean`.

## `Step1.lean`

Step 1 (the data reserve after dropping the carry bit, and the full work
reserve).

- **`threeRegsCleanState_to_grownRecursiveWorkspaceCleanState`** — converts
  `ThreeRegsCleanState` on three registers into `RecursiveWorkspaceCleanState`
  for a phase-product workspace's grown x/z extensions, when the workspace's
  reserves match two of the three clean registers.
- **`gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean`** — derives
  `GateWorkspaceCleanState` for a `Gate.CPhaseProdUsing` node directly from
  `ThreeRegsCleanState`, via the conversion above and
  `LowerGateClass.evalL_zeroExtend`.
- **`eval_CPhaseProdUsing_preserves_threeRegsCleanState`** — evaluating
  `Gate.CPhaseProdUsing` preserves `ThreeRegsCleanState`, using
  `GateSemanticsFacts.eval_CPhaseProdUsing_ket`'s ket-level semantics (the
  gate acts as a scalar on a clean basis state).
- **`eval_IQFT_preserves_threeRegsCleanState`** — the inverse QFT on a
  register `r` preserves `ThreeRegsCleanState` on any three registers
  disjoint from `r.active`, by expanding it into its basis sum
  (`eval_iqft_work_expansion`) and checking each term.
- **`threeRegsCleanState_to_QFTWorkspaceCleanState`** — `ThreeRegsCleanState`
  implies `QFTWorkspaceCleanState` for a QFT's x/z workspace pools, when the
  third clean register matches the reserve they're both carved from
  (`qftXWork`/`qftZWork_mem_reserve`).

## `Step2.lean`

Step 2: makes the carry bit active, swaps the phase-product operand order,
and preserves `ShorLoweringCleanState`. Also proves Step 4's full lowered
readiness (its local recursive workspace lives in the same file as the
constant-multiplication helper it reuses) and Step 1's own packaged theorem.

- **`threeRegsCleanState_swap23`** *(private)* — the second and third clean
  registers of `ThreeRegsCleanState` play symmetric roles.
- **`ownedQubits_grow_subset`** / **`ownedDisjoint_grow_right`** *(private)* —
  growing a register never adds qubits it didn't already own, so
  owned-disjointness survives growing the right-hand register.
- **`eval_QFT_preserves_threeRegsCleanState`** *(private)* — the forward QFT
  (not just inverse) preserves `ThreeRegsCleanState`, by the same basis-sum
  expansion technique as `Step1.lean`'s IQFT lemma but via `QFTSemantics.eval_QFT_ket`.
- **`gateWorkspaceCleanState_PhaseProdUsing_of_threeRegsClean`** /
  **`eval_PhaseProdUsing_preserves_threeRegsCleanState`** *(private)* — the
  uncontrolled-phase-product analogues of `Step1.lean`'s `CPhaseProdUsing`
  lemmas.
- **`shorConcreteCleanState_to_step4ReserveClean`** *(private)* — Step 4
  temporarily uses `scratch.active`, but its three lowering-workspace
  reserves are already zero in the public concrete Shor invariant; this
  extracts that fact as a plain `ThreeRegsCleanState`.
- **`lowered_fastConstMulInto_ready_and_clean`** *(private)* — dynamic
  readiness for the QFT/phase-product/inverse-QFT block computing `N * work`
  into Step 4's scratch register (`fastConstMulInto`), sequencing the three
  sub-gates via `LoweredCleanResult.seq`.
- **`lowered_step4_ready_and_clean`** — Step 4's full lowered readiness: the
  forward constant-multiplication block is discharged from the reserve-only
  invariant, the comparator difference/CNOT sign-copy are workspace-trivial,
  and the adjoint constant-multiplication block is discharged at the fully
  uncomputed high-level output (via `eval_step4_preserves_lowering_clean`
  from `Primitives.lean`).
- **`lowered_step1_ready_and_full_clean`** — Step 1's own packaged theorem
  (despite living in this file): sequences the CPhaseProdUsing/IQFT stages
  using `Step1.lean`'s lemmas into a `LoweredCleanResult` for the concrete
  `step1` gate.
- **`lowered_step2_ready_and_carry_clean`** — the file's other named stage
  theorem: Step 2's full lowered readiness, preserving `ShorLoweringCleanState`
  after making the carry bit active.

## `Step5.lean`

Step 5, proved by decomposing it as the adjoint of a forward circuit
(`step5Forward`), proving the forward body clean, then applying a generic
adjoint-preservation lemma. The largest file in the folder.

- **`LoweredCleanResult.adj`** *(private)* — the generic adjoint-sequencing
  lemma: if the forward gate `U`'s `LoweredCleanResult` holds starting from
  `†U`'s output state, and the postcondition holds after `†U`, then `†U`
  itself has a `LoweredCleanResult` from the original input.
- **`step5Forward`** *(private)* — the forward circuit Step 5 is defined as
  the adjoint of: `H_reg work.active`, a controlled phase product encoding
  `2·(k5val mod N)/N`, then the final inverse QFT on the z-extension.
- **`step5_eq_adj_step5Forward`** *(private)* — `step5 = †step5Forward` (by
  `rfl`).
- **`ThreeRegsCleanState.weaken`** *(private)* — `ThreeRegsCleanState`
  transports along register-subset hypotheses (weakens which qubits are
  required fresh).
- **`threeRegsCleanState_to_grownRecursiveWorkspaceCleanState_of_subset`** /
  **`gateWorkspaceCleanState_CPhaseProdUsing_of_threeRegsClean_of_subset`** /
  **`eval_CPhaseProdUsing_preserves_threeRegsCleanState_of_subset`**
  *(private)* — subset-hypothesis variants of `Step1.lean`'s three
  `CPhaseProdUsing`-related lemmas, needed because Step 5's clean registers
  don't line up exactly with the phase-product workspace's reserves.
- **`lowered_step5Forward_ready_and_full_clean`** *(private)* — dynamic
  readiness for the forward circuit: sequences the Hadamard, controlled
  phase-product, and inverse-QFT stages.
- **`qeval_injective`** *(private)* — `qs.eval U` is injective, via
  `qs.eval_adj_apply`.
- **`eval_adj_seq_eq`** / **`eval_adj_adj_eq`** *(private)* — adjoint
  distributes contravariantly over `;;` (`†(U;;V) = †U ∘ †V` as evaluators),
  and adjoint is involutive (`††U = U`), both proved via injectivity of
  `qs.eval` rather than gate-syntax rewriting.
- **`eval_step5_QFT_preserves_full_clean`** *(private)* — the QFT on Step
  5's z-extension preserves `ShorLoweringCleanState`, by basis-sum expansion.
- **`step5Workspace_xReserve_subset`** / **`step5Workspace_zReserve_subset`**
  — Step 5's phase-product workspace reserves are subsets of the data/work
  reserves (definitional `rfl` facts).
- **`eval_adj_step5_CPhaseProdUsing_preserves_full_clean`** — the *adjoint*
  controlled phase product preserves `ShorLoweringCleanState`: since it acts
  as a nonzero scalar `c⁻¹` on each clean basis ket (derived from the forward
  gate's scalar action via `qs.eval_adj_apply`), cleanliness survives.
- **`writeNat_writeNat_same`** — writing a value twice to the same register
  is the same as writing it once (the second write overwrites the first).
- **`bit_writeNat_qubitReg`** *(private)* / **`bit_eq_testBit_toNat_qubitReg`**
  — single-qubit bit/`testBit` correspondence facts used to reason about
  `Gate.H`'s ket-level action.
- **`hadamard_scale_sq`** — `(1/√2)² · 2 = 1`, the normalization identity
  behind Hadamard being self-inverse.
- **`hadamard_plus_identity`** / **`hadamard_minus_identity`** — the module
  identities `a•(a•(u+v) + a•(u-v)) = u` and `a•(a•(u+v) - a•(u-v)) = v` for
  `a` satisfying `hadamard_scale_sq`, the linear-algebra core of `H ∘ H = id`.
- **`eval_H_involutive_ket`** *(private)* — `Gate.H q` applied twice to a
  basis ket returns the same ket, via the two identities above.
- **`eval_H_involutive`** *(private)* — lifts the ket-level involution fact
  to arbitrary states by linearity (`qs.state_induction`).
- **`eval_adj_H_eq_eval_H`** *(private)* — since `H` is self-adjoint and
  involutive, `†(Gate.H q)` evaluates the same as `Gate.H q` itself.
- **`eval_H_preserves_threeRegsCleanState`** *(private)* — a single Hadamard
  preserves `ThreeRegsCleanState` on registers disjoint from its qubit.
- **`eval_adj_H_preserves_threeRegsCleanState`** *(private)* — the adjoint
  version, immediate from the previous two lemmas.
- **`eval_adj_hadamardFold_preserves_threeRegsCleanState`** *(private)* —
  generalizes the single-Hadamard locality fact to a left fold of Hadamards
  (i.e. `H_reg`), by induction on the qubit list.
- **`eval_adj_H_reg_work_preserves_full_clean`** *(private)* — specializes
  the fold lemma to `†(H_reg work.active)` preserving
  `ShorLoweringCleanState`.
- **`eval_adj_step5Forward_eq`** *(private)* — unfolds `†step5Forward`
  semantically into QFT, then adjoint controlled-phase-product, then adjoint
  Hadamards, using `eval_adj_seq_eq`/`eval_adj_adj_eq`.
- **`eval_adj_step5Forward_preserves_full_clean`** — the main semantic
  preservation theorem: composes the QFT/adjoint-phase-product/adjoint-Hadamard
  locality facts above to show the full adjoint Step-5 circuit preserves
  `ShorLoweringCleanState`.
- **`lowered_step5_ready_and_full_clean`** — the main lowered-readiness
  theorem: packages the semantic preservation fact with
  `lowered_step5Forward_ready_and_full_clean`'s local workspace obligations
  (via `LoweredCleanResult.adj`) into a `LoweredCleanResult` for the public
  `step5` gate.
- **`threeRegsCleanState_to_QFTWorkspaceCleanState_first`** — the
  first-register variant of `Step1.lean`'s
  `threeRegsCleanState_to_QFTWorkspaceCleanState` (matching the *first* clean
  register against the QFT reserve instead of the third); consumed by
  `IQFT.lean` for the final inverse QFT, whose reserve happens to line up
  with the exponent register rather than the third clean slot.

## `IQFT.lean`

Lowered readiness for the final inverse QFT applied to the exponent
register at the end of order finding.

- **`lowered_IQFT_ready_and_full_clean`** *(private)* — under the full
  `ShorLoweringCleanState` invariant: the high-level inverse QFT changes only
  `x.active`, so all three reserve registers stay clean
  (`eval_IQFT_preserves_threeRegsCleanState`), and the QFT's own workspace
  cleanliness follows from `threeRegsCleanState_to_QFTWorkspaceCleanState_first`.
- **`lowered_IQFT_ready_and_concrete_clean`** — the same fact under the
  strengthened `ShorConcreteCleanState` invariant that also tracks the
  Step-3/4 scratch register, reducing to the full-clean case via
  `ShorConcreteCleanState.to_lowering`.

## `ModMul.lean`

Lowered readiness for one controlled modular-multiplication core
(`CmodMulInPlaceCore`), one exponent/control qubit at a time.

- **`shorConcreteCarrier`** — a proof-only exponent view: an `ExtReg` whose
  active part is the real exponent register but whose reserve is the
  strengthened exponent-plus-scratch register from `ShorConcreteCleanState`.
  Lets the Hadamard/Step-1/2/5 lemmas (stated for a plain exponent register)
  be reused without losing track of scratch cleanliness.
- **`shorConcreteCarrier_ownedQubits`** *(private, `@[simp]`)* — the
  carrier's owned qubits are exactly the exponent's plus the scratch
  register's.
- **`shorConcreteCarrier_ownedDisjoint_right`** — the carrier is
  owned-disjoint from any register disjoint from both the exponent and
  scratch.
- **`flag_not_shorConcreteCarrier`** *(private)* — the comparator flag is
  outside the carrier's owned qubits whenever it's outside both the exponent
  and scratch.
- **`lowered_CmodMulInPlaceCore_ready_and_clean`** — the main theorem:
  sequences Steps 1 through 5 (`step1`/`step2`/`step3`/`step4`/`step5`),
  threading `ShorConcreteCleanState` through the lowered implementation via
  `LoweredCleanResult.seq`, reusing the exponent-position lemmas through
  `shorConcreteCarrier` for Steps 1, 2, and 5.

## `ModExp.lean`

Folds the per-core result over the full list of exponent/control qubits.

- **`lowered_modExpApproxStepsValid_ready_and_clean`** — the only
  declaration: folds `lowered_CmodMulInPlaceCore_ready_and_clean` over
  `ctrls` by induction, threading `ShorConcreteCleanState` through every
  controlled modular multiplication in the loop via `LoweredCleanResult.seq`
  at each cons step.

## `Dynamic.lean`

Assembles the per-stage results above into readiness and dynamic
clean-state preservation for the complete circuit — the final theorem of
this directory.

- **`lowered_orderFindingApprox_ready_and_full_clean`** — composes exponent
  Hadamards, data initialization, the full modular-exponentiation loop, and
  the final inverse QFT (in that order) via `LoweredCleanResult.seq`,
  proving the complete lowered circuit starts each recursive sub-lowering
  with clean workspace and preserves `ShorConcreteCleanState`.
- **`gateWorkspaceCleanState_orderFindingApprox`** — the main public
  clean-workspace theorem for the raw setup arguments: starting from an
  initially clean basis state (`shorConcreteCleanState_ket` from
  `Proofs/Budgets.lean`), the full approximate order-finding gate has clean
  local workspace everywhere the lowering procedure needs it.
- **`LoweredShorReady.workspace_clean`** — packages the theorem above through
  the public `LoweredShorReady` record as `.workspace_clean`; together with
  `Static.lean`'s `.workspace`, this is what
  `Proofs/Correctness.lean`'s `Shor_correct_approx_lowered_of_modExp_bound`
  consumes to discharge `orderFindingApproxLow_probability_eq`'s cleanliness
  hypothesis.
