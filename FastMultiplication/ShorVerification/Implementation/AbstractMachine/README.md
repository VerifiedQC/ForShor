# AbstractMachine

This directory contains the low-level abstract machine for the Shor verification development. Its job is to take the high-level `Gate` programs from `Basic.lean` and prove that their lowered `LowGate` implementations have the same semantics.

The final approach is deliberately two-stage:

1. First, prove specialized lowerers for the hard recursive gates: signed phase products, controlled signed phase products, and QFT.
2. Then, define a whole-program lowerer by structural recursion over arbitrary `Gate` syntax and dispatch the hard cases to those specialized theorems.

This separation keeps the final theorem small. Most of the work is hidden behind explicit lowering plans, readiness predicates, and workspace-cleanliness proofs.

## Final Endpoint

The main public theorem of this directory is:

```lean
theorem lowerGate_correctness
```

in `WholeProgramCorrectness.lean`. It states that evaluating the lowered `LowGate` program agrees with evaluating the original high-level `Gate`, assuming:

- `GateWorkspaceOK ops G`: the gate has enough static reserve workspace for every recursive QFT and phase-product node.
- `GateWorkspaceCleanState qs k hk ops G hworkspace ψ`: the relevant reserve bits are clean at the input state where each lowered subprogram begins.
- the phase-product source program `ops` is safe and returns the symbolic state to `State.start_state`.

The proof is by induction on `Gate`. Direct gates lower constructor-by-constructor. `Gate.QFT` calls the QFT lowering theorem, and signed/controlled signed phase products call the phase-product lowering theorems.

## Root Files

### `LowGate.lean`

This file defines the target language:

```lean
inductive LowGate
```

`LowGate` contains direct low-level counterparts for primitive high-level gates, plus explicit constructors for arithmetic operations, naive phase-product leaves, allocation/deallocation, and radix reversal. It is intentionally only syntax. The semantics are supplied later by `LowerGateClass`, so the lowering proofs can be parametric in the concrete quantum model.

This is the foundation used by every file below: all lowerers erase their proof data into a `LowGate`.

### `WholeProgramCorrectness.lean`

This is the final assembly file for the abstract machine.

It defines:

- `GateWorkspaceOK`: a static, syntax-directed condition saying every recursive node has enough reserve workspace.
- `lowerGate`: the public lowering function from high-level `Gate` to `LowGate`.
- `GateWorkspaceCleanState`: the dynamic clean-state condition needed at the exact state where each lowered subprogram starts.
- `lowerGate_correctness`: the whole-program semantic correctness theorem.

The key design choice is that callers do not build phase-product or QFT lowering plans themselves. They only prove `GateWorkspaceOK`; the concrete specialized lowerers construct the internal plans and layouts.

## `PhaseProductLoweringCorrectness/`

This folder proves correctness of recursive lowering for `Gate.SignedPhaseProd` and `Gate.CSignedPhaseProd`.

The final public outputs are:

```lean
noncomputable def lowerSignedPhaseProdWithWorkspace
theorem evalL_lowerSignedPhaseProd

noncomputable def lowerCSignedPhaseProdWithWorkspace
theorem evalL_lowerCSignedPhaseProd
```

These are the theorems consumed by `WholeProgramCorrectness.lean`.

The proof strategy is:

1. Define the compiled replacement gate using the phase-product compiler theorem.
2. Build an explicit finite recursive lowering plan.
3. Prove that interpreting a ready plan is semantically correct.
4. Prove linearity/closure lemmas so basis-state readiness scales to general quantum states.
5. Prove the canonical workspace choices make the plan ready.
6. Package the plan and readiness proofs into public signed and controlled correctness theorems.

### `Definitions.lean`

This file sets up the objects used everywhere else in the folder.

It defines `compiledSignedPhaseGate` and `compiledCSignedPhaseGate`, which are the high-level compiled gates that replace primitive signed phase products. These use `compileOpsToSignedGate` and `compileOpsToCSignedGate` from the algorithm-correctness layer, with interpolation coefficients supplied by `loweringPhaseCoeff`.

It also defines:

- `LowerGateClass`: the semantic interface for interpreting `LowGate`.
- `LowerablePhaseGate`: the syntactic class of high-level gates supported by the phase-product lowering planner.
- width and reserve models such as `immediateNeed`, `reserveNeed`, and `requiredChildReserve`.
- `SignedRecursiveWorkspaceOK` and `CSignedRecursiveWorkspaceOK`: static recursive workspace conditions.
- `RecursiveWorkspaceCleanBasis`, `RecursiveWorkspaceCleanState`, `SignedRecursiveWorkspaceStateOK`, and `CSignedRecursiveWorkspaceStateOK`: dynamic cleanliness conditions.

This file answers the question: what does it mean for a phase-product lowering problem to have enough recursive workspace?

### `Plan.lean`

This file introduces the actual lowering plan datatype:

```lean
inductive PhaseLoweringPlan
```

A plan is a finite certificate explaining how to lower a high-level gate. Direct gates map straight to `LowGate` constructors. A signed phase product either:

- stops at a naive low-level phase-product leaf, or
- recurses through a concrete `Gate.PhaseProductLayout`, using the compiled phase-product circuit as the next child gate.

The interpreter:

```lean
noncomputable def lowerGateRec
```

erases the plan into a `LowGate`.

This file also constructs the canonical standard plans:

- `standardSignedPhaseLoweringPlan`
- `standardCSignedPhaseLoweringPlan`

Those are the recursive plans used by the public lowerers.

### `PlanSemantics.lean`

This file proves that a ready plan is correct.

It defines:

```lean
noncomputable def PhaseLoweringReady
```

`PhaseLoweringReady` is the semantic precondition for executing a plan at a particular state. Direct gates require no readiness. Recursive phase-product steps require a clean compiler workspace and readiness for the child plan.

The central theorem is:

```lean
lemma evalL_lowerGateRec_correct
```

It proves, by induction over `PhaseLoweringPlan`, that evaluating `lowerGateRec plan` with `LowerGateClass.evalL` agrees with evaluating the high-level gate stored in the plan. The recursive step uses the phase-product compiler correctness theorem through:

- `eval_compiledSignedPhaseGate_correct`
- `eval_compiledCSignedPhaseGate_correct`

This file is the semantic heart of the phase-product lowering proof.

### `Linearity.lean`

This file proves closure properties needed to move from basis-state cleanliness to arbitrary quantum states.

The important idea is that phase products act diagonally on basis states, so they preserve recursive workspace cleanliness. The file proves this first for signed phase products:

```lean
lemma eval_SignedPhaseProd_preserves_recursiveWorkspaceClean
```

It then develops linear closure facts for plan evaluation and readiness:

- zero states,
- sums,
- scalar multiples.

These lemmas are what let later readiness proofs work for general `qs.State`, not only for individual basis kets.

### `Workspace.lean`

This file connects the abstract reserve predicates from `Definitions.lean` to the concrete layouts used by the compiler.

Its lemmas move fresh-zero facts across subregister inclusions, show that child reserve bits lie inside parent reserve bits, and derive compiler workspace hypotheses from recursive workspace cleanliness.

The key endpoint is:

```lean
lemma eval_compileSignedAllocations_ket_fits_and_child_clean
```

It says that allocation into the compiled signed layout both produces the fitted encoded state needed by the compiler proof and leaves the child recursive reserves clean.

This file answers the question: why does the static recursive reserve model actually give the clean physical workspace required by the next recursive call?

### `PlanReadiness.lean`

This file assembles the readiness proof for the canonical phase-product plans.

It first proves readiness for annotated compiled bodies, including the no-phase prefixes and the recursive phase leaves that appear in block decompositions. Then it proves readiness for allocation and deallocation plans. Finally it packages everything into:

```lean
theorem standardSignedPhaseLoweringPlan_ready_and_clean
theorem standardSignedPhaseLoweringPlan_ready
theorem standardCSignedPhaseLoweringPlan_ready
```

and the workspace-facing helpers:

```lean
lemma standardSignedPhaseLoweringPlan_ready_of_workspace
lemma standardCSignedPhaseLoweringPlan_ready_of_workspace
```

This file is the bridge from "we have a canonical recursive plan" to "that plan is executable at the current clean state."

### `Correctness.lean`

This is the public packaging layer for phase-product lowering.

It combines:

- the standard plans from `Plan.lean`,
- the readiness theorems from `PlanReadiness.lean`,
- the plan interpreter theorem from `PlanSemantics.lean`,
- and the generated interpolation-point facts.

The result is the public signed and controlled correctness API:

```lean
theorem evalL_lowerSignedPhaseProd
theorem evalL_lowerCSignedPhaseProd
```

These theorems are exactly what the whole-program proof uses for `Gate.SignedPhaseProd` and `Gate.CSignedPhaseProd`.

## `QFTLoweringCorrectness/`

This folder proves correctness of recursive lowering for `Gate.QFT`.

The final public output is:

```lean
noncomputable def lowerQFT
theorem evalL_lowerQFT
```

These are consumed by `WholeProgramCorrectness.lean`.

The QFT proof depends on the phase-product proof because the split QFT identity contains a middle phase-product gate.

### `PlanSemantics.lean`

This file defines the explicit recursive QFT plan:

```lean
inductive QFTLoweringPlan
```

A QFT plan has three cases:

- empty register: lower to `LowGate.id`;
- singleton register: lower to one Hadamard gate;
- split register: lower the right QFT, then lower the middle phase product, then lower the left QFT, then apply radix reversal.

The plan is workspace-agnostic. A split node stores a phase-product workspace and a phase-product lowering plan, but it does not decide how to carve the reserve registers.

The central theorem is:

```lean
theorem evalL_lowerQFTPlan
```

It proves that a ready QFT plan evaluates like `Gate.QFT`. The recursive split case uses the high-level theorem `eval_QFT_split` and the phase-product plan correctness theorem.

### `Workspace.lean`

This file chooses the canonical concrete workspace for QFT lowering and builds the lowered circuit.

It carves the inactive reserve of the QFT input register into two pools:

- `qftXWork`
- `qftZWork`

It defines the workspace-size function and static workspace predicates:

- `qftWorkspaceNeed`
- `QFTReserveOK`
- `QFTWorkspaceOK`

It also constructs the phase-product plan used inside a QFT split:

```lean
noncomputable def standardPhaseProdUsingPlan
```

and then builds the standard recursive QFT plan:

```lean
noncomputable def standardQFTLoweringPlan
noncomputable def reserveQFTLoweringPlan
noncomputable def lowerQFT
```

This file now stops at construction. It answers the static question: how do we carve the reserve register and build the recursive QFT lowering plan?

### `Readiness.lean`

This file proves that the concrete workspace selected in `Workspace.lean` is clean enough to execute the recursive QFT plan, and that the resulting `lowerQFT` circuit is semantically correct.

It defines and uses the dynamic clean-state predicates from the workspace layer:

- `QFTWorkspaceCleanState`
- `QFTWorkspaceStateOK`

The proof has three main jobs:

- convert fresh-zero facts about `qftXWork` and `qftZWork` into the phase-product clean-state assumptions needed by the middle split gate;
- prove that the middle phase product and the recursive QFT calls preserve those workspace pools;
- assemble readiness for the standard recursive QFT plan and expose the public correctness theorem.

The important readiness and correctness endpoints are:

```lean
theorem standardPhaseProdUsingPlan_ready_and_clean
theorem standardQFTLoweringPlan_ready_and_clean
theorem evalL_lowerQFT
```

This file answers the dynamic question: given the static reserve condition plus clean reserve bits in the input state, why is the canonical QFT lowering ready, clean-preserving, and semantically correct?

## How the Proofs Fit Together

The dependency flow is:

```text
LowGate
  -> PhaseProductLoweringCorrectness/Definitions
  -> PhaseProductLoweringCorrectness/Plan
  -> PhaseProductLoweringCorrectness/PlanSemantics
  -> PhaseProductLoweringCorrectness/Linearity
  -> PhaseProductLoweringCorrectness/Workspace
  -> PhaseProductLoweringCorrectness/PlanReadiness
  -> PhaseProductLoweringCorrectness/Correctness
  -> QFTLoweringCorrectness/PlanSemantics
  -> QFTLoweringCorrectness/Workspace
  -> QFTLoweringCorrectness/Readiness
  -> WholeProgramCorrectness
```

Conceptually:

1. `LowGate.lean` gives the target syntax.
2. The phase-product folder proves the hard recursive phase-product lowering theorem.
3. The QFT folder proves recursive QFT lowering, using phase-product lowering for the middle cross-term.
4. `WholeProgramCorrectness.lean` turns those component results into a lowering theorem for arbitrary high-level `Gate` programs.

The final result is that the rest of the repository can reason about a high-level circuit, lower it to an explicit `LowGate` circuit, and use `lowerGate_correctness` to transfer semantic facts across that lowering step.
