# `Implementation/Shor/`

This folder assembles the pieces proved in `Compilation/`, `QFT/`,
`PhaseProduct/`, and `ModularExponentiation/` into the full approximate
order-finding circuit and proves Shor's algorithm correct: workspace
readiness for the whole lowered circuit, the success-probability bound, and
the classical reduction from a good order-finding outcome to a nontrivial
factor.

The folder is organized in layers (below). **Every import is "justified":** a
file may only import another file if it directly uses a declaration that
file defines — never a declaration it merely re-exports transitively.
`scripts/check_shor_layers.sh` (repo root) enforces the layer order, the
`Proofs/Readiness/` chain order, and the absence of umbrella files (a file
that only imports and declares nothing of its own); it also enforces the
one allowlisted exception below. `scripts/check_compilation_layers.sh`
enforces the analogous discipline for the sibling `Compilation/` folder that
`Shor/` sits above.

## Layer order

```
Math  <  Circuit  <  Spec  <  Proofs  <  Main
```

A file may import its own folder or any folder to its left. Inside `Proofs/`:

```
Budgets, Setup  <  Readiness/*  <  NaiveShor/*  <  Correctness
```

and the `Readiness/` chain is itself ordered

```
Static < Sequencing < Primitives < Init < Step1 < Step2 < Step5 < IQFT < ModMul < ModExp < Dynamic
```

**One allowlisted exception:** `Spec/Assertions.lean` imports
`Proofs/Readiness/Static.lean` directly. The assertion
`ShorCorrectApproxLoweredUniform` inlines a `GateWorkspaceOK` proof term into
the circuit; by proof irrelevance the *meaning* of the Prop doesn't depend on
that proof's body, but the *file* dependency is real until `Spec` gains its
own `hws : GateWorkspaceOK …` field or existentially quantifies over it.

Reading order for newcomers: start at `Main.lean`, then follow imports
*backwards* — `Spec/Assertions.lean` for what is claimed, `Proofs/Correctness.lean`
for how the claim is proved, and outward from there into `Proofs/Readiness/`,
`Spec/`, `Circuit/`, `Math/` as needed. The one-line descriptions below are
grouped in dependency order (lowest layer first) to match that traversal.

## `Math/` — pure math, no framework/register dependencies

| File | Purpose |
|---|---|
| `OrderFindingAnalysis.lean` | Number-theory, Fourier/geometric-sum, and counting lemmas backing the ideal order-finding good-outcome analysis. Import closure is Mathlib plus the project's semantics-free vocabulary (`ord`, `qftPhase`, `GoodOutcome`) — no `QSemantics`, `eval`, or measurement. |

## `Circuit/` — the concrete order-finding circuit

| File | Purpose |
|---|---|
| `Workspace.lean` | The static reserve budgets and capacity/isolation conditions (`ShorWorkspaceNeed`, `shorWorkspaceNeed`, `ShorWorkspaceLargeEnough`, `ShorWorkspaceIsolation`) used by the lowering readiness proofs. |
| `OrderFinding.lean` | The approximate order-finding circuit (`orderFindingApprox`/`orderFindingApproxLow`), built from the verified modular-exponentiation implementation, and the ideal circuit (`orderFindingIdeal`) that swaps in the abstract exact modular-exponentiation gate. |

## `Spec/` — the public specification surface

| File | Purpose |
|---|---|
| `Cleanliness.lean` | The static clean-input predicates and dynamic clean-state invariants (`ThreeRegsCleanState`, `FullShorWorkspaceCleanState`, `ShorLoweringCleanState`, `ShorConcreteCleanState`, `IdealOrderFindingInput`) used by the readiness proofs and the final correctness statements. |
| `Setup.lean` | The user-facing setup/readiness records (`ShorLoweringSetup`, `ShorApproxSetup(Minimal)`, `LoweredShorReady`, `ShorFactoringInstance`) and the bridge from the lower-level implementation setup to the public one. |
| `Assertions.lean` | The final Shor correctness guarantees (`ShorCorrect`, `ShorCorrectApproxLoweredUniform`), each stated once as a named proposition. `Proofs/Correctness.lean`'s theorems are typed directly by these Props, so there is exactly one copy of each statement. |

## `Proofs/` — everything below is proof-only; nothing outside `Proofs/`/`Main.lean` may import it

| File | Purpose |
|---|---|
| `Budgets.lean` | The dynamic clean-state preservation lemmas for the clean-state invariants declared in `Spec/Cleanliness.lean`. |
| `Setup.lean` | `ShorApproxSetup.toIdealOrderFindingInput` — the final bridge from the approximate setup to the ideal order-finding input predicate. |
| `Readiness/` | Workspace readiness and clean-state preservation for the full lowered circuit, split by circuit stage (below); see each file's own docstring for its exact scope. |
| `Correctness.lean` | The quantum-facing part of the Shor statement: the ideal and approximate order-finding circuits, the measurement interface, and the final success-probability theorem. Classical order/continued-fraction material lives in `NaiveShor/`. |
| `NaiveShor/` | The ideal-circuit (`ctrlModMul`) analysis: preliminaries, the QPE/IQFT chain, the good-outcome mass lower bound, and the classical reduction tying a good outcome to a nontrivial factor. |

### `Proofs/Readiness/` — chained by circuit stage

| File | Purpose |
|---|---|
| `Static.lean` | The public static readiness theorem `gateWorkspaceOK_orderFindingApprox`, expanding `ShorWorkspaceLargeEnough` into the per-stage `GateWorkspaceOK` facts, and its packaged form `LoweredShorReady.workspace`. |
| `Sequencing.lean` | `LoweredCleanResult`/`LoweredCleanResult.seq` — the two-fact package (clean local workspace + post-state satisfies `P`) and its sequencing lemma across `Gate.seq`, used by every later stage. |
| `Primitives.lean` | Workspace-free gate locality (`WorkspaceFree.clean`) and the primitive register-locality/disjointness helpers, plus Steps 3/4 (comparator and its lowering) readiness and clean-state preservation. |
| `Init.lean` | Readiness and clean-state preservation for `H_reg`/`initY1`, which allocate no recursive lowering workspace but must still preserve the global clean-state invariant. |
| `Step1.lean` | Step 1 (data reserve after dropping the carry bit, full work reserve); final theorem `lowered_step1_ready_and_full_clean`. |
| `Step2.lean` | Step 2 (carry bit active, swapped phase-product operand order), preserving `ShorLoweringCleanState`. |
| `Step5.lean` | Step 5 via adjoint decomposition: proves the forward Step-5 body clean, then applies the generic adjoint lemma `LoweredCleanResult.adj`. |
| `IQFT.lean` | The final inverse QFT on the exponent register: `lowered_IQFT_ready_and_full_clean` under the full clean-state invariant, `lowered_IQFT_ready_and_concrete_clean` under the strengthened concrete one. |
| `ModMul.lean` | One controlled modular-multiplication core (`CmodMulInPlaceCore`), one exponent/control qubit at a time. |
| `ModExp.lean` | Folds `ModMul.lean`'s per-core result over the full list of exponent/control qubits, preserving the invariant through the whole loop. |
| `Dynamic.lean` | Assembles the per-stage results above into readiness and dynamic clean-state preservation for the complete circuit: `gateWorkspaceCleanState_orderFindingApprox` and its packaged form `LoweredShorReady.workspace_clean`. |

## `Main.lean`

The three final Shor correctness theorems (`Shor_end_to_end_factoring`,
`Shor_correct_approx_lowered_uniform`, and the one in between), each typed by
its named proposition from `Spec/Assertions.lean` and proven from
`Proofs/Correctness.lean` and `Framework/Math/Factoring_Reduction/*`. Content
is byte-identical across this reorganization — only its import lines
changed. This is the file the `Reference/` implementations consume; all
supporting lemmas live under `Shor.Proofs`.
