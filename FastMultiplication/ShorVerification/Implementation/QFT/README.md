# `Implementation/QFT/`

This folder implements and proves correct the recursive **Quantum Fourier
Transform (QFT)**: splitting a register's QFT into two half-size recursive
QFTs joined by a phase-product macro and a radix reversal, the workspace
budget model for that recursion, and the lowering machinery that turns the
recursive plan into primitive `LowGate`s.

The folder is organized in layers (below). **Every import is "justified":** a
file may only import another file if it directly uses a declaration that file
defines — never a declaration it merely re-exports transitively.
`scripts/check_qft_layers.sh` (repo root) enforces both the layer order and
the absence of umbrella files (a file that only imports and declares nothing
of its own).

## Layer order

```
Split  <  Workspace  <  Lowering  <  Spec  <  Proofs  <  Main
```

A file may import its own folder or any folder to its left.

Reading order for newcomers: start at `Main.lean`, then follow imports
*backwards* — `Spec/Assertions.lean` for what is claimed,
`Proofs/Lowering/Readiness.lean` for how the claim is proved, and outward
from there into `Proofs/Decomposition.lean`, `Lowering/`, `Workspace.lean`,
`Split.lean` as needed. The one-line descriptions below are grouped in
dependency order (lowest layer first) to match that traversal.

## `Split.lean` — register-splitting convention

| File | Purpose |
|---|---|
| `Split.lean` | Fixes the low/right–high/left split convention (`splitM`, `halfSplitPoint`, `leftReg`, `rightReg`) and the small containment/disjointness facts (`leftReg_mem_parent`, `rightReg_mem_parent`, `disjoint_left_right`) used whenever the recursion reuses the same workspace pools on both halves. |

## `Workspace.lean` — the recursive workspace budget model

| File | Purpose |
|---|---|
| `Workspace.lean` | `qftWorkspaceNeed`: how large the two global reserve pools (x-side, z-side) must be for a register of a given width, accounting for the middle phase product and both recursive QFT calls. The public precondition on a single `ExtReg` (`QFTReserveOK`), the internal static condition on an already-selected pair of workspace registers (`QFTWorkspaceOK`), the monotonicity bounds letting a child reuse the same pools, and the constructions (`QFTWorkspaceOK.phaseWorkspace`, `.signedWorkspaceOK`, `.left`, `.right`) that carve those pools for the phase-product macro and for each recursive child. |

## `Lowering/` — turning a recursive QFT plan into a circuit

| File | Purpose |
|---|---|
| `Plan.lean` | `QFTLoweringPlan`: the finite certificate carried by the public lowerer — empty/singleton base cases and a recursive split case (carrying the phase-product workspace and subplan for the middle macro). `lowerQFTPlan`: the interpreter erasing such a plan to a `LowGate`. |
| `PlanBuilders.lean` | Builds plans rather than just interpreting them: `standardPhaseProdUsingPlan` (the canonical unsigned phase-product subplan used at each split, built by zero-extending both operands, lowering the resulting signed phase product, then deallocating the extensions), and the two public plan constructors `standardQFTLoweringPlan` (from explicit workspace registers satisfying `QFTWorkspaceOK`) and `reserveQFTLoweringPlan` (the bridge from the public reserve precondition `QFTReserveOK` to a concrete plan, deriving its workspace registers from `qftXWork`/`qftZWork`). |
| `Lower.lean` | `lowerQFT`: the final public constructor — the canonical lowered QFT circuit, its workspace selected deterministically from the reserve precondition rather than supplied separately. |

## `Spec/` — the public specification surface

| File | Purpose |
|---|---|
| `Cleanliness.lean` | The cleanliness predicates needed to state QFT workspace readiness: `Gate.PhaseProdWorkspace.CleanState` (the unsigned phase-product macro's own clean-workspace subspace) and `QFTWorkspaceCleanState`/`QFTWorkspaceStateOK` (the state-level precondition on the QFT lowerer's inactive register). |
| `Readiness.lean` | `QFTLoweringReady`: the semantic precondition required to execute a `QFTLoweringPlan` on a state — a split node needs the phase-product macro workspace clean, the right child's plan ready, and (after evaluating the right child and the phase gate) the left child's plan ready. |
| `Assertions.lean` | `LowerQFTCorrect` — the final claim: the canonical recursive lowering of a QFT gate has the same semantics as the high-level `Gate.QFT` gate, on states with valid, clean recursive workspace. Proved in `Main.lean`. |

## `Proofs/` — everything below is proof-only; nothing outside `Proofs/`/`Main.lean` may import it

| File | Purpose |
|---|---|
| `Decomposition.lean` | The high-level circuit identity: `Gate.QFT` on a register decomposes into a QFT on the right half, the unsigned phase-product macro, a QFT on the left half, and a radix reversal. See its own README for the exact statements. |
| `Lowering/` | Correctness of the plan/lowering machinery — see `Proofs/Lowering/README.md`. |

## `Main.lean`

Proves the folder's one public theorem, `lowerQFT_correct` (packaging
`Spec.Assertions.LowerQFTCorrect`), from `Proofs.Lowering.Readiness`'s
`evalL_lowerQFT`. Imports only `Spec.Assertions` and
`Proofs.Lowering.Readiness` — every other dependency is transitive through
those two.
