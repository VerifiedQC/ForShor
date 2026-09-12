# `Implementation/PhaseProduct/`

This folder implements and proves correct the **phase-product** subroutine: the
recursive, chunked circuit that computes `exp(i·φ·x·z)` on two registers `x`, `z`
(signed and controlled-signed variants), the compiler that builds it from an
interpolation-based Toom-Cook decomposition, and the lowering machinery that
turns it into primitive `LowGate`s.

The folder is organized in layers (below). **Every import is "justified":** a
file may only import another file if it directly uses a declaration that file
defines — never a declaration it merely re-exports transitively.
`scripts/check_phaseproduct_layers.sh` (repo root) enforces both the layer
order and the absence of umbrella files (a file that only imports and
declares nothing of its own).

## Layer order

```
Math  <  Compiler  <  Gates  <  Lowering  <  Spec  <  Proofs  <  Main
```

A file may import its own folder or any folder to its left. `Math/Table_Generation/`
is a self-contained subtree with its own internal layering (see below) and is
exempt from this rule — treat it as a black box.

Reading order for newcomers: start at `Main.lean`, then follow imports
*backwards* — `Spec/Assertions.lean` for what is claimed, `Proofs/Lowering/Correctness.lean`
for how the claim is proved, and outward from there into `Proofs/`, `Lowering/`,
`Compiler/` as needed. The one-line descriptions below are grouped in
dependency order (lowest layer first) to match that traversal.

## `Math/` — pure math, no framework/register dependencies (besides `Table_Generation`)

| File | Purpose |
|---|---|
| `ToomCook.lean` | Pure interpolation algebra: interpolation points, Vandermonde-style invertibility, radix reconstruction, and the exponential phase scalars from weighted point sums. |
| `MasterTheorem.lean` | The shifted scalar-recurrence envelope (master-theorem-style bound) used to derive the `O(n^(2+ε))` asymptotic gate-count result. |
| `Table_Generation.lean` | Umbrella re-exporting the whole table-generation development (see below). |
| `Table_Generation/` | **Self-contained subtree** with its own internal layering; nothing outside it should import anything but its existing public paths (`Math.Table_Generation`, `Math.Table_Generation.Generator`, `Math.Table_Generation.Programs.WithProduct`). It synthesizes and certifies the concrete interpolation-point programs used by the compiler. Internal layout: |
| `Table_Generation/Core/Registers.lean` | Symbolic register/state model: shifts, negation, scaled addition, right-shift success. |
| `Table_Generation/Core/RegisterLemmas.lean` | First proof layer over that model: inverse-program facts, `run?` simp lemmas, state algebra, well-formed undo. |
| `Table_Generation/Core/Language.lean` | The table-generation program language: symbolic ops, partial execution semantics, point-row matchers, coverage predicates, notation. |
| `Table_Generation/Core/ListHelpers.lean` | Generic list lemmas used across the table-generation proofs. |
| `Table_Generation/Core/RunLemmas.lean` | Program-agnostic coverage/execution lemmas: coverage bookkeeping, composition under concatenation, the `NoPhase` framework. |
| `Table_Generation/Core/Coverage.lean` | Turns ordered point-consumption proofs into explicit phase-block decompositions and back into unordered `PhaseProductCoverage` proofs. |
| `Table_Generation/Core/Tactics.lean` | Tactic elaborators automating phase-product coverage / return-to-original-state checks, plus small example programs. |
| `Table_Generation/Builders/Fragments.lean` | Concrete program-fragment generators (`computeLocal*`, `addConst*`, …) and bridges between fold-based and recursive generators. |
| `Table_Generation/Builders/FragmentLemmas.lean` | Correctness of those fragments. |
| `Table_Generation/Programs/WithProduct.lean` | `genOpsWithProduct` and its two headline certification theorems (`_returns_to_original`, `_PhaseProductCoverage`). |
| `Table_Generation/Generator.lean` | Umbrella for the parity-reset generator (imports `Metrics` + `Correctness`). |
| `Table_Generation/Generator/Spec.lean` | `ProductMode` (phase product vs. triple product) and its point-count spec. |
| `Table_Generation/Generator/Defs.lean` | `streamPoint` (deterministic interpolation-point stream `0,∞,1,-1,2,-2,…`) and the generator built from it. |
| `Table_Generation/Generator/Precomputed.lean` | Precomputed `k=2`/`k=3` table-generator artifacts for both product modes. |
| `Table_Generation/Generator/Metrics.lean` | `arithmeticOperationCount`, `phaseProductCount` and other program size metrics. |
| `Table_Generation/Generator/WellFormed.lean` | Well-formedness lemmas for the generator's output programs. |
| `Table_Generation/Generator/Correctness.lean` | Correctness of the generator (e.g. `streamPoint_allowed`). |
| `Table_Generation/Generator/Examples.lean` | Utilities for inspecting generated point streams/programs (`ToString` instances, etc.). |
| `Table_Generation/Examples.lean` | Worked examples certified with the `Tactics.lean` elaborators, plus a few state-update helper lemmas. |

## `Compiler/` — the recursive phase-product compiler's definitions

Internal order: `Layout → Widths → Coefficients → Compile → Workspace` (each
may import the ones before it).

| File | Purpose |
|---|---|
| `Layout.lean` | `LayoutState`, `WidthState`, `NeededWidths` and their bookkeeping; top-heavy split parameters; the abstract `PhaseSplitLayout`/`Gate.PhaseProductLayout` split interface; `initSignedLayoutState`/`targetSignedLayoutState`/`growExtRegTo`/`ExtReg.CanGrowTo`/`LayoutState.CanGrowToNeeds`; `ReserveBudget`. |
| `Widths.lean` | Width scanning over a source program (`scanNeededWidths`), the recursion-size parameters (`phaseInputSize`, `nextSignedWidth`), and the lemmas connecting a scan back to the layout it was scanned from. |
| `Coefficients.lean` | Interpolation/phase-coefficient definitions (`interpMatrix`, `phaseCoeffFromPts`, `cramerCoeffFromPts`, …), the canonical interpolation points (`alternatingPoint`, `genInterpolationPoints`), and the bridge to the pure Toom-Cook math (`GoodToomCookPoints`, `toMathPoint`). |
| `Compile.lean` | The annotated-operation compiler: `AnnotatedOp`/`annotatePhaseTermsAux`, per-chunk allocation/deallocation gates, and the full signed/controlled-signed compilers (`compileOpsToSignedGate`, `compileOpsToCSignedGate`, `controlPhaseLeaves`, `Gate.PhaseProductLayout.ControlDisjoint`). |
| `Workspace.lean` | The recursive-workspace size model (`RecursivePhaseWorkspace.reserveNeed`), the static workspace-sufficiency predicates (`SignedRecursiveWorkspaceOK`, `CSignedRecursiveWorkspaceOK`), the concrete reserve-budget construction (`PhaseSplitLayout.ofBudget`, `ReserveBudget.ofRequirements`), and the canonical deterministic recursive step (`CanonicalSignedStep`, `canonicalSignedStep`). Top of the `Compiler/*` chain. |

## `Gates/` — circuit-macro definitions

| File | Purpose |
|---|---|
| `Macros.lean` | The unsigned/controlled phase-product macros (`PhaseProdWorkspace`, `PhaseProdUsing`, `CPhaseProdUsing`) — implementation-only circuit constructions the lowering/correctness proofs consume. Depends only on `Framework/`, not on `Compiler/`. |
| `NaiveLeaf.lean` | The reference (unoptimized) signed/controlled phase-product circuits (`Naive_SignedPhaseProd`, `Naive_CSignedPhaseProd`) and their `ℂ`-valued term/exponent bookkeeping. Correctness lemmas about these live in `Proofs/NaiveLeaf.lean`. |

## `Lowering/` — turning a compiled circuit into a certified plan

| File | Purpose |
|---|---|
| `Plan.lean` | Compiled gate packages (`compiledSignedPhaseGate`/`compiledCSignedPhaseGate`), the `PhaseLoweringPlan` inductive plan language, the interpreter `lowerGateRec`, and the standard interpolation-point public interface (`lowerSignedPhaseProd`, `lowerCSignedPhaseProd`). |
| `PlanBuilders.lean` | Allocation/deallocation plan builders, annotated-body plan builders, one-level compiled phase-product plans, and the canonical recursive planners `standardSignedPhaseLoweringPlan`/`standardCSignedPhaseLoweringPlan`. |
| `Lower.lean` | The two top-level lowered-circuit constructors from a root workspace assumption: `lowerSignedPhaseProdWithWorkspace`, `lowerCSignedPhaseProdWithWorkspace`. |

## `Spec/` — the public specification surface

| File | Purpose |
|---|---|
| `Cleanliness.lean` | The cleanliness predicates needed to state readiness/assertions: compiler-workspace cleanliness (`CompilerWorkspaceOK`, `CleanWorkspaceState`), layout reserve cleanliness, and cleanliness of the complete reserves (`RecursiveWorkspaceCleanState`, `SignedRecursiveWorkspaceStateOK`, `CSignedRecursiveWorkspaceStateOK`). |
| `Readiness.lean` | `PhaseLoweringReady`: the semantic precondition for executing a lowering plan on a state. `QFT/Defs.lean` needs this to *define* `QFTLoweringReady`, which is why it can't live in `Proofs/`. |
| `Assertions.lean` | The final named propositions the implementation claims to satisfy (proved in `Main.lean`). |

## `Proofs/` — everything below is proof-only; nothing outside `Proofs/`/`Main.lean` may import it

| File | Purpose |
|---|---|
| `NaiveLeaf.lean` | Correctness of the naive reference circuits in `Gates/NaiveLeaf.lean`. Its apex theorems (`evalL_naive_signedPhaseProd_ket`, `gateCount_Naive_SignedPhaseProd`, and the controlled variants) are consumed by `Proofs/Lowering/EvalL.lean` and `GateCount/PhaseProduct/Lemmas.lean`, which is why they stay here rather than in `Main.lean`. |

### `Proofs/Compiler/` — correctness of the compiler (`Compiler/`, `Gates/`)

Internal order: `Support/WidthSoundness → Allocation/Body/Interpolation →
Compilation → Correctness` (each may import the ones before it); `MacroSemantics`
stands slightly apart (see below).

| File | Purpose |
|---|---|
| `Support.lean` | Shared definitions/small lemmas for the gate-level proof: symbolic row semantics, encoding invariants, layout locality predicates, signed-width arithmetic. |
| `WidthSoundness.lean` | The width scan is large enough for every symbolic row value reached during execution (one-step preservation → prefix domination → allocation-facing soundness). |
| `Allocation.lean` | The allocation prefix copies each symbolic source chunk into the widened target layout (static arithmetic → freshness/disjointness → single-chunk → full allocation). |
| `Body/SingleStep.lean` | Slot disjointness and single-instruction correctness: layout disjointness ⟶ active-register disjointness, and that each compiled arithmetic instruction preserves the encoded symbolic state; plus outside-layout preservation for one step. |
| `Body/NoPhaseRuns.lean` | A no-phase segment is a sequence of arithmetic row updates; carries outside-layout preservation and encoded-state preservation through such a segment. |
| `Body/PhaseBlocks.lean` | After a no-phase prefix produces the matching row, the phase gate contributes exactly the prescribed scalar; block inductions compose those scalars across all interpolation points. |
| `Body/Controlled.lean` | `controlPhaseLeaves` only changes phase-product leaves — pushes it through compiled lists and shows purely arithmetic fragments are fixed; then the public body theorems (uncontrolled evaluates to the phase scalar, controlled evaluates to that scalar or identity). |
| `Body/Dealloc.lean` | Allocation followed by deallocation cancels slot-by-slot, transporting the proved body scalar back to the original input basis state. |
| `Interpolation.lean` | The algebraic identity behind compilation: reconstructing signed extended registers from split chunks, then turning accumulated Toom-Cook point phases into the final signed product phase. |
| `Compilation.lean` | Assembles allocation + body/deallocation + the Toom-Cook identity into the public correctness theorems for compiled signed/controlled circuits. |
| `Correctness.lean` | The apex gate-level results: compiled signed/controlled-signed gates evaluate as specified. This folder's public surface, consumed by `Proofs/Lowering/`. |
| `MacroSemantics.lean` | The `PhaseProdUsing`/`CPhaseProdUsing` semantic bridge: on a clean workspace, the macros contribute exactly the expected phase. |

### `Proofs/Lowering/` — correctness of the plan/lowering machinery (`Lowering/`, `Spec/`)

Internal order: `EvalL → Lowerable → PlanSemantics → Linearity → Workspace →
PlanReadiness/* → Correctness` (each may import the ones before it).

| File | Purpose |
|---|---|
| `EvalL.lean` | `evalL_*` rewrite lemmas unfolding `LowerGateClass.evalL` for each phase-product primitive — the simp library the rest of this folder builds on. |
| `Lowerable.lean` | `LowerablePhaseGate` and the `lowerable_*` lemmas showing every gate the compiler produces inhabits it. |
| `PlanSemantics.lean` | The core interpreter theorem: evaluating the low-level circuit selected by a ready plan agrees with the high-level gate stored in the plan; one-step semantic facts for compiled signed/controlled recursive nodes. |
| `Linearity.lean` | Lifts basis-level readiness/cleanliness proofs to arbitrary quantum states: phase products preserve clean recursive workspace, and plan evaluation/readiness respect zero/add/scalar-multiplication. |
| `Workspace.lean` | Moves reserve-cleanliness facts through the concrete layouts created by recursive lowering; shows signed allocation produces a fitted target encoding while keeping every child reserve clean for later recursive calls. |
| `PlanReadiness/BodyReadiness.lean` | Readiness for compiled bodies: no-phase prefixes thread readiness forward; block decompositions identify the basis state reached before each recursive phase leaf. |
| `PlanReadiness/AllocDeallocReadiness.lean` | Allocation/deallocation chunks compile to primitive low gates, so their readiness proofs mostly transport across the plan constructors' definitional equalities. |
| `PlanReadiness/RecursiveReadiness.lean` | Assembles allocation + body readiness + recursive child readiness + deallocation into readiness for the canonical (un)controlled signed lowering plan; extends the basis-ket proof to arbitrary clean states by linearity. |
| `Correctness.lean` | The plan-level semantic bridge `Main.lean` packages into its final reader-facing statements. |

## `Main.lean`

Proves the two public headline theorems referenced throughout the rest of the
codebase (`#print axioms` gate target). Imports only `Spec.Assertions` and
`Proofs.Lowering.Correctness` — every other dependency is transitive through
those two.
