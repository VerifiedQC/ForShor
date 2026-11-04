# `Implementation/PhaseProduct/`

This folder implements and proves correct the **phase-product** subroutine: the
recursive, chunked circuit that computes `exp(i·φ·x·z)` on two registers `x`, `z`
(signed and controlled-signed variants), the compiler that builds it from an
interpolation-based Toom-Cook decomposition, and the lowering machinery that
turns it into primitive `LowGate`s.

Lowering is parameterised by a **`ShorLoweringPolicy`**: a width-indexed
choice of Toom-Cook table, so a recursion can use a wide table at wide
operands and narrower ones as it descends. The familiar fixed-table names —
`StandardPhaseLoweringPlan`, `standardSignedPhaseLoweringPlan`,
`SignedRecursiveWorkspaceOK`, and every statement phrased with them — are the
**constant policy** on one table. See
the `Statement.lean` guide below for the plan type, the step/dispatcher split,
and the workspace model and why both spellings of it exist.

## Layout

```
PhaseProduct/
  Statement.lean   everything needed to state what Main.lean proves
  Proofs/          every lemma, the helper definitions only proofs use,
                   and the table generator (Proofs/Math/)
  Main.lean        the four correctness theorems, proved
```

`Statement.lean` imports nothing from `PhaseProduct/`; a reader can check the
claims in `Main.lean` against it alone. Layer order:

```
Statement  <  Proofs/Math  <  Proofs  <  Main
```

Other folders' `Statement.lean` files import only this `Statement.lean`.
Other folders' proofs may also import files under `Proofs/`.

Reading order for newcomers: `Main.lean` for what is proved, `Statement.lean`
for what the claims mean, then `Proofs/Lowering/Correctness.lean` and outward
for how.

## `Statement.lean`

Each section is the code of one former definition file. It holds exactly
what the four assertions need. The unsigned phase-product macros that the QFT
and modular-exponentiation statements use live in `QFT/Statement.lean`.

The definitions here are **plain data**. A split layout records its reserve
registers, `Policy.canonicalStep` is just the layout a recursive step uses,
and a plan node records its table and layout; none of them carries a proof about itself. The only proof
left in a structure is `PhaseSplitLayout.active_reserve_disjoint`, which
`ExtReg` itself requires. What the proofs need to know about these objects
(that a layout partitions the reserve, that a step fits in the workspace, that
the policy chose the step's table) is stated and proved in `Proofs/`, under
the workspace hypothesis the correctness theorems already assume. So the only
theorems left in this file are the few a definition uses: the planner's
termination lemma `phaseInputSize_target_le` (with the two width bounds it
rests on), the two `controlPhaseLeaves` identities `Policy.cStepPlan` casts
along, and `Policy.reserveNeed_const`, which `QFT/Statement.lean` uses.

In dependency order, ending with the assertions:

| Section | Contents |
|---|---|
| Layout | `LayoutState`, `WidthState`, `NeededWidths` and their bookkeeping; the top-heavy split parameters; the split interface (`PhaseSplitLayout`, `Gate.PhaseProductLayout`); `growExtRegTo`; `initSignedLayoutState`/`targetSignedLayoutState`; `ReserveBudget`. |
| Widths | `scanNeededWidths` (how wide each chunk's value grows over the source program), `phaseInputSize`, `nextSignedWidth`, and `phaseInputSize_target_le`: a child is never wider than `nextSignedWidth`, which is why the planner terminates. |
| Coefficients | The interpolation matrix and the computable Cramer coefficients (`interpMatrix`, `cramerCoeffFromPts`) the compiled phases use. |
| Compilation | `AnnotatedOp`, per-chunk allocation/deallocation gates, and the signed/controlled compilers `compileOpsToSignedGate`, `compileOpsToCSignedGate`, `controlPhaseLeaves`. |
| Workspace | The recursive reserve model `RecursivePhaseWorkspace.reserveNeed`, the static workspace predicates `SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`, and the reserve-budget construction (`PhaseSplitLayout.ofBudget`, `ReserveBudget.ofRequirements`). |
| The workspace model under a policy | `Policy.reserveNeed` (asks `P.choose` for each level's table), `Policy.WorkspaceOK`/`Policy.CWorkspaceOK`, and `Policy.canonicalStep`, the layout each recursive step uses. |
| Naive phase-product leaf | The base-case circuits `Naive_SignedPhaseProd`/`Naive_CSignedPhaseProd`, built from `signedBitWeight`/`signedTerms`. |
| Plans | `compiledSignedPhaseGate`/`compiledCSignedPhaseGate`, the plan language `PhaseLoweringPlan P`, its interpreter `lowerGateRec`, `StandardPhaseLoweringPlan`. |
| Plan builders | Allocation/deallocation and annotated-body plans, the one-level step `Policy.stepPlan`, the width dispatcher `Policy.signedPlanOf`/`Policy.signedPlan` (and controlled twins), and `standardSignedPhaseLoweringPlan`/`standardCSignedPhaseLoweringPlan`. |
| Entry points | `lowerSignedPhaseProd`/`lowerCSignedPhaseProd` and their `Policy.` forms: the lowered circuit of the canonical plan. They take no workspace argument; the workspace condition is a hypothesis of the correctness statements. |
| Cleanliness | `RecursiveWorkspaceCleanState` and the full workspace preconditions `SignedRecursiveWorkspaceStateOK`/`CSignedRecursiveWorkspaceStateOK`, with their policy forms. |
| Assertions | `LowerSignedPhaseProductCorrect`, `LowerCSignedPhaseProductCorrect` and their `Policy.` forms: the canonical lowered circuit evaluates exactly like `Gate.SignedPhaseProd` (resp. `CSignedPhaseProd`) on any state with a valid, clean workspace. |

Nothing else lives here: every definition that no statement needs, including
ones other folders' proofs or `Emit/` use, is in `Proofs/`.

### Notes on the design

**Plans are indexed by a policy.** A plan is parameterised by a
`ShorLoweringPolicy`, a width-indexed choice of Toom-Cook table, fixed for the
whole plan. A recursive node records the table it used and its layout; that
the policy chose that table at this width, that it shrinks the operands, and
that the layout fits are the node's `SignedStepOK` facts in
`Proofs/Spec/Readiness.lean`, and `PhaseLoweringPlan.Valid` says every node
satisfies them. The fixed-table names are the constant policy:
`StandardPhaseLoweringPlan k hk pts hpts ops` abbreviates
`PhaseLoweringPlan (constPolicy ⟨k, hk, pts, hpts, ops⟩)`.

**The planner needs no proofs.** `Policy.signedPlanOf P phi x z n` labels its
plan with the size `n` and its children with `nextSignedWidth`; recursion
terminates by `phaseInputSize_target_le`, which holds for every layout. So
`Policy.signedPlan` and the lowerers built on it take no workspace argument;
`Policy.signedPlan_valid` (in `Proofs/Lowering/PlanReadiness/PlanValid.lean`)
shows that the plan is valid whenever the workspace fits, from
`Policy.canonicalStep_spec`.

**The dispatcher takes the lookup as an argument.** `Policy.signedPlanOf` has
the shape `∀ o, P.choose (phaseInputSize x z) = o → PhaseLoweringPlan P …`
rather than a `match h : P.choose … with` in its body. The latter unfolds to an
`Option.casesOn` under an `Eq.ndrec` motive that `split` and `cases` cannot see
through; passing the result in keeps both branches reachable by `cases o`.

**Two spellings of the workspace model.** `Policy.reserveNeed` and
`Policy.WorkspaceOK` agree with the fixed-table `reserveNeed` and
`SignedRecursiveWorkspaceOK` at a constant policy only propositionally
(`reserveNeed_const`, `workspaceOK_const_iff`), which is why both exist.

**Coefficients compile fast but prove as Cramer.** `cramerCoeffFromPts` as code
is a `(2k-1)!`-term determinant. `gjCoeffFromPts` (in
`Proofs/Compiler/Coefficients.lean`) eliminates, verifies `M · M⁻¹ = I`, and
falls back to Cramer otherwise; its equality with Cramer is tagged `@[csimp]`,
so compiled code runs the cubic path while every proof still sees Cramer's
rule.

## `Proofs/` — every lemma, and the table generator

| File | Purpose |
|---|---|
| `NaiveLeaf.lean` | Correctness of the naive reference circuits defined in `Statement.lean`. Its apex theorems (`evalL_naive_signedPhaseProd_ket`, `gateCount_Naive_SignedPhaseProd`, and the controlled variants) are consumed by `Proofs/Lowering/EvalL.lean` and `GateCount/PhaseProduct/Lemmas.lean`, which is why they stay here rather than in `Main.lean`. |

### `Proofs/Compiler/` — correctness of the compiler

Internal order: `Support/WidthSoundness → Allocation/Body/Interpolation →
Compilation → Correctness` (each may import the ones before it).

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

### `Proofs/Lowering/` — correctness of the plan/lowering machinery

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
| `PlanReadiness/PlanValid.lean` | The builders and the dispatcher produce valid plans whenever the workspace fits (`Policy.signedPlan_valid`, `Policy.cSignedPlan_valid`). |
| `PlanReadiness/AllocDeallocReadiness.lean` | Allocation/deallocation chunks compile to primitive low gates, so their readiness proofs mostly transport across the plan constructors' definitional equalities. |
| `PlanReadiness/RecursiveReadiness.lean` | Assembles allocation + body readiness + recursive child readiness + deallocation into readiness for the canonical (un)controlled signed lowering plan; extends the basis-ket proof to arbitrary clean states by linearity. |
| `Correctness.lean` | The plan-level semantic bridge `Main.lean` packages into its final reader-facing statements. |

### The rest of `Proofs/`

| File | Purpose |
|---|---|
| `Compiler/Coefficients.lean` | The canonical points `alternatingPoint`/`genInterpolationPoints`, `phaseCoeffFromPts` and the Cramer equality, the `gjCoeffFromPts` fast path and its `@[csimp]` lemma, and `toMathPoint`, the bridge to `Proofs/Math/ToomCook.lean` that proves `genInterpolationPoints_good`. |
| `Compiler/GaussJordan.lean` | Exact elimination over `ℚ` (`matrixToRows`, `gaussJordanInverseRows`, `isRightInverseRows`) and `mul_rowsToMatrix_eq_one_of_isRightInverseRows`: a `true` from the check is the `Matrix` equation. |
| `Compiler/Compile.lean` | `phaseProductCount`, the number of phase-product leaves in a program. |
| `Compiler/Layout.lean`, `Compiler/Widths.lean`, `Compiler/Workspace.lean` | The layout invariants (`ValidPhaseSplit`, `PhaseSplitLayout.Valid`, `Gate.PhaseProductLayout.Valid`, `LayoutState.CanGrowTo`) and lemmas about the layout, width and reserve models of `Statement.lean`, including `PhaseSplitLayout.ofBudget_valid`. |
| `Compiler/PolicyWorkspace.lean` | `Policy.StepSpec` and `Policy.canonicalStep_spec`: under the workspace condition, the canonical step's layout is valid, every chunk can grow, and every child again has enough workspace at width `nextSignedWidth`. |
| `Gates/NaiveLeaf.lean` | The `ℂ`-valued term and exponent bookkeeping of the naive leaf, summed in `NaiveLeaf.lean`. |
| `Lowering/Plan.lean`, `Lowering/PlanBuilders.lean`, `Lowering/Lower.lean` | `generatedInterpolationPoints_length`; `planCompiledSignedPhaseGate`/`planCompiledCSignedPhaseGate` `standardSignedPhaseLoweringPlan_eq` (the fixed-table planner is the dispatcher at the constant policy) and `Policy.lowerGateRec_signedPlanOf_relabel` (the plan's size label does not affect the circuit). |
| `Spec/Cleanliness.lean` | `CompilerWorkspaceOK`, `CleanWorkspaceState`, `LayoutState.CleanForGrowth`, `LayoutReserveCleanBasis`/`LayoutReserveCleanState`, and the constant-policy forms of the workspace-state predicates. |
| `Spec/Readiness.lean` | `SignedStepOK`/`CSignedStepOK`, a recursive node's static facts; `PhaseLoweringPlan.Valid`; and `PhaseLoweringReady`, the precondition for running a plan on a state (a node's facts, a clean workspace, and a ready child). `QFT/` builds `QFTLoweringReady` from it. |

### `Proofs/Math/` — the table generator and the pure math

| File | Purpose |
|---|---|
| `ToomCook.lean` | Pure interpolation algebra: interpolation points, Vandermonde-style invertibility, radix reconstruction, and the exponential phase scalars from weighted point sums. |
| `MasterTheorem.lean` | The shifted scalar-recurrence envelope (master-theorem-style bound) used to derive the `O(n^(2+ε))` asymptotic gate-count result. |
| `Table_Generation.lean` | Umbrella re-exporting the whole table-generation development (see below). |
| `Table_Generation/` | **Self-contained subtree** with its own internal layering; nothing outside it should import anything but its existing public paths (`Proofs.Math.Table_Generation`, `Proofs.Math.Table_Generation.Generator`, `Proofs.Math.Table_Generation.Programs.WithProduct`). It synthesizes and certifies the concrete interpolation-point programs used by the compiler. Internal layout: |
| `Table_Generation/Core/Registers.lean` | Symbolic register/state model: shifts, negation, scaled addition, right-shift success. |
| `Table_Generation/Core/RegisterLemmas.lean` | First proof layer over that model: inverse-program facts, `run?` simp lemmas, state algebra, well-formed undo. |
| `Table_Generation/Core/Language.lean` | The table-generation program language: symbolic ops, partial execution semantics, point-row matchers, coverage predicates, notation. |
| `Table_Generation/Core/ListHelpers.lean` | Generic list lemmas used across the table-generation proofs. |
| `Table_Generation/Core/RunLemmas.lean` | Program-agnostic coverage/execution lemmas: coverage bookkeeping, composition under concatenation, the `NoPhase` framework. |
| `Table_Generation/Core/Coverage.lean` | Turns ordered point-consumption proofs into explicit phase-block decompositions and back into unordered `PhaseProductCoverage` proofs. |
| `Table_Generation/Core/Tactics.lean` | Tactic elaborators automating phase-product coverage / return-to-original-state checks, plus small example programs. |
| `Table_Generation/Builders/Fragments.lean` | Concrete program-fragment builders (`computeLocal*`, `addConst*`, …) and the per-point/whole-list generators built from them (`opsForPointWithProduct`, `genOpsWithProduct`). |
| `Table_Generation/Builders/FragmentLemmas.lean` | Correctness of those fragments. |
| `Table_Generation/Programs/WithProduct.lean` | Certifies `genOpsWithProduct` (defined in `Builders/Fragments.lean`) end to end: its two headline theorems (`genOpsWithProduct_returns_to_original`, `genOpsWithProduct_PhaseProductCoverage`). |
| `Table_Generation/Generator.lean` | Umbrella for the parity-reset generator (imports `Metrics` + `Correctness`). |
| `Table_Generation/Generator/Spec.lean` | `ProductMode` (phase product vs. triple product) and its point-count spec. |
| `Table_Generation/Generator/Defs.lean` | `streamPoint` (deterministic interpolation-point stream `0,∞,1,-1,2,-2,…`) and the generator built from it. |
| `Table_Generation/Generator/Precomputed.lean` | Precomputed `k=2`/`k=3` table-generator artifacts for both product modes. |
| `Table_Generation/Generator/Metrics.lean` | `arithmeticOperationCount`, `phaseProductCount` and other program size metrics. |
| `Table_Generation/Generator/WellFormed.lean` | Well-formedness lemmas for the generator's output programs. |
| `Table_Generation/Generator/Correctness.lean` | Correctness of the generator (e.g. `streamPoint_allowed`). |
| `Table_Generation/Generator/Examples.lean` | Utilities for inspecting generated point streams/programs (`ToString` instances, etc.). |
| `Table_Generation/Examples.lean` | Worked examples certified with the `Tactics.lean` elaborators, plus a few state-update helper lemmas. |


## `Main.lean`

Proves the two public headline theorems referenced throughout the rest of the
codebase (`#print axioms` gate target). Imports only `Statement` and
`Proofs.Lowering.Correctness` — every other dependency is transitive through
those two.

