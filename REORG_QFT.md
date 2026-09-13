# REORG_QFT: restructure `Implementation/QFT/`

All paths below are relative to `FastMultiplication/ShorVerification/`. This plan reuses the
rules of `REORG.md` verbatim: **§1 ground rules** (pure move, one green build + one commit per
step, the two gates `lake build` + `#print axioms` on `Shor.Shor_correct` /
`Shor.exists_shorGateCountBound`, split only at existing banners, never change namespaces) and
**§3 justified-import rule** (no umbrella files; every `import M` must be justified by a direct
use of a declaration `M` itself defines). Read those two sections first.

## 0. Diagnosis

`Implementation/QFT/` is small (6 files, ~5.1k lines) and already has the right skeleton
(`Defs` / `Assertions` / `Main` / `Proofs`). Its problems are local:

1. **`Defs.lean` (1493 lines, 21 defs, 27 lemmas) is a concatenation of ten sections** that
   belong to four different layers: register splitting (§1), the plan language and interpreter
   (§2), readiness lemmas (§3), a plan *builder* for the unsigned macro (§4), the workspace
   budget model and predicates (§5–§6), ~375 lines of workspace helper lemmas and bounds
   (§7–§8), the child-workspace constructions (§9), and the canonical plans + `lowerQFT` (§10).
2. **`Defs.lean` imports a proof file** (`PhaseProduct.Proofs.Lowering.Linearity`) solely for
   two lemmas in §3 (`evalL_lowerQFTPlan_zero`, `QFTLoweringReady.zero`, l.197–264), which use
   `PhaseLoweringReady.zero` / `evalL_lowerGateRec_zero`. Those are proofs and belong in
   `Proofs/…/PlanSemantics.lean`, whose own §3 is already titled "Readiness linearity".
3. **`Shor/Defs.lean` (a definitions file) imports `QFT/Proofs/LoweringCorrectness/Readiness.lean`
   and uses nothing from it** — a stale import that makes a definitions module depend on a
   1071-line proof.
4. **`Proofs/LoweringCorrectness/PlanSemantics.lean` has its module docstring at line 251**, after
   a §1 that lives in a different namespace block (`GateSemanticsDissolvedQFT.QFTSemantics`) —
   two files were concatenated.
5. Naming drift vs. the reorganised `PhaseProduct/`: `Proofs/LoweringCorrectness/` should be
   `Proofs/Lowering/`; the state-level cleanliness predicates and `QFTLoweringReady` should sit
   in `Spec/` like their phase-product counterparts.

Not a problem (leave alone): the 7 `def`s inside `Proofs/Decomposition.lean` (`finMulAddEquiv`,
`nTot`, `mHalf`, `leftQFTReg`, `rightQFTReg`, `j0`, `j1`) and `QFTWorkspaceCleanState.rec'` in
`Readiness.lean` are proof-local vocabulary; nothing outside `Proofs/` uses them
(`leftQFTReg`/`rightQFTReg` are used by `PlanSemantics.lean`, also a proof). `Decomposition.lean`
is imported by `ModularExponentiation/Proofs/CmpLtNW.lean` for `exp_phaseProd_eq_qftPhase`,
`eval_sum_univ_qs`, `Clean.writeRight` — a justified proof-to-proof import. `nTot`/`mHalf`
duplicate `regSize`/`splitM`; do **not** dedup (pure move).

## 1. Target layout

Import direction is strictly downward. Nothing outside `Proofs/` imports `Proofs/`;
`Main.lean` imports `Spec/` and `Proofs/`.

```
Implementation/QFT/
  Split.lean              ← Defs.lean §1 (l.26–90) minus `Gate.PhaseProdWorkspace.CleanState`:
                              `splitM`, `halfSplitPoint`, `leftReg`, `rightReg`, `leftReg_mem_parent`,
                              `rightReg_mem_parent`, `disjoint_left_right`
  Workspace.lean          ← Defs.lean §5 (l.430) `qftWorkspaceNeed`;
                              §6 static part: `qftXWork` (l.479), `qftZWork` (l.491), `QFTReserveOK` (l.506),
                              `QFTWorkspaceOK` (l.558);
                              §7 (l.585) helper lemmas incl. `QFTReserveOK.explicitWorkspace` (l.768);
                              §8 (l.812) `qftWorkspaceNeed_*` bounds;
                              §9 (l.960) `Gate.PhaseProdWorkspace.ownedDisjoint_grow`, `QFTWorkspaceOK.phaseWorkspace`
                              (l.1016, DATA), `.signedWorkspaceOK` (l.1110), `.left` (l.1257), `.right` (l.1307)
  Lowering/
    Plan.lean             ← Defs.lean §2 (l.91–153): `QFTLoweringPlan`, `lowerQFTPlan`
    PlanBuilders.lean     ← Defs.lean §4 (l.266–429): `phaseProdUsingInputSize`, `standardPhaseProdUsingPlan`;
                              §10 (l.1357–1479): `standardQFTLoweringPlan`, `reserveQFTLoweringPlan`
    Lower.lean            ← Defs.lean l.1480–1493: `lowerQFT`
  Spec/
    Cleanliness.lean      ← Defs.lean l.67–77 `Gate.PhaseProdWorkspace.CleanState`;
                              §6 state part: `QFTWorkspaceCleanState` (l.523) with its `zero`/`ket`-style
                              lemmas in that block, `QFTWorkspaceStateOK` (l.539)
    Readiness.lean        ← Defs.lean l.154–189 `QFTLoweringReady` (the `noncomputable def` only)
    Assertions.lean       ← Assertions.lean (whole file)
  Proofs/
    Decomposition.lean    ← Proofs/Decomposition.lean (unchanged content)
    Lowering/PlanSemantics.lean ← Proofs/LoweringCorrectness/PlanSemantics.lean
                              + Defs.lean §3 (`evalL_lowerQFTPlan_zero`, `QFTLoweringReady.zero`) appended to its §3
                              "Readiness linearity"; module docstring moved to the top of the file (see step 4)
    Lowering/Readiness.lean     ← Proofs/LoweringCorrectness/Readiness.lean (unchanged content)
  Main.lean               UNCHANGED content; imports `Spec.Assertions`, `Proofs.Lowering.Readiness`
```

Deleted: `Defs.lean` (contents split; **no umbrella replaces it**), `Proofs/LoweringCorrectness/`.

Layer order for the check script (§4): `Split < Workspace < Lowering < Spec < Proofs < Main`.
(`Spec` is above `Lowering` because `QFTLoweringReady` mentions `lowerQFTPlan`; `Lowering` must
**not** import `Spec` — if the build says `standardQFTLoweringPlan` needs a `Spec` declaration,
stop and report: that declaration is a static predicate misfiled as state-level.)

## 2. External consumers — import rewrites

Current importers of `Implementation.QFT.*` outside the folder (find with
`grep -rn "Implementation.QFT" FastMultiplication --include="*.lean" | grep -v "Implementation/QFT/"`):

| Consumer | Today | After (justified) |
|---|---|---|
| `Shor/Defs.lean` | `QFT.Defs`, `QFT.Proofs.LoweringCorrectness.Readiness` | `QFT.Workspace` (`qftWorkspaceNeed`, `qftXWork`, `qftZWork`, `QFTReserveOK`), `QFT.Spec.Cleanliness` (`QFTWorkspaceCleanState`), `QFT.Lowering.Lower` (`lowerQFT`); **drop** the `Readiness` import (uses none of its 15 theorems) |
| `Shor/Proofs/Budgets.lean` | `QFT.Defs` | `QFT.Workspace` (`QFTWorkspaceOK.left`/`.right` and `qftWorkspaceNeed` bounds) — confirm by the §3 procedure of `REORG.md` |
| `Shor/Proofs/WholeProgramCorrectness.lean` | `QFT.Proofs.LoweringCorrectness.Readiness` | `QFT.Proofs.Lowering.Readiness` (`evalL_lowerQFT`) |
| `ModularExponentiation/Proofs/CmpLtNW.lean` | `QFT.Proofs.Decomposition` | unchanged (justified) |

Inside the folder, after step 3 every file imports the specific `QFT.*` and `PhaseProduct.*`
files it uses (today's `Defs.lean` already imports `PhaseProduct` by specific files — keep that
granularity; do not reintroduce a hub).

## 3. Migration order (one green build + one commit per step)

**Step 1 — move the two proof lemmas out of `Defs.lean`.** Cut `Defs.lean` §3 (l.190–264:
`evalL_lowerQFTPlan_zero`, `QFTLoweringReady.zero`) into
`Proofs/LoweringCorrectness/PlanSemantics.lean` at the end of its §3 "Readiness linearity"
(same `namespace Shor`; check `evalL_lowerQFTPlan_zero` is not needed earlier in that file — it
is used only by `QFTLoweringReady.zero`). Remove
`import …PhaseProduct.Proofs.Lowering.Linearity` from `Defs.lean`; `PlanSemantics.lean` already
imports it. Check with `grep -rw "QFTLoweringReady.zero\|evalL_lowerQFTPlan_zero"` that every
remaining user imports `PlanSemantics` (expected: `Readiness.lean` only). Build.

**Step 2 — create `Spec/`.**
- `git mv Assertions.lean Spec/Assertions.lean`; update `Main.lean`.
- `Spec/Readiness.lean` ← `QFTLoweringReady` (l.154–189). Imports: `QFT.Defs` for now (step 3
  replaces it with `Lowering.Plan`), `PhaseProduct.Spec.Readiness`, and `Spec.Cleanliness`.
- `Spec/Cleanliness.lean` ← `Gate.PhaseProdWorkspace.CleanState` (l.67–77, keep its
  `namespace Gate.PhaseProdWorkspace` block), `QFTWorkspaceCleanState` and the `theorem zero`
  beside it (l.523–~537), `QFTWorkspaceStateOK` (l.539–~557). Imports: `Implementation.Semantics.CleanClosure`,
  `PhaseProduct.Gates.Macros`, and (for now) `QFT.Defs` for `qftXWork`/`qftZWork` if
  `QFTWorkspaceStateOK` mentions them — step 3 turns that into `QFT.Workspace`.
- `Defs.lean` imports `Spec.Cleanliness` where the moved names are still used (§9/§10 should
  not need them; if they do, stop and report — a state predicate would be on the data path).
Build.

**Step 3 — split `Defs.lean`** into `Split.lean`, `Workspace.lean`, `Lowering/Plan.lean`,
`Lowering/PlanBuilders.lean`, `Lowering/Lower.lean` per §1, in that dependency order. Then
`git rm Defs.lean` and rewrite every `import …QFT.Defs` (inside and outside the folder) to the
defining files per §2 and the justified-import procedure. Build.

**Step 4 — `Proofs/LoweringCorrectness/` → `Proofs/Lowering/`** (`git mv` both files).
In `PlanSemantics.lean`, move the `/-! # QFT Lowering Plan Semantics … -/` module docstring
(currently l.251–261) to directly below the imports. This is a docstring *relocation*, not an
edit — allowed under REORG.md §1.7 because the move made its position wrong. Update `Main.lean`
and `Shor/Proofs/WholeProgramCorrectness.lean`. Build.

**Step 5 — imports and check script.**
- `Shor/Defs.lean`: drop the `QFT…Readiness` import; replace `QFT.Defs` per §2.
- Extend `scripts/check_phaseproduct_layers.sh` to take the subroutine root and its layer table
  as parameters (or add a sibling `check_qft_layers.sh` with layers
  `Split=1, Workspace=2, Lowering=3, Spec=4, Proofs=5, Main=6`); include the umbrella detector.
  Both roots must exit 0.
- Audit every file in `QFT/` against the justified-import rule.
Build. Run the axiom gate. Commit.

**Step 6 (optional, separate PR).** `Proofs/Decomposition.lean` §5 "Reindexing sums and cast
utilities" (l.908–982: `Asize_eq_lr`, `cast_arrow_apply`, `cast_app`, `fin_cast_eq_symm_formula`,
`fin_cast_eq_finMulAdd_formula`, `Fin.coe_cast_typeEq`) mentions no semantics and could become
`Math/FinCasts.lean`. Marginal; do it only if `Math/` is wanted for symmetry with `PhaseProduct/`.

## 4. Decisions recorded

- **No `Defs.lean` umbrella** — same decision and reason as `REORG.md` §6. `Shor/Defs.lean`
  ends up importing three `QFT` files; that is the documentation of its real dependencies.
- **`QFTWorkspaceOK.phaseWorkspace` stays in `Workspace.lean`** although it produces data
  (`Gate.PhaseProdWorkspace`): it is the QFT counterpart of `canonicalSignedStep`, which lives
  in `PhaseProduct/Compiler/Workspace.lean` for the same reason — it is the workspace *choice*,
  consumed by the plan builders above it.
- **`Gate.PhaseProdWorkspace.CleanState` stays in `QFT/Spec/Cleanliness.lean`** even though it
  is about a `PhaseProduct` macro: every user is a QFT file. Moving it to
  `PhaseProduct/Spec/Cleanliness.lean` would be equally correct; not done to keep this reorg
  inside `QFT/`.
- **Proof-local `def`s stay in `Proofs/`** (`rec'`, `leftQFTReg`, `rightQFTReg`, `finMulAddEquiv`,
  `nTot`, `mHalf`, `j0`, `j1`): the rule violated in `PhaseProduct/` was "definitions that
  non-proof files need live in `Proofs/`", which does not apply here.
- **`Main.lean` is byte-identical except its two `import` lines.**

## 5. Checklist

- [ ] Step 1: `Defs.lean` §3 lemmas moved to `PlanSemantics.lean`; `Defs.lean` imports no `Proofs/` file.
- [ ] Step 2: `Spec/{Assertions,Readiness,Cleanliness}.lean`.
- [ ] Step 3: `Split.lean`, `Workspace.lean`, `Lowering/{Plan,PlanBuilders,Lower}.lean`; `Defs.lean` deleted; no `…QFT.Defs` import anywhere.
- [ ] Step 4: `Proofs/Lowering/{PlanSemantics,Readiness}.lean`; docstring at top of `PlanSemantics.lean`.
- [ ] Step 5: `Shor/Defs.lean` no longer imports a QFT proof file; layer script covers `QFT/` and exits 0; nothing outside `Proofs/` imports `Proofs/`.
- [ ] After every step: `lake build` green; `#print axioms` on both headline theorems unchanged.
