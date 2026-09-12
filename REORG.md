# REORG: restructure `Implementation/PhaseProduct/`

All paths below are relative to `FastMultiplication/ShorVerification/`.

## 0. Purpose and scope

`Implementation/PhaseProduct/` (45 files, ~33k lines) grew by concatenation. The
problems this reorg fixes are structural:

1. **Definitions live under `Proofs/`.** The macro gates every other subroutine uses
   (`PhaseProdWorkspace`, `PhaseProdUsing`, `CPhaseProdUsing`), the lowering leaf
   (`Naive_SignedPhaseProd`, `CPhase`), the readiness predicate `PhaseLoweringReady`
   (needed by `QFT/Defs.lean` to *define* `QFTLoweringReady`), and ~20 more `def`s sit in
   proof files. So definition files import proof files, and outside subroutines import six
   different internal proof files.
2. **`DefsCore.lean` (2212 lines) is a concatenation** — its section numbers run
   1–8, 1, 2, 6, 8, 4, 5, 6, 7, 8. It mixes a generic `CleanClosure` used by QFT/Shor/ModExp,
   the compiler, 45 support lemmas, the workspace size model, `canonicalSignedStep`, and
   cleanliness predicates.
3. **A 3366-line general gate-semantics library** (`GateSemanticsLemmas.lean`) is filed as a
   phase-product proof; only two theorems in it (`eval_PhaseProdUsing_ket`,
   `eval_CPhaseProdUsing_ket`, lines ~1359–1496) are about phase products.
4. Naming: three files called `Main.lean`; `Toom_Cook_formula`, `MasterTheoremProof` vs.
   CamelCase everywhere else.

**Out of scope — do not touch:** `Math/Table_Generation/` (all 22 files, both umbrellas
`Math/Table_Generation.lean` and `Math/Table_Generation/Generator.lean`, and every import
line inside that subtree). Its internal layering has known oddities; they are deliberately
left alone in this reorg. Files *outside* it keep importing it exactly as they do today.

**Invariant of the whole reorg: this is a pure move.** No statement changes, no proof
changes, no renames of declarations. Only: `git mv`, splitting a file at an existing
`/-! === Section` banner, editing `import` lines, and adding/removing `namespace … end`
wrappers where a split forces it. `Main.lean` keeps the two final theorems, unchanged.

## 1. Ground rules for the agent

1. Work on a branch (`git checkout -b phaseproduct-reorg`); the tree must be clean and
   `lake build` green before starting.
2. **Every numbered step in §5 ends with a green `lake build` and one commit.** If a step
   turns red, fix imports until green; never touch a proof body to make a step pass. If a
   proof genuinely breaks because a `simp` set changed (it shouldn't — nothing is renamed),
   stop and report.
3. **Two gates after every step:**
   `lake build` and
   `#print axioms Shor.Shor_correct` / `#print axioms Shor.exists_shorGateCountBound`
   (must stay `[propext, Classical.choice, Quot.sound]`). Put these two `#print axioms`
   lines in a scratch file and run `lake env lean scratch.lean`.
4. **Splitting a file:** copy the slice verbatim (including its `open`/`variable`/`section`
   lines and any `private` helpers it uses), give the new file the imports it needs (start
   with the old file's import list, then prune), wrap in the same `namespace`. A `private`
   declaration used by two slices must be de-privatised (this is the one allowed textual
   change; note it in the commit message).
5. **Moving a declaration between namespaces is forbidden.** If a slice lives inside
   `namespace GateSemanticsFacts … end` in the old file, it lives inside the same namespace
   in the new file.
6. **Layer rule (§4).** After the last step the check script must pass. Run it after every
   step anyway so regressions are visible.
7. Do not "improve" while moving: no reformatting, no docstring edits beyond fixing a path
   that the move made wrong, no dedup. The two `Point` types (`Operations.Point` vs
   `ToomCookMath.Point`) and the `interpMatrix`/`interpEntry` pair are *deliberate* per
   `RESTRUCTURE_PLAN.md`, bridged by `phaseCoeffFromPtsWidth_eq_interpCoeff`.

## 2. Target layout

Import direction is strictly downward in this listing. Nothing outside `Proofs/` imports
`Proofs/`; `Main.lean` imports `Proofs/` and `Spec/`.

```
Implementation/Semantics/                       NEW — shared by all subroutines (peer of Implementation/RegisterLemmas.lean)
  CleanClosure.lean                               ← DefsCore.lean lines 22–44 (`CleanClosure` and its constructors)
  GateSemanticsLemmas.lean                        ← Proofs/GateLevelCorrectness/GateSemanticsLemmas.lean minus the two PhaseProdUsing theorems

Implementation/PhaseProduct/
  Math/
    ToomCook.lean                                 ← Math/Toom_Cook_formula.lean   (rename only)
    MasterTheorem.lean                            ← Math/MasterTheoremProof.lean  (rename only)
    Table_Generation.lean, Table_Generation/…     UNCHANGED (out of scope)
  Compiler/                                      ← DefsCore.lean, split at its banners
    Layout.lean         §1 (l.64) Layout states & width bookkeeping, §2 (l.140) split parameters, §3 (l.160) ExtReg split interface, `ReserveBudget` (l.529–540), §7 defs `initSignedLayoutState`, `targetSignedLayoutState`, `growExtRegTo`, `ExtReg.CanGrowTo`, `LayoutState.CanGrowToNeeds`
    Widths.lean         §4 (l.225) width scanning, `phaseInputSize`, `nextSignedWidth` (l.302–305), support §2 (l.612) width scans & signed-fit safety, support §6 (l.1218) scan consequences
    Coefficients.lean   §5 (l.251) interpolation & phase coefficients incl. `lagrangeCoeff`, support §8 (l.1326) canonical interpolation points (`alternatingPoint`, `genInterpolationPoints`, …), `GoodToomCookPoints` + `toMathPoint` (from SupportLemmas l.984–1000)
    Compile.lean        §6 (l.325) annotated ops & `phaseProductCount`, §7 (l.393–440) alloc/dealloc gates & `compileSigned(De)Allocations*`, §8 (l.460) `compileAnnotatedOpsToSignedGateAux`, `compileOpsToSignedGate`, `controlPhaseLeaves`, `compileOpsToCSignedGate`, `Gate.PhaseProductLayout.ControlDisjoint`, support §1 (l.575) annotation lemmas
    Workspace.lean      block l.1340–1417 (`PhaseSplitLayout.ofBudget` etc.), §4 (l.1426) `RecursivePhaseWorkspace` size model, §5 (l.1578) `SignedRecursiveWorkspaceOK`, §6 (l.1602) `requiredChildReserve`, `ReserveBudget.ofRequirements`, `CanonicalSignedStep`, `canonicalSignedStep`, `CSignedRecursiveWorkspaceOK` (l.2121)
  Gates/
    Macros.lean         ← Proofs/GateLevelCorrectness/GateConstructions.lean (whole file)
    NaiveLeaf.lean      ← Proofs/NaivePhaseProduct.lean lines 1–101 (defs: `sequence`, `CPhase`, `signedBitWeight`, `signedTermsAux`, `signedTerms`, `signedPairAngle`, `naiveSignedPhaseGates`, `Naive_SignedPhaseProd`, `basisBitInt`, `signedTermValue`, `signedPairExponent`, `naiveSignedPhaseExponents`) ++ Proofs/NaiveCPhaseProduct.lean lines 1–45 (`CCPhase`, `naiveCSignedPhaseGates`, `Naive_CSignedPhaseProd`) and its two `noncomputable def`s at l.177/189
  Lowering/
    Plan.lean           ← PhaseLoweringPlan.lean §1 (l.17) compiled gate packages, §2 (l.76) plan language, §3 (l.220) `lowerGateRec`, §4 (l.262) standard interface
    PlanBuilders.lean   ← PhaseLoweringPlan.lean §5 (l.336) alloc/dealloc plan builders, §6 (l.472) annotated body builders, §7 (l.582) one-level plans, §8 (l.745) `standardSignedPhaseLoweringPlan`, `standardCSignedPhaseLoweringPlan`
    Lower.lean          ← Defs.lean body (`lowerSignedPhaseProdWithWorkspace`, `lowerCSignedPhaseProdWithWorkspace`)
  Spec/
    Cleanliness.lean    ← DefsCore §7 (l.2147) `RecursiveWorkspaceCleanBasis/State`, §8 (l.2174) `SignedRecursiveWorkspaceStateOK`, `CSignedRecursiveWorkspaceStateOK`; SupportLemmas l.140–160 `LayoutState.CleanForGrowth`, `CompilerWorkspaceOK`, `CleanWorkspaceState`; Linearity l.64–88 `LayoutReserveCleanBasis`, `LayoutReserveCleanState`
    Readiness.lean      ← PlanSemantics.lean l.28 `PhaseLoweringReady` (the `noncomputable def`, nothing else)
    Assertions.lean     ← Assertions.lean (whole file)
  Proofs/
    NaiveLeaf.lean                 ← rest of NaivePhaseProduct.lean (from l.103) ++ rest of NaiveCPhaseProduct.lean (from l.46); its apex theorems (`evalL_naive_signedPhaseProd_ket`, `gateCount_Naive_SignedPhaseProd`, `evalL_naive_csignedPhaseProd_ket`, `gateCount_Naive_CSignedPhaseProd`) stay here — they are consumed by `Proofs/Lowering/EvalL.lean` and `GateCount/PhaseProduct/Lemmas.lean`
    Compiler/Support.lean          ← GateLevelCorrectness/SupportLemmas.lean minus the defs moved to Spec/Cleanliness and Compiler/Coefficients
    Compiler/WidthSoundness.lean   ← GateLevelCorrectness/WidthSoundness.lean
    Compiler/Allocation.lean       ← GateLevelCorrectness/AllocationCorrectness.lean
    Compiler/Body.lean             ← GateLevelCorrectness/BodyCorrectness.lean
    Compiler/Interpolation.lean    ← GateLevelCorrectness/InterpolationCorrectness.lean
    Compiler/MacroSemantics.lean   ← GateSemanticsLemmas.lean `eval_PhaseProdUsing_ket`, `eval_CPhaseProdUsing_ket` (l.1359–1496, inside `namespace GateSemanticsFacts`)
    Compiler/Compilation.lean      ← GateLevelCorrectness/CompilationCorrectness.lean
    Compiler/Correctness.lean      ← GateLevelCorrectness/Main.lean
    Lowering/EvalL.lean            ← LoweringCorrectness/EvalLLemmas.lean
    Lowering/Lowerable.lean        ← LoweringCorrectness/Lowerable.lean
    Lowering/PlanSemantics.lean    ← LoweringCorrectness/PlanSemantics.lean minus `PhaseLoweringReady`
    Lowering/Linearity.lean        ← LoweringCorrectness/Linearity.lean minus the two cleanliness defs
    Lowering/Workspace.lean        ← LoweringCorrectness/Workspace.lean
    Lowering/PlanReadiness.lean    ← LoweringCorrectness/PlanReadiness.lean
    Lowering/Correctness.lean      ← LoweringCorrectness/Main.lean
  (no Defs.lean)        DELETED in step 6 — there are no umbrella files; consumers import the file that defines what they use (§3)
  Main.lean             UNCHANGED content; imports `Spec.Assertions` and `Proofs.Lowering.Correctness` (+ `Proofs.Compiler.Correctness` if the `simpa` set needs it — it currently does via the old import chain)
```

Deleted after the move: `DefsCore.lean`, `PhaseLoweringPlan.lean` (contents split), `Defs.lean`
(was a one-line re-export of `Lowering.Lower` after step 4 — an umbrella),
`Proofs/GateLevelCorrectness/`, `Proofs/LoweringCorrectness/`, `Proofs/Naive*PhaseProduct.lean`.

## 3. External consumers — import rewrites

**No umbrella imports.** There is no `Defs.lean`. The rule for every `import` line, inside or
outside `PhaseProduct/`, is the *justified-import rule*: an import of module `M` is allowed only
if the importing file uses **directly** (by name, in its own text) at least one declaration
that `M` itself defines. Relying on `M`'s transitive imports to bring in a name you use is
not allowed — import the defining file too. (Lean does not warn about unused imports, so this
is enforced by reading, not by the compiler.) The only exception is `Math.Table_Generation*`,
which is out of scope and keeps whatever imports it has today.

After step 6 the file `Defs.lean` no longer exists, so every `import …PhaseProduct.Defs` line
must be replaced. The table below was produced by scanning each consumer for identifiers
defined in the new definition files; it is a **starting point**, not the final answer, because
the scan misses namespace-qualified uses (e.g. `Gate.PhaseProdWorkspace.ofExtRegs`). Procedure
per consumer: (1) replace `Defs` with the imports listed; (2) build; (3) add the defining file
for any name the compiler reports unknown; (4) finally `grep` the file for one declaration from
each imported module and delete any import that has none.

| Consumer | Replace `Defs` (and old proof imports) with |
|---|---|
| `GateCount/Definitions.lean` | `Compiler.Coefficients` (`GoodToomCookPoints`, `genInterpolationPoints`), `Compiler.Compile` (`phaseProductCount`), `Compiler.Layout` (`NeededWidths`, `WidthState`), `Compiler.Workspace` (`(C)SignedRecursiveWorkspaceOK`), `Lowering.Lower` |
| `GateCount/PhaseProduct/Lemmas.lean` | `Compiler.{Coefficients,Compile,Layout,Widths,Workspace}`, `Gates.Macros`, `Lowering.{Lower,Plan,PlanBuilders}`, `Math.MasterTheorem`, `Math.ToomCook`, `Proofs.NaiveLeaf` (already present) |
| `GateCount/PhaseProduct/Main.lean` | `Compiler.Compile`, `Compiler.Widths`, `Compiler.Workspace` |
| `GateCount/QFT_GateCount.lean` | `Compiler.Layout` (`PhaseSplitLayout.child`), `Compiler.Workspace`, `Lowering.Lower`, `Lowering.Plan` (`lowerGateRec`) |
| `GateCount/Shor_GateCount.lean` | `Compiler.Coefficients` (`genInterpolationPoints_good`) + whatever the compiler asks for |
| `ModularExponentiation/Defs.lean`, `ModularExponentiation/CmpLtNW.lean` | `Gates.Macros` (`Gate.PhaseProdWorkspace`, `PhaseProdUsing`, `CPhaseProdUsing`) — `CmpLtNW.lean` already has it; drop `Defs` |
| `ModularExponentiation/Proofs/{Core,Step1Bound,Step1QPE,Step2Bound,Algorithm1Expansion}.lean` | `Gates.Macros`; `Step1QPE` also `Compiler.Layout` (`ReserveBudget.offset`); keep existing `Proofs.Compiler.MacroSemantics` / `Proofs.Lowering.Workspace` (proof-to-proof, justified by `eval_PhaseProdUsing_ket` / `FreshZero.of_subset`) |
| `ModularExponentiation/Proofs/ConstArithmeticLowering.lean` | keep `Proofs.Lowering.EvalL` (justified); add `Gates.Macros` only if the compiler asks |
| `QFT/Defs.lean` | `Compiler.Layout`, `Compiler.Widths` (`phaseInputSize`), `Compiler.Workspace`, `Gates.Macros` (`xExt`, `zExt`, `Clean`), `Lowering.Plan`, `Lowering.PlanBuilders` (`standardSignedPhaseLoweringPlan`), `Spec.Readiness` (`PhaseLoweringReady`); keep `Proofs.Lowering.Linearity` (justified: `PhaseLoweringReady.zero`, `evalL_lowerGateRec_zero`) |
| `QFT/Proofs/Decomposition.lean` | `Gates.Macros`; keep `Proofs.Compiler.MacroSemantics` |
| `QFT/Proofs/LoweringCorrectness/PlanSemantics.lean` | `Compiler.Coefficients`, `Lowering.Plan`, `Spec.Readiness`; keep `Proofs.Lowering.Linearity` |
| `QFT/Proofs/LoweringCorrectness/Readiness.lean` | `Compiler.Coefficients`, `Compiler.Workspace`, `Gates.Macros`, `Lowering.Plan`, `Lowering.PlanBuilders`, `Spec.Cleanliness`, `Spec.Readiness`; keep `Proofs.Compiler.MacroSemantics`, `Proofs.Lowering.PlanReadiness` |
| `Reference/StandardLoweringSetup.lean` | `Compiler.Coefficients` (`genInterpolationPoints`) in addition to the unchanged `Math.Table_Generation.Programs.WithProduct` |
| `Shor/Defs.lean` | `Compiler.Coefficients`, `Compiler.Workspace`, `Gates.NaiveLeaf` (`LowGate.sequence`), `Lowering.Lower`, `Lowering.PlanBuilders`, `Spec.Cleanliness`; keep `Main`; **drop** `Proofs.Lowering.Workspace` (uses nothing from it) |
| `Shor/Proofs/Budgets.lean` | keep `Proofs.Lowering.Workspace` (`FreshZero.of_subset`); add `Compiler.Workspace`/`Spec.Cleanliness` only if the compiler asks |
| `Shor/Proofs/Readiness.lean` | `Compiler.Workspace`, `Gates.Macros`, `Spec.Cleanliness`; keep `Proofs.Compiler.MacroSemantics` |
| `Shor/Proofs/WholeProgramCorrectness.lean` | `Compiler.Coefficients`, `Compiler.Workspace`, `Lowering.Lower`, `Spec.Cleanliness`; keep `Main` |
| any file using `CleanClosure` directly | `Implementation.Semantics.CleanClosure` |

Find any consumer this table missed with
`grep -rn "Implementation.PhaseProduct" FastMultiplication --include="*.lean" | grep -v "Implementation/PhaseProduct/"`,
and confirm no `Defs` import survives with
`grep -rn "Implementation.PhaseProduct.Defs$" FastMultiplication --include="*.lean"`.

The same justified-import rule applies **inside** `PhaseProduct/`: after step 6, audit every
file's imports the same way (steps 3–4 left several files importing `Compiler.Workspace` or
`Lowering.Lower` "for now" as the top of the chain — replace those with the defining files).

## 4. Allowed-import matrix and check script

Folder order (a file may import from its own folder or any folder to its **left**):

```
Semantics(shared)  <  Math  <  Compiler  <  Gates  <  Lowering  <  Spec  <  Proofs  <  Main
```

Additional constraints:
- `Math/*` imports nothing from this subroutine outside `Math/` (Mathlib and `Framework/` only).
- `Math/Table_Generation/**` is a frozen subtree: the script treats all of it as layer `Math`
  and does **not** inspect imports between its own files.
- **No umbrella files.** A file whose content is only `import` lines (no declarations) is an
  umbrella and is forbidden; the script flags it. Every import must satisfy the justified-import
  rule of §3.
- Inside `Proofs/`: `NaiveLeaf < Compiler/* < Lowering/*`; and within each, the order in §2.

Add `scripts/check_phaseproduct_layers.sh` (run from repo root; exit 1 on violation):

```sh
#!/usr/bin/env bash
# Asserts that every file under Implementation/PhaseProduct imports only from folders at or
# below its own layer. Pure moves must keep this green from the last step on.
set -euo pipefail
root=FastMultiplication/ShorVerification/Implementation/PhaseProduct
prefix=FastMultiplication.ShorVerification.Implementation.PhaseProduct.
layer() { case "$1" in
  Math*) echo 1;; Compiler*) echo 2;; Gates*) echo 3;;
  Lowering*) echo 4;; Spec*) echo 5;; Proofs*) echo 6;; Main) echo 7;; *) echo 9;; esac; }
status=0
while IFS= read -r f; do
  mod=${f#$root/}; mod=${mod%.lean}; mod=${mod//\//.}
  case "$mod" in Math.Table_Generation*) continue;; esac   # frozen subtree, not inspected
  # umbrella detector: a file with imports but no declarations of its own
  if grep -qE '^import ' "$f" && ! grep -qE '^(noncomputable def|def|abbrev|structure|inductive|class|instance|theorem|lemma|@\[|macro|elab|syntax)' "$f"; then
    echo "UMBRELLA FILE: $mod"; status=1
  fi
  me=$(layer "$mod")
  while IFS= read -r imp; do
    dep=${imp#$prefix}; dl=$(layer "$dep")
    if [ "$dl" -gt "$me" ]; then echo "LAYER VIOLATION: $mod imports $dep"; status=1; fi
  done < <(grep -oE "^import ${prefix}[A-Za-z0-9_.]+" "$f" | sed 's/^import //')
done < <(find "$root" -name '*.lean')
exit $status
```

(`Spec` above `Lowering` is deliberate: `Spec/Readiness` mentions `lowerGateRec`, and
`Spec/Assertions` mentions `lowerSignedPhaseProdWithWorkspace`.)

## 5. Migration order (one green build + one commit per step)

Do the steps in this order; each is chosen so the previous step's structure is not touched again.

**Step 1 — extract the shared pieces to `Implementation/Semantics/`.**
1a. Create `Implementation/Semantics/CleanClosure.lean` with `DefsCore.lean` lines 22–44
    (the `CleanClosure` inductive and everything in that `namespace Shor … end Shor` block).
    `DefsCore.lean` imports it. Build.
1b. `git mv Proofs/GateLevelCorrectness/GateSemanticsLemmas.lean Implementation/Semantics/GateSemanticsLemmas.lean`.
    Cut `eval_PhaseProdUsing_ket` and `eval_CPhaseProdUsing_ket` (l.1359–1496; keep them inside
    `namespace GateSemanticsFacts`) into a new
    `PhaseProduct/Proofs/GateLevelCorrectness/MacroSemantics.lean` importing
    `GateConstructions` and `Implementation.Semantics.GateSemanticsLemmas`. Replace the moved
    file's `import …PhaseProduct.Defs` / `…GateConstructions` with what the compiler still
    requires (expected: `Framework.Semantics.*`, `Implementation.RegisterLemmas`,
    `Implementation.Semantics.CleanClosure`; if it also needs a `PhaseProduct` definition,
    stop and report which one — that means a declaration is misfiled). Rewrite all 12 external
    importers per §3. Build.

**Step 2 — move definitions out of `Proofs/`.**
- `git mv Proofs/GateLevelCorrectness/GateConstructions.lean Gates/Macros.lean`.
- Split `Proofs/NaivePhaseProduct.lean` at l.103 and `Proofs/NaiveCPhaseProduct.lean` at l.46:
  defs → `Gates/NaiveLeaf.lean` (one file; keep both `namespace LowGate` blocks), lemmas →
  `Proofs/NaiveLeaf.lean`. `PhaseLoweringPlan.lean` now imports `Gates.NaiveLeaf`, not a proof file.
- Create `Spec/Readiness.lean` with `PhaseLoweringReady` (PlanSemantics l.28–~80); PlanSemantics imports it.
- Create `Spec/Cleanliness.lean` with DefsCore §7–§8 (l.2147–2212), SupportLemmas
  l.140–160 (`LayoutState.CleanForGrowth`, `CompilerWorkspaceOK`, `CleanWorkspaceState`), and
  Linearity l.64–88 (`LayoutReserveCleanBasis`, `LayoutReserveCleanState`). The three source
  files import it.
- `git mv Assertions.lean Spec/Assertions.lean`; `Main.lean` import updated.
Build.

**Step 3 — split `DefsCore.lean` into `Compiler/*`** per the §2 table, in dependency order
`Layout → Widths → Coefficients → Compile → Workspace`. Move `GoodToomCookPoints`/`toMathPoint`
from SupportLemmas into `Compiler/Coefficients.lean` in the same step (they are used by
`Main.lean` and `GateCount/Definitions.lean`). Every former importer of `DefsCore` imports
`Compiler.Workspace` (the top of the chain) for now; step 6 replaces that with justified
imports of the defining files. Delete `DefsCore.lean`. Build.

**Step 4 — split `PhaseLoweringPlan.lean` and `Defs.lean`.** §1–§4 → `Lowering/Plan.lean`;
§5–§8 → `Lowering/PlanBuilders.lean`; `Defs.lean` body → `Lowering/Lower.lean`. `Defs.lean`
is temporarily a one-line re-export of `Lowering.Lower` so external consumers keep building;
step 6 deletes it. Build.

**Step 5 — renames and folder moves** (all `git mv`, then fix imports):
- `Math/Toom_Cook_formula.lean → Math/ToomCook.lean`; `Math/MasterTheoremProof.lean → Math/MasterTheorem.lean`.
  (`Math/Table_Generation*` is not touched.)
- `Proofs/GateLevelCorrectness/ → Proofs/Compiler/` with renames (`SupportLemmas → Support`,
  `AllocationCorrectness → Allocation`, `BodyCorrectness → Body`, `InterpolationCorrectness → Interpolation`,
  `CompilationCorrectness → Compilation`, `Main → Correctness`; `MacroSemantics` keeps its name).
- `Proofs/LoweringCorrectness/ → Proofs/Lowering/` (`EvalLLemmas → EvalL`, `Main → Correctness`).
Build.

**Step 6 — remove the umbrella, justify every import, add the check script.**
- Rewrite every external `import …PhaseProduct.Defs` per the §3 table and procedure
  (replace, build, add what the compiler asks for, then delete imports that define nothing the
  file uses). Do the same for the old proof imports listed there.
- `git rm Implementation/PhaseProduct/Defs.lean`. Build; run both `grep`s in §3 — no `Defs`
  import may survive anywhere.
- Audit imports **inside** `PhaseProduct/` by the same justified-import rule, in particular the
  "top of the chain" imports left by steps 3–4 (`Compiler.Workspace`, `Lowering.Lower`).
- Fix internal imports so that nothing outside `Proofs/`/`Main.lean` imports `Proofs/`.
- Add `scripts/check_phaseproduct_layers.sh` (§4); it must exit 0 — this includes the
  umbrella detector.
Build. Run the axiom gate. Commit.

**Step 7 (optional, separate PR).** Split `Proofs/Compiler/Body.lean` (3097 lines) and
`Proofs/Lowering/PlanReadiness.lean` (2750 lines) along their own docstring structure
(Body: single-instruction facts / no-phase runs / phase blocks / controlled variant / dealloc;
PlanReadiness: body readiness / alloc-dealloc readiness / lift to states). Same rules apply.

## 6. Decisions recorded

- **No umbrella files, no umbrella imports.** `Defs.lean` is deleted rather than turned into
  a re-export hub; every import names the file that defines something the importer uses
  (§3 justified-import rule). Reason: an umbrella hides the real dependency graph — a consumer
  that imports "everything" can never be told what it actually depends on, and the layer check
  becomes meaningless. The cost is a few more import lines per consumer, which is the point:
  they document the dependency. (`Math/Table_Generation.lean` and `…/Generator.lean` are
  pre-existing umbrellas inside the frozen subtree and are left alone.)
- **`Math/Table_Generation/` is out of scope.** Its files, umbrellas, and internal imports are
  left exactly as they are; it is imported from outside by its existing paths.
- **The naive-leaf correctness theorems stay in `Proofs/NaiveLeaf.lean`**, not `Main.lean`:
  `evalL_naive_signedPhaseProd_ket` is consumed by `Proofs/Lowering/EvalL.lean` and the two
  `gateCount_Naive_*` theorems by `GateCount/PhaseProduct/Lemmas.lean`; moving them to
  `Main.lean` would force proof files to import `Main`.
- **`MasterTheorem.lean` stays in `PhaseProduct/Math/`** although its only consumer is
  `GateCount/PhaseProduct/Lemmas.lean`: it is mathematics *about the phase-product recursion*,
  and the litmus is "what is it about", not "who imports it".
- **`Spec/Assertions.lean` stays a separate file** (matching `ModularExponentiation/Assertions.lean`
  and `QFT/Assertions.lean`); `Main.lean` keeps only the two proofs, exactly as today.
- **`Spec` is above `Lowering`** because the assertions mention the lowerer; it is *below*
  `Proofs` because proofs prove the assertions.
- **`GoodToomCookPoints` is a definition, not a lemma**, and lives in `Compiler/Coefficients.lean`
  because `Main.lean` and `GateCount/Definitions.lean` state theorems with it.

## 7. Checklist

- [x] Step 1: `Implementation/Semantics/{CleanClosure,GateSemanticsLemmas}.lean`; `MacroSemantics.lean`; 12 external imports rewritten.
- [x] Step 2: `Gates/Macros`, `Gates/NaiveLeaf`, `Spec/{Readiness,Cleanliness,Assertions}`; `PhaseLoweringPlan` imports no proof file.
- [x] Step 3: `Compiler/{Layout,Widths,Coefficients,Compile,Workspace}.lean`; `DefsCore.lean` deleted.
- [x] Step 4: `Lowering/{Plan,PlanBuilders,Lower}.lean`; `PhaseLoweringPlan.lean` deleted.
- [x] Step 5: `Math/ToomCook`, `Math/MasterTheorem`, `Proofs/Compiler/`, `Proofs/Lowering/`.
- [x] Step 6: `Defs.lean` deleted; every external and internal import justified per §3; no `…PhaseProduct.Defs` import anywhere; `scripts/check_phaseproduct_layers.sh` exits 0 (layers + umbrella detector); nothing outside `Proofs/` imports `Proofs/`.
- [ ] After every step: `lake build` green; `#print axioms` on both headline theorems unchanged.
- [ ] `Main.lean` content byte-identical except its two `import` lines.
- [ ] `git diff --stat -- FastMultiplication/ShorVerification/Implementation/PhaseProduct/Math/Table_Generation*` is empty.
