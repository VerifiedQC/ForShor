# REORG_SHOR: restructure `Implementation/Shor/`

All paths below are relative to `FastMultiplication/ShorVerification/`. Same rules as the
three earlier reorgs (PhaseProduct, QFT, ModularExponentiation — see the per-folder `README.md`s
and the three `scripts/check_*_layers.sh`): **pure move** (`git mv`, splits at existing
`/-! === Section` banners or `section … end` blocks, import edits, namespace wrappers only;
no statement/proof/name changes), **one green build + one commit per step**, the two gates
after every step (`lake build`; `#print axioms Shor.Shor_correct` /
`Shor.exists_shorGateCountBound` stay `[propext, Classical.choice, Quot.sound]`), and the
**justified-import rule** (no umbrella files; `import M` only if the importing file directly uses
a declaration `M` itself defines).

## 0. Diagnosis

13 files, ~16.7k lines. `Shor/` is the top of the implementation: it composes the three
subroutines into order finding and proves the headline theorems. Its problems:

1. **`Assertions.lean` (the spec) imports `Proofs/Readiness.lean` (7,749 lines)** for a single
   88-line wrapper, `LoweredShorReady.workspace`, which the assertion
   `ShorCorrectApproxLoweredUniform` plugs into `orderFindingApproxLow`'s `GateWorkspaceOK` slot.
   That wrapper depends only on Readiness §1 (`gateWorkspaceOK_orderFindingApprox`, 612 lines,
   which uses nothing from §2–§12 nor from any ModExp proof). So the spec drags 7,100 lines of
   dynamic-readiness proof it never touches.
2. **The generic `Gate → LowGate` compiler lives in `Shor/Defs.lean`.** `GateWorkspaceOK`,
   `lowerGate`, `GateWorkspaceCleanState` (l.45–258) mention no Shor name; `GateCount/*`
   (5 files) and `Reference/ShorProgram.lean` depend on them. `RESTRUCTURE_PLAN.md` Phase 4
   names their home: `Compilation/ — Gate → LowGate lowering (lowerGate)`. Their correctness
   (`Proofs/WholeProgramCorrectness.lean`: `GateWorkspaceOK.*`, `lowerGate_*`,
   `lowerGate_correctness`) goes with them.
3. **Definitions live under `Proofs/`**: `IdealOrderFindingInput` (used in *every* assertion
   statement) and `ShorApproxSetupMinimal.toShorApproxSetup` (data; used by Assertions, Main,
   Reference) in `Proofs/OrderFinding.lean`; the clean-state predicates
   `FullShorWorkspaceCleanState`, `ShorLoweringCleanState`, `ShorConcreteCleanState`,
   `exponentScratchCleanReg`, `ExtReg.ownedReg` in `Proofs/Budgets.lean`. `Defs.lean` even
   contains empty `namespace ThreeRegsCleanState … end` stubs (l.415–425) with the comment
   "proof files extend these namespaces" — the definitions were left in the proof file.
4. **Generic mathematics filed under Shor proofs**:
   `Proofs/Correctness.lean` §2 (l.44–645): ~600 lines of `MeasureClass` / `probability_of_success`
   lemmas (`measProj_*`, `probMeas_l1_dist`, `probability_of_success_eval_dist`, …) with **zero**
   Shor mentions — facts about the framework's measurement interface;
   `shors_probability_bound` (Correctness l.1698–1747): pure number theory whose every dependency
   (`exists_two_distinct_prime_factors`, `valid_choices_card_general`, `general_unsuccessful_bound`,
   `one_not_successful_choice`) already lives in `Framework/Math/Factoring_Reduction/ProbabilityBound.lean`;
   `Proofs/NaiveShor/Lemmas.lean` (2,276 lines) — its own header says "purely mathematical";
   `RegisterHadamardSemantics.eval_Hreg_ket` (Readiness l.22–126) — a semantics lemma about ModExp's `H_reg`;
   `writeNat_overwrite_same_reg` — a generic `RegEncoding` lemma that `NaiveShor/PhaseEstimation.lean`
   imports the 5,760-line `ModularExponentiation/Proofs/Step1QPE.lean` to reach.
5. **Stale imports**: `Defs.lean` imports `PhaseProduct.Main` and `Semantics.GateSemanticsLemmas`
   and uses nothing from either; `GateCount/Definitions.lean` imports `Shor.Proofs.Correctness`
   and uses nothing from it (dragging Correctness + NaiveShor + Readiness into GateCount).
6. **`Proofs/Readiness.lean` is 7,749 lines** — the largest file in the repo — in 13 clean sections
   (§7 Step-2 readiness 1,627 lines, §8 Step-5 2,342 lines). `Proofs/Correctness.lean` §1 is an
   empty banner ("Order-finding circuits — these definitions assemble…") whose definitions moved
   out long ago; `Proofs/OrderFinding.lean` §1–§2 are likewise empty banners. Third `Main.lean`
   (`Proofs/NaiveShor/Main.lean`).

Not a problem (leave alone): `Shor_correct` is proved in `Proofs/NaiveShor/Main.lean` and
*used* by `Proofs/Correctness.lean` (l.1428), so it cannot move into `Shor/Main.lean`; the
`rec'` eliminators in Budgets are proof-local; `successProbAfterFinset` and
`ShorApproxSetup.toModExpConfig` (Correctness) are proof-local vocabulary.

## 1. Target layout

```
Implementation/Compilation/                 NEW — the generic whole-gate Gate → LowGate compiler (RESTRUCTURE_PLAN Phase 4)
  LowerGate.lean          ← Shor/Defs.lean "Generic Whole-Gate Lowering" (l.45–258): GateWorkspaceOK, lowerGate, GateWorkspaceCleanState
  Correctness.lean        ← Shor/Proofs/WholeProgramCorrectness.lean (whole file)
Implementation/Semantics/
  Measurement.lean        NEW ← Shor/Proofs/Correctness.lean §2 (l.44–645, incl. successProbAfterFinset and probability_of_success_eval_dist)
Implementation/RegisterLemmas.lean
  (+ ExtReg.ownedReg ← Budgets l.141–146;  + writeNat_overwrite_same_reg ← ModularExponentiation/Proofs/Step1QPE.lean l.140–~150)
Framework/Math/Factoring_Reduction/ProbabilityBound.lean
  (+ shors_probability_bound ← Shor/Proofs/Correctness.lean l.1698–1747)      ← the ONE Framework touch; see §4
ModularExponentiation/Proofs/Core.lean
  (+ RegisterHadamardSemantics.eval_Hreg_ket ← Shor/Proofs/Readiness.lean l.22–126, keep its namespace)

Implementation/Shor/
  Math/
    OrderFindingAnalysis.lean  ← Proofs/NaiveShor/Lemmas.lean (whole file, unchanged content)
  Circuit/
    Workspace.lean      ← Defs "Shor Workspace Budgets And Clean Inputs", static part: ShorWorkspaceNeed (l.270), qftReserveNeed (281),
                          shorWorkspaceNeed (293), ShorWorkspaceLargeEnough (334), ShorWorkspaceIsolation (382)
    OrderFinding.lean   ← Defs: initY1 (442), orderFindingApprox (448), orderFindingApproxLow (465), orderFindingIdeal (479)
  Spec/
    Cleanliness.lean    ← Defs: ShorWorkspaceCleanInput (367), ThreeRegsCleanState (410), ShorCleanInput (513);
                          Budgets: ThreeRegsCleanState.{zero,ket,add,smul,rec'} (l.40–71), FullShorWorkspaceCleanState (+rec', l.76–102),
                          ShorLoweringCleanState (+rec', l.111–137), exponentScratchCleanReg (147), ShorConcreteCleanState (166);
                          OrderFinding: IdealOrderFindingInput (l.52–59)
    Setup.lean          ← Defs: ShorLoweringSetup (495), ShorApproxSetup (529), ShorApproxSetupMinimal (569), LoweredShorReady (673),
                          ShorFactoringInstance (715); OrderFinding: ShorApproxSetupMinimal.toShorApproxSetup (l.41–140, incl. its private helper)
    Assertions.lean     ← Assertions.lean; imports Proofs.Readiness.Static (see §4) instead of Proofs.Readiness
  Proofs/
    Budgets.lean        ← Budgets l.191–315 (the lemmas: shorConcreteCleanState_ket, ShorConcreteCleanState.to_lowering, fullShorWorkspaceCleanState_*, shorLoweringCleanState_ket)
    Setup.lean          ← OrderFinding.lean: ShorApproxSetup.toIdealOrderFindingInput (l.141–163)
    Readiness/
      Static.lean       ← Readiness §1 (l.154–765) + §13 LoweredShorReady.workspace (l.7664–7698)
      Sequencing.lean   ← §2 (l.766–866)
      Primitives.lean   ← §3–§4 (l.867–1734)
      Init.lean         ← §5 (l.1735–2154)
      Step1.lean        ← §6 (l.2155–2544)
      Step2.lean        ← §7 (l.2545–4171)
      Step5.lean        ← §8 (l.4172–6513)
      IQFT.lean         ← §9 (l.6514–6733)
      ModMul.lean       ← §10 (l.6734–7106)
      ModExp.lean       ← §11 (l.7107–7261)
      Dynamic.lean      ← §12 (l.7262–7660) + §13 LoweredShorReady.workspace_clean (l.7700–7746)
    Correctness.lean    ← Correctness §3–§4 (l.646–1690): probability transfer, ShorApproxSetup.prepared_state_valid, toModExpConfig,
                          Shor_correct_approx_uniform*, probability_of_success_lowerGate_eq, orderFindingApproxLow_probability_eq,
                          Shor_correct_approx_lowered_of_modExp_bound
    NaiveShor/
      Preliminaries.lean, PhaseEstimation.lean, GoodOutcomeMassLowerBound.lean   (unchanged content)
      Correctness.lean  ← NaiveShor/Main.lean
  Main.lean             UNCHANGED content; imports Spec.Assertions, Proofs.Correctness
```

Deleted: `Defs.lean`, `Proofs/OrderFinding.lean`, `Proofs/WholeProgramCorrectness.lean`,
`Proofs/Readiness.lean` (all split/moved; **no umbrella replaces any of them**).

Layer order for the check script: `Math < Circuit < Spec < Proofs < Main`; inside `Proofs/`
the `Readiness/` chain is `Static < Sequencing < Primitives < Init < Step1 < Step2 < Step5 < IQFT < ModMul < ModExp < Dynamic`,
and `Budgets, Setup < Readiness/* < NaiveShor/* < Correctness`. Repo-wide: `Compilation` sits
above `PhaseProduct`, `QFT`, `ModularExponentiation` and below `Shor`, `GateCount`, `Reference`.

## 2. External consumers — import rewrites

| Consumer | Today | After (justified) |
|---|---|---|
| `GateCount/Definitions.lean` | `Shor.Proofs.Correctness` (uses nothing from it) | `Compilation.LowerGate` (`lowerGate`, `GateWorkspaceOK`) + whatever else the compiler names; **drop** the Correctness import |
| `GateCount/PhaseProduct/{Lemmas,Main}.lean`, `GateCount/QFT_GateCount.lean` (transitive today) | — | `Compilation.LowerGate` |
| `GateCount/Shor_GateCount.lean` (transitive) | — | `Compilation.LowerGate`, `Shor.Circuit.OrderFinding` (`orderFindingApprox(Low)`), `Shor.Spec.Setup` (`ShorApproxSetup`) |
| `Reference/ShorProgram.lean` (transitive) | — | `Compilation.LowerGate` (`GateWorkspaceOK`), `Shor.Circuit.OrderFinding`, `Shor.Spec.Setup` (`ShorLoweringSetup`, `ShorApproxSetup(Minimal)`, `toShorApproxSetup`) |
| `Reference/ReferenceLayout.lean` | `Shor.Proofs.OrderFinding` | `Shor.Spec.Setup` (`toShorApproxSetup`), `Shor.Circuit.Workspace` (`shorWorkspaceNeed`, `ShorWorkspaceLargeEnough`) |
| `Reference/ReferenceReadiness.lean` | `Shor.Proofs.Readiness` | `Shor.Proofs.Readiness.Static` (`LoweredShorReady.workspace`), `Shor.Spec.Setup` (`LoweredShorReady`, `ShorApproxSetupMinimal`), `Shor.Circuit.Workspace` |
| `Reference/ReferenceShorImplementation.lean`, `Reference2048Headline.lean` | `Shor.Main` | unchanged (+ `Shor.Spec.Setup` if `ShorLoweringSetup` is named directly) |
| `Reference/StandardLoweringSetup.lean` | `Shor.Defs` | `Shor.Spec.Setup` |
| `Shor/Main.lean` | `Shor.Assertions`, `Shor.Proofs.Correctness` | `Shor.Spec.Assertions`, `Shor.Proofs.Correctness`, and `Framework.Math.Factoring_Reduction.ProbabilityBound` (`shors_probability_bound`) |
| `ModularExponentiation/Proofs/Step1QPE.lean` | (defines `writeNat_overwrite_same_reg`) | `Implementation.RegisterLemmas` |
| `Shor/Proofs/NaiveShor/PhaseEstimation.lean` | `ModularExponentiation.Proofs.Step1QPE` (for that one lemma) | `Implementation.RegisterLemmas`; **drop** the Step1QPE import |

Find anything missed with
`grep -rn "Implementation.Shor\b" FastMultiplication --include="*.lean" | grep -v "Implementation/Shor/"`
and confirm no `Shor.Defs` import survives with `grep -rn "Implementation.Shor.Defs$" FastMultiplication --include="*.lean"`.

## 3. Migration order (one green build + one commit per step)

**Step 1 — extract the shared pieces (one commit each).**
1a. `Implementation/Compilation/LowerGate.lean` ← `Shor/Defs.lean` l.45–258 (the `## Generic Whole-Gate Lowering`
    block: `GateWorkspaceOK`, its empty `namespace GateWorkspaceOK end`, `lowerGate`, `GateWorkspaceCleanState`).
    Imports (justified): `QFT.Lowering.Workspace` (`QFTReserveOK`), `QFT.Lowering.PlanBuilders` (`lowerQFT`),
    `QFT.Spec.Cleanliness` (`QFTWorkspaceStateOK`), `PhaseProduct.Compiler.Workspace` (`(C)SignedRecursiveWorkspaceOK`),
    `PhaseProduct.Lowering.Lower`, `PhaseProduct.Spec.Cleanliness` (`RecursiveWorkspaceCleanState`),
    `ModularExponentiation.Circuit.Workspace` (`ConstArithmeticWorkspace`), `ModularExponentiation.Lowering.ConstArithmetic`,
    `ModularExponentiation.Spec.Validity` (`CmpGeConstCleanState`, `CSubConstCleanState`) — start from `Defs.lean`'s list, prune.
    `git mv Shor/Proofs/WholeProgramCorrectness.lean Implementation/Compilation/Correctness.lean`. `Shor/Defs.lean` imports `Compilation.LowerGate`. Build.
1b. `Implementation/Semantics/Measurement.lean` ← `Shor/Proofs/Correctness.lean` l.44–645 (keep the `variable {qs} [RegEncoding qs.Basis]`
    lines it relies on; imports `Framework.Quantum.Measurement`, `Framework.Submission` for `probability_of_success`/`r_found`).
    `Correctness.lean` imports it. Build.
1c. Move `shors_probability_bound` (Correctness l.1698–1747) to the end of
    `Framework/Math/Factoring_Reduction/ProbabilityBound.lean` (all its dependencies are already there; the file imports only
    `Factoring_Reduction.Defs`, so no cycle). `Shor/Main.lean` imports `ProbabilityBound`. Build.
1d. Move `ExtReg.ownedReg` (Budgets l.141–146) and `writeNat_overwrite_same_reg` (ModExp `Proofs/Step1QPE.lean` l.140–~150)
    to `Implementation/RegisterLemmas.lean`. `Step1QPE.lean`, `Budgets.lean` and `NaiveShor/PhaseEstimation.lean` import
    `RegisterLemmas`; `PhaseEstimation.lean` **drops** `ModularExponentiation.Proofs.Step1QPE`. Build.
1e. Move `RegisterHadamardSemantics.eval_Hreg_ket` (Readiness l.22–126) into `ModularExponentiation/Proofs/Core.lean`
    inside a `namespace RegisterHadamardSemantics … end` block (the `section GateSemanticsDissolvedShor` wrapper is dropped;
    the fully qualified name is unchanged). `Readiness.lean` already imports `ModularExponentiation.Proofs.Core`. Build.

**Step 2 — stale imports.** `Shor/Defs.lean` drops `PhaseProduct.Main` and `Semantics.GateSemanticsLemmas`;
`GateCount/Definitions.lean` replaces `Shor.Proofs.Correctness` with `Shor.Defs` (temporary; step 4 makes it precise). Build.

**Step 3 — create `Spec/`.**
- `git mv Assertions.lean Spec/Assertions.lean`; update `Main.lean`, `Proofs/Correctness.lean`, `Proofs/NaiveShor/Preliminaries.lean`.
- `Spec/Cleanliness.lean` and `Spec/Setup.lean` per §1, pulling from `Defs.lean`, `Proofs/Budgets.lean`, `Proofs/OrderFinding.lean`.
  Delete the empty `namespace ThreeRegsCleanState/FullShorWorkspaceCleanState/ShorLoweringCleanState … end` stubs in `Defs.lean`
  (l.415–425; they declare nothing — the one allowed deletion). What remains of `Proofs/OrderFinding.lean` is one lemma:
  `git mv` it to `Proofs/Setup.lean`.
- `Defs.lean`, `Budgets.lean`, `Readiness.lean`, `Correctness.lean` import the new `Spec` files where names are used.
Build.

**Step 4 — split `Defs.lean` into `Circuit/Workspace.lean`, `Circuit/OrderFinding.lean`;** `git rm Defs.lean`;
rewrite every `…Shor.Defs` import (inside and outside the folder) per §2 and the justified-import procedure
(replace → build → add what the compiler names → delete imports whose module defines nothing the file uses),
including the transitive consumers listed in §2. Build.

**Step 5 — `Proofs/`.**
- Split `Readiness.lean` into `Proofs/Readiness/*` per §1, one file per section (§3+§4 together, §13 split between
  `Static` and `Dynamic`). Give each file `import` of the previous one in the chain to start, then prune per the rule
  (§1's theorem uses nothing from later sections and no ModExp proof, so `Static.lean` imports only `Spec/*`, `Circuit/*`,
  `Compilation.LowerGate` and the subroutine workspace files). `Spec/Assertions.lean` and `Reference/ReferenceReadiness.lean`
  import `Proofs.Readiness.Static`; `Proofs/Correctness.lean` imports `Proofs.Readiness.Dynamic`.
- `git mv Proofs/NaiveShor/Lemmas.lean Math/OrderFindingAnalysis.lean` (imports `Framework.Math.ShorDefinition`,
  `Framework.AbstractMachine.Gates`, `Implementation.Semantics.QftPhase` — unchanged). `Preliminaries.lean`, `PhaseEstimation.lean` import it.
- `git mv Proofs/NaiveShor/Main.lean Proofs/NaiveShor/Correctness.lean`; `Proofs/Correctness.lean` import updated.
- Delete the empty §1 banner block in `Proofs/Correctness.lean` (l.34–43, no declarations).
Build.

**Step 6 — check script, audit.**
- Add `scripts/check_shor_layers.sh` (same shape as `check_qft_layers.sh`) with layers
  `Math=1, Circuit=2, Spec=3, Proofs=4, Main=5`, the umbrella detector, and the intra-`Proofs` order of §1.
  Add one **allowlisted exception**: `Spec.Assertions → Proofs.Readiness.Static` (see §4). Must exit 0.
- Add `scripts/check_compilation_layers.sh` (or extend one script to several roots): `Compilation/LowerGate < Compilation/Correctness`;
  no file under `Compilation/` imports `Shor.*`, `GateCount.*`, `Reference.*`.
- Audit every file in `Shor/`, `Compilation/`, and the §2 consumers against the justified-import rule.
- Add `Shor/README.md` (navigational only, like the other folders').
Build. Run the axiom gate. Commit.

**Step 7 (optional, separate PR).** `Proofs/Readiness/Step5.lean` (2,342 lines) and `Step2.lean` (1,627) can be
split further along their own sub-banners; `Proofs/Correctness.lean` §4 (l.796–1690) along its theorem groups.

## 4. Decisions recorded

- **`Spec/Assertions.lean` still imports one proof file, `Proofs/Readiness/Static.lean`** (612 lines instead of 7,749).
  The assertion `ShorCorrectApproxLoweredUniform` inlines `hready.workspace : GateWorkspaceOK …` into the circuit term;
  by proof irrelevance the *meaning* of the Prop does not depend on that proof body (the existing docstring says so), but
  the *file* dependency is real. Removing it entirely is not a pure move — it needs either a `workspace : GateWorkspaceOK …`
  field on `LoweredShorReady`, or quantifying the assertion over an arbitrary `hws` — and is recorded here as the
  follow-up that would let `Spec` stop importing `Proofs` altogether.
- **`Compilation/` is a new top-level implementation folder**, not a `Shor/` subfolder: `lowerGate` is the compiler for
  the whole `Gate` language, mentions no Shor name, and is consumed by `GateCount/*` and `Reference/*` independently of
  order finding. `RESTRUCTURE_PLAN.md` Phase 4 already names it.
- **`shors_probability_bound` goes to `Framework/Math/Factoring_Reduction/ProbabilityBound.lean`** — the only Framework file
  this reorg touches. It is purely about `successful_choices`/`valid_choices`, every lemma it uses is already in that
  file, and by the Framework's own litmus ("would a different correct implementation still need this?") it is backbone
  math. If touching Framework is unwanted, the fallback is `Shor/Math/ClassicalBound.lean` importing `ProbabilityBound`.
- **`Semantics/Measurement.lean` is implementation-side**, not `Framework/Quantum/Measurement.lean`, to keep Framework
  untouched beyond the item above; it contains only lemmas about `MeasureClass`/`probability_of_success`.
- **`Shor_correct` stays in `Proofs/NaiveShor/Correctness.lean`**: `Proofs/Correctness.lean` uses it (l.1428), so `Main.lean`
  cannot own it without reversing the import direction. `Main.lean` keeps its two theorems byte-identical.
- **`NaiveShor/` keeps its name** (established term for the ideal-`ctrlModMul` analysis); only its `Main.lean` is renamed.
- **`Readiness/` is split by its own 13 sections**, chained; `Static.lean` is separated first because it is the only part
  the spec and `Reference/ReferenceReadiness.lean` need.

## 5. Checklist

- [ ] Step 1a: `Implementation/Compilation/{LowerGate,Correctness}.lean`.
- [ ] Step 1b: `Implementation/Semantics/Measurement.lean`.
- [ ] Step 1c: `shors_probability_bound` in `Framework/Math/Factoring_Reduction/ProbabilityBound.lean`.
- [ ] Step 1d: `ExtReg.ownedReg`, `writeNat_overwrite_same_reg` in `Implementation/RegisterLemmas.lean`; `PhaseEstimation.lean` no longer imports `Step1QPE`.
- [ ] Step 1e: `eval_Hreg_ket` in `ModularExponentiation/Proofs/Core.lean`.
- [ ] Step 2: `Shor/Defs.lean` and `GateCount/Definitions.lean` stale imports removed.
- [ ] Step 3: `Spec/{Assertions,Cleanliness,Setup}.lean`; `Proofs/Setup.lean`; empty namespace stubs deleted.
- [ ] Step 4: `Circuit/{Workspace,OrderFinding}.lean`; `Defs.lean` deleted; no `…Shor.Defs` import anywhere.
- [ ] Step 5: `Proofs/Readiness/*` (11 files); `Math/OrderFindingAnalysis.lean`; `Proofs/NaiveShor/Correctness.lean`; `Readiness.lean` deleted.
- [ ] Step 6: `scripts/check_shor_layers.sh` + `Compilation` check exit 0; `Spec.Assertions → Proofs.Readiness.Static` is the only Spec→Proofs edge; `Shor/README.md`.
- [ ] After every step: `lake build` green; `#print axioms` on both headline theorems unchanged.
- [ ] `Main.lean` content byte-identical except its `import` lines.
