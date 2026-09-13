# REORG_MODEXP: restructure `Implementation/ModularExponentiation/`

All paths below are relative to `FastMultiplication/ShorVerification/`. This plan reuses the
rules of `REORG.md` verbatim: **§1 ground rules** (pure move, one green build + one commit per
step, the two gates `lake build` + `#print axioms` on `Shor.Shor_correct` /
`Shor.exists_shorGateCountBound`, split only at existing banners or `section … end` blocks,
never change namespaces) and **§3 justified-import rule** (no umbrella files; every `import M`
must be justified by a direct use of a declaration `M` itself defines). Read those first.

## 0. Diagnosis

15 files, ~21.5k lines. The layout is already `Defs`/`Assertions`/`Main`/`Proofs`, but:

1. **Definitions files outside this folder depend on the whole proof stack.**
   `Shor/Defs.lean` imports `Proofs/ModExp.lean` (666 lines, which transitively pulls in
   `Step1QPE` 5760, `Step2Bound` 4003, `Algorithm1Expansion` 3009, `Core` 1956, …) and uses
   **no theorem from it** — only definitions that live in `Defs.lean`, `CmpLtNW.lean`,
   `ConstArithmeticLowering.lean`. `Shor/Assertions.lean` does the same for `tbits` alone.
   `Shor/Proofs/OrderFinding.lean` likewise uses only `ModExpLayout`, `ModMulCircuitWorkspaceOK`.
2. **Cross-subroutine inversion.** `Proofs/CmpLtNW.lean` imports
   `Shor/Proofs/NaiveShor/Lemmas.lean` for one lemma, `qftPhase_mod_left_shor` — a pure fact
   about `qftPhase` (`Framework/AbstractMachine/Gates.lean`). ModExp must sit *below* Shor.
3. **~2,500 lines of program-independent mathematics filed as a proof.** `Proofs/Step1QPE.lean`
   l.3079–5602 (sections `CircularDistanceAndZeroPhase`, `KernelChordBound`, reciprocal-square
   tail sums, floor-shell geometry, summing the majorant, the ordinary-fraction tail bound) contain
   zero mentions of `qs`/`QSemantics`/`Gate`/`RegEncoding` and zero references to the Algorithm-1
   model (`alg1*`, `Alg1Trace`, `cfg`). By the repo's litmus ("would a different implementation
   still need this?") they are `Math/`.
4. **`Proofs/Core.lean` (1956 lines) defines the analysis model** — 44 `def`s: staged gates
   `U1`/`U2`/`U34`/`U5`/`stagedGate`, the `alg1*` reference quantities, `Alg1Trace`, packets — used
   by seven other proof files, and imports `Proofs/CmpLtNW.lean` although none of those
   definitions need it (verified: no `CmpLtNW` lemma name occurs in the definition ranges).
5. **`Defs.lean` (626 lines) mixes five concerns**: generic gate macros (`IQFT`, `H_reg`) and a
   PhaseProduct helper (`Gate.PhaseProdWorkspace.ofExtRegs`); the Algorithm-1 circuit
   (`step1`…`step5`, `CmodMulInPlaceCore`, `modExpApprox*`); validity predicates; precision
   (`stepErr`, `algorithm1ExtraBits`, `Algorithm1Precision`); config records.
6. Two top-level files each carry both a workspace *structure* and a construction:
   `CmpLtNW.lean` (`CmpLtNWWorkspace` + the Gate-level step-4 comparator) and
   `ConstArithmeticLowering.lean` (`ConstArithmeticWorkspace`, four clean-state predicates, and
   the LowGate-level step-3 lowering).

Not a problem (leave alone): `Proofs/ModExp.lean`'s two `def`s (`ModExpTailLayout`,
`ModExpTailArithmeticOK`) are proof-local tail invariants used only there.

## 1. Target layout

Import direction is strictly downward. Nothing outside `Proofs/` imports `Proofs/`;
`Main.lean` imports `Spec/` and `Proofs/`.

```
Implementation/Semantics/
  QftPhase.lean            NEW ← Shor/Proofs/NaiveShor/Lemmas.lean l.350–437: `qftPhase_eq_exp_grid_shor`,
                             `star_qftPhase_eq_negative_grid_phase_shor`, `omega_pow_self_shor`,
                             `qftPhase_mod_left_shor`, `norm_qftPhase_one_shor` (pure facts about `qftPhase`/`ωPow`)
Implementation/PhaseProduct/Gates/Macros.lean
  (+ `Gate.PhaseProdWorkspace.ofExtRegs`)   ← Defs.lean ≈l.49–103 (it constructs that structure; users:
                             ModExp, Shor/Proofs/Readiness, Reference/ReferenceLayout, GateCount/Shor_GateCount)

Implementation/ModularExponentiation/
  Math/
    QPETail.lean           ← Proofs/Step1QPE.lean l.3079–5602 (the six `section` blocks from
                             `CircularDistanceAndZeroPhase` on, up to but excluding `Section 15: The uniform
                             Step-1 tail bound`), plus the defs they need: `qpeCircularDistance` (≈l.3098),
                             `qpeCircularTail` (≈l.3108), and `qpeKernel` (≈l.2660) **if** it mentions no semantics
                             (check; if it does, keep it in Step1QPE and stop at the first section that needs it)
  Circuit/
    Workspace.lean         ← Defs.lean "Shared circuit syntax and workspace" minus IQFT/H_reg/ofExtRegs/steps:
                             `ModMulCircuitWorkspaceOK` (≈l.106) + its lemmas + `step1Workspace`/`step2Workspace`/
                             `step5Workspace`; `cmpLtNWWidth`, `CmpLtNWWorkspace` (CmpLtNW.lean l.9–48);
                             `ConstArithmeticWorkspace` (ConstArithmeticLowering.lean l.21–30)
    CmpLtNW.lean           ← CmpLtNW.lean l.50–120: `cmpLtNWSignQubit`, `fastConstMulInto`, `cmpLtNWDifference`, `cmpLtNW`
    Steps.lean             ← Defs.lean: `IQFT` (≈l.41), `H_reg` (≈l.45), `step1`…`step5`, `step5Constant`,
                             `CmodMulInPlaceCore` (≈l.232–314)
    ModExp.lean            ← Defs.lean: `tbits`, `modExpIdealSteps`, `modExpIdeal'` (≈l.317–338);
                             "Modular-exponentiation layout and gates": `ModExpLayout`, `ModExpArithmeticOK`,
                             `modExpApproxStepsValid`, `modExpApproxValid` (≈l.469–515)
  Lowering/
    ConstArithmetic.lean   ← ConstArithmeticLowering.lean l.60–143: `constArithmeticUnitQubit`, `constArithmeticUnit`,
                             `lowerCopyBitPowers`, `lowerCopyConstFromUnit`, `lowerPrepareNegConst`,
                             `lowerCmpGeConst`, `lowerCSubConst`
  Spec/
    Precision.lean         ← Defs.lean: `stepErr` (≈l.335), `algorithm1ExtraBits` (≈l.437), `Algorithm1Precision` (≈l.450)
    Validity.lean          ← Defs.lean "Valid inputs and ideal controlled multiplication": `ModMulCoreLayout`,
                             `GoodModMulBasisInput`, `ValidModMulState`, `GoodAlgorithm1BasisInput`, `ValidAlgorithm1State`;
                             ConstArithmeticLowering.lean l.32–58: `ConstArithmeticCleanBasis`, `CSubConstCleanBasis`,
                             `CmpGeConstCleanState`, `CSubConstCleanState`
    Config.lean            ← Defs.lean "Shared configurations" + "One controlled modular multiplication":
                             `Algorithm1Env`, `ModExpConfig` (+ `approxGate`, `idealGate`, `ValidUnitState`),
                             `ModMulConfig` (+ `approxGate`, `idealGate`, `ValidState`, `ValidUnitState`)
    Assertions.lean        ← Assertions.lean (whole file)
  Proofs/
    Model.lean             ← Proofs/Core.lean definitions: `Step5ConstantOK` (l.610), §3 staged gates (l.650–724),
                             §5–§9 reference arithmetic / Fourier scaffolding / trace packets / reference states /
                             coefficient packets (l.1224–1931) — all 44 `def`/`abbrev`/`structure`s
    Core.lean              ← Proofs/Core.lean lemmas (everything else, same section order)
    CmpLtNW.lean           ← Proofs/CmpLtNW.lean (imports `Implementation.Semantics.QftPhase` instead of Shor)
    ConstArithmetic.lean   ← Proofs/ConstArithmeticLowering.lean
    Algorithm1Expansion.lean, Step1QPE.lean (rest), Step1Bound.lean, Step2Bound.lean,
    Step34Exact.lean, FinalModMul.lean, ModExp.lean     (unchanged content)
  Main.lean                UNCHANGED content; imports `Spec.Assertions`, `Proofs.ModExp`
  README.md                paths updated (documentation path fix, allowed)
```

Deleted: `Defs.lean`, `CmpLtNW.lean`, `ConstArithmeticLowering.lean` (contents split; **no
umbrella replaces them**), `Proofs/ConstArithmeticLowering.lean` (renamed).

Layer order for the check script: `Math < Circuit < Lowering < Spec < Proofs < Main`.
(`Spec/Config` refers to `CmodMulInPlaceCore`, so `Spec` is above `Circuit`; `Lowering` needs only
`Circuit/Workspace`. Neither `Circuit` nor `Lowering` may import `Spec` — if the build says
otherwise, a static structure is misfiled as a predicate: stop and report.)

## 2. External consumers — import rewrites

Current importers (`grep -rn "Implementation.ModularExponentiation" FastMultiplication --include="*.lean" | grep -v "Implementation/ModularExponentiation/"`),
plus the files that today reach ModExp names *transitively through `Shor/Defs.lean`* and must
import directly under the justified-import rule:

| Consumer | Today | After (justified) |
|---|---|---|
| `Shor/Defs.lean` | `Proofs.ModExp`, `ConstArithmeticLowering` | `Circuit.Steps` (`IQFT`, `H_reg`), `Circuit.ModExp` (`modExpApproxValid`, `modExpIdeal'`, `ModExpLayout`), `Circuit.Workspace` (`ModMulCircuitWorkspaceOK`, `CmpLtNWWorkspace`, `ConstArithmeticWorkspace`), `Spec.Precision` (`Algorithm1Precision`), `Spec.Validity` (`CmpGeConstCleanState`, `CSubConstCleanState`), `Lowering.ConstArithmetic` (`lowerCmpGeConst`, `lowerCSubConst`); **drop** `Proofs.ModExp` |
| `Shor/Assertions.lean` | `Proofs.ModExp` | `Circuit.ModExp` (`tbits`) |
| `Shor/Proofs/OrderFinding.lean` | `Proofs.ModExp` | `Circuit.ModExp`, `Circuit.Workspace`; keep `Proofs.ModExp` only if a theorem from it is used (the scan found none) |
| `Shor/Proofs/Correctness.lean` | `Proofs.ModExp` | keep `Proofs.ModExp` (`modExpApprox_valid_dist_uniform`) + `Spec.Config` (`ModExpConfig`, `approxGate`, `idealGate`), `Spec.Validity`, `Spec.Precision` (`stepErr`), `Circuit.Steps`, `Circuit.ModExp`, `Circuit.Workspace` — per the §3 procedure |
| `Shor/Proofs/WholeProgramCorrectness.lean` | `Proofs.ConstArithmeticLowering` | `Proofs.ConstArithmetic` (`evalL_lowerCmpGeConst`, `evalL_lowerCSubConst`), `Spec.Validity` |
| `Reference/ReferencePrecision.lean` | `Defs` | `Spec.Precision` |
| `Reference/ReferenceLayout.lean` (transitive today) | — | `Spec.Precision` (`Algorithm1Precision`), `Circuit.Workspace` (`ModMulCircuitWorkspaceOK`, `CmpLtNWWorkspace`), `PhaseProduct.Gates.Macros` (`ofExtRegs`) |
| `Reference/ReferenceShorImplementation.lean`, `Reference2048Headline.lean` (transitive) | — | `Spec.Precision` (`stepErr`), `Circuit.ModExp` (`tbits`), `Spec.Config` (`ModExpConfig`) |
| `GateCount/Shor_GateCount.lean` (transitive) | — | `Circuit.Steps` (`CmodMulInPlaceCore`), `Circuit.ModExp`, `Circuit.Workspace`, `Lowering.ConstArithmetic`, `Spec.Precision` (`algorithm1ExtraBits`), `PhaseProduct.Gates.Macros` (`ofExtRegs`) |
| `Shor/Proofs/Readiness.lean` (transitive) | — | `Circuit.{Steps,ModExp,Workspace}`, `Lowering.ConstArithmetic`, `Spec.Validity`, `PhaseProduct.Gates.Macros` |
| `Shor/Proofs/NaiveShor/Lemmas.lean` | (defines the `qftPhase_*_shor` block) | `Implementation.Semantics.QftPhase` |
| `Shor/Proofs/NaiveShor/{GoodOutcomeMassLowerBound,Preliminaries,PhaseEstimation}.lean` (transitive) | — | `Circuit.ModExp` (`modExpIdealSteps`), `Circuit.Steps` (`IQFT`, `H_reg`) as applicable |

## 3. Migration order (one green build + one commit per step)

**Step 1 — break the two cross-folder oddities.**
1a. Create `Implementation/Semantics/QftPhase.lean` with the `qftPhase`/`ωPow` block of
    `Shor/Proofs/NaiveShor/Lemmas.lean` (l.350–437; move the minimal self-contained set — at least
    `qftPhase_mod_left_shor` and any `*_shor` helper it uses, e.g. `omega_pow_self_shor`; keep the
    names). Imports: `Framework.AbstractMachine.Gates` (+ Mathlib). `NaiveShor/Lemmas.lean` and
    `Proofs/CmpLtNW.lean` import it; `Proofs/CmpLtNW.lean` **drops** its `Shor.Proofs.NaiveShor.Lemmas`
    import. Build.
1b. Move `Gate.PhaseProdWorkspace.ofExtRegs` (Defs.lean ≈l.49–103, inside `namespace Gate`/
    `PhaseProdWorkspace` as it is) to the end of `PhaseProduct/Gates/Macros.lean`. `Defs.lean`
    already imports `Gates.Macros`. Build.

**Step 2 — stop definitions files from importing proofs.** In `Shor/Defs.lean`,
`Shor/Assertions.lean`, `Shor/Proofs/OrderFinding.lean` replace `…ModularExponentiation.Proofs.ModExp`
with `…ModularExponentiation.Defs` (temporary; step 4 makes it precise). Build. Expect a noticeably
smaller rebuild fan-out from `Shor/Defs.lean` afterwards.

**Step 3 — create `Spec/`.**
- `git mv Assertions.lean Spec/Assertions.lean`; update `Main.lean`.
- `Spec/Precision.lean` ← `stepErr`, `algorithm1ExtraBits`, `Algorithm1Precision`.
- `Spec/Validity.lean` ← the "Valid inputs and ideal controlled multiplication" section of `Defs.lean`
  and the four clean predicates + `ConstArithmeticCleanBasis` from `ConstArithmeticLowering.lean`.
- `Spec/Config.lean` ← the "Shared configurations" and "One controlled modular multiplication" sections.
- `Defs.lean`, `ConstArithmeticLowering.lean` import the new files where names are still used.
Build.

**Step 4 — split the three top-level definition files.**
- `Circuit/Workspace.lean`, `Circuit/Steps.lean`, `Circuit/ModExp.lean` from `Defs.lean` per §1;
  `Circuit/CmpLtNW.lean` from `CmpLtNW.lean` (its `cmpLtNWWidth`/`CmpLtNWWorkspace` go to
  `Circuit/Workspace.lean`); `Lowering/ConstArithmetic.lean` from `ConstArithmeticLowering.lean`
  (its `ConstArithmeticWorkspace` goes to `Circuit/Workspace.lean`).
- `git rm Defs.lean CmpLtNW.lean ConstArithmeticLowering.lean`.
- Rewrite every import of those three modules, inside and outside the folder, per §2 and the
  justified-import procedure (replace → build → add what the compiler names → delete imports whose
  module defines nothing the file uses). Include the *transitive* consumers listed in §2.
Build.

**Step 5 — `Proofs/`.**
- Split `Proofs/Core.lean` at its `section` blocks into `Proofs/Model.lean` (the 44 definitions, in
  their existing sections `Algorithm1PrecisionAndConstants` (only `Step5ConstantOK`), staged gates,
  §5–§9) and `Proofs/Core.lean` (all lemmas, including the `IdealCtrlModMulExactSemantics` block
  l.15–50 and `ModMulPrimitiveDerivedSemantics`). `Model.lean` imports `Spec.*`/`Circuit.*` only —
  if the compiler says a definition needs a `Proofs/CmpLtNW` lemma, leave that definition in `Core.lean`
  and report it. `Core.lean` imports `Model` and `Proofs.CmpLtNW`.
- `git mv Proofs/ConstArithmeticLowering.lean Proofs/ConstArithmetic.lean`; update
  `Shor/Proofs/WholeProgramCorrectness.lean`.
Build.

**Step 6 — `Math/QPETail.lean`.** Cut `Proofs/Step1QPE.lean` from the start of
`section CircularDistanceAndZeroPhase` (≈l.3089) through the end of the section preceding
`Section 15: The uniform Step-1 tail bound` (≈l.5602) into `Math/QPETail.lean`, together with the
defs `qpeCircularDistance`, `qpeCircularTail`, and — only if it mentions no semantics — `qpeKernel`
(≈l.2660, in `section AnalyticQpeSetup`). Keep every `section … end` intact. `Math/QPETail.lean`
imports Mathlib only (and `Framework.*` if a cast lemma needs `ASize`); `Step1QPE.lean` imports it.
Check with `grep -cE "qs\.|QSemantics|Gate\.|RegEncoding|alg1|Alg1" Math/QPETail.lean` = 0. Build.

**Step 7 — check script, README, audit.**
- Extend the layer script from `REORG.md` §4 to this root with layers
  `Math=1, Circuit=2, Lowering=3, Spec=4, Proofs=5, Main=6` (umbrella detector included); it must exit 0.
- Audit every file in the folder and every consumer in §2 against the justified-import rule.
- Update the file paths in `README.md` (`FinalModMul.lean`, `ModExp.lean`, `Algorithm1Expansion.lean`,
  `Step1QPE.lean`, `Step1Bound.lean` are unchanged; add `Math/QPETail.lean` under Step 1 and the new
  `Circuit/`, `Spec/` names). Text otherwise unchanged.
Build. Run the axiom gate. Commit.

**Step 8 (optional, separate PR).** `Proofs/Step2Bound.lean` (4003 lines) and
`Proofs/Algorithm1Expansion.lean` (3009 lines) are fully semantic and each already organised in
7–8 banners; split along those banners only if smaller files are wanted. `Step1QPE.lean` will be
~3,300 lines after step 6.

## 4. Decisions recorded

- **`IQFT` and `H_reg` stay in ModExp (`Circuit/Steps.lean`)** although `Shor/Defs.lean` uses
  them for the order-finding frame: Shor legitimately depends on ModExp, and these macros were
  introduced for Algorithm 1. Moving them to a new shared module would create a folder for two
  one-liners.
- **`Gate.PhaseProdWorkspace.ofExtRegs` moves to `PhaseProduct/Gates/Macros.lean`**: it is a
  constructor for a PhaseProduct structure, and three non-ModExp files use it.
- **The `qftPhase_*_shor` lemmas move to `Implementation/Semantics/QftPhase.lean`**: they are
  facts about a `Framework/AbstractMachine/Gates.lean` definition, used by two subroutines; keeping
  them in Shor made ModExp depend on Shor.
- **`Proofs/Core.lean` is split into `Model` (defs) + `Core` (lemmas)**, both under `Proofs/`.
  The model is proof-local (nothing outside `Proofs/` uses it), so it does not move up a layer;
  the split exists to make the 44 definitions readable in one place and to stop them depending
  on `Proofs/CmpLtNW`.
- **`CmpLtNWWorkspace` and `ConstArithmeticWorkspace` are `Circuit/`, not `Spec/`**: they are
  structures with data fields (`mulWorkspace : Gate.PhaseProdWorkspace …`) consumed by the circuit
  constructions, i.e. the counterparts of `ModMulCircuitWorkspaceOK`. The *state* predicates
  (`Good*BasisInput`, `Valid*State`, `*CleanState`) are `Spec/`.
- **`Math/QPETail.lean` passes the repo litmus**: zero semantics, zero model references, so any
  implementation using phase estimation would need it.
- **`Main.lean` is byte-identical except its two `import` lines.**

## 5. Checklist

- [ ] Step 1: `Implementation/Semantics/QftPhase.lean`; `ofExtRegs` in `PhaseProduct/Gates/Macros.lean`; `Proofs/CmpLtNW.lean` no longer imports anything under `Shor/`.
- [ ] Step 2: `Shor/Defs.lean`, `Shor/Assertions.lean`, `Shor/Proofs/OrderFinding.lean` import no `ModularExponentiation/Proofs/*`.
- [ ] Step 3: `Spec/{Assertions,Precision,Validity,Config}.lean`.
- [ ] Step 4: `Circuit/{Workspace,CmpLtNW,Steps,ModExp}.lean`, `Lowering/ConstArithmetic.lean`; `Defs.lean`, `CmpLtNW.lean`, `ConstArithmeticLowering.lean` deleted; no import of them anywhere.
- [ ] Step 5: `Proofs/Model.lean` + `Proofs/Core.lean`; `Proofs/ConstArithmetic.lean`.
- [ ] Step 6: `Math/QPETail.lean` with zero semantics/model mentions.
- [ ] Step 7: layer script covers this root and exits 0; README paths updated; every import justified (including the transitive consumers in §2).
- [ ] After every step: `lake build` green; `#print axioms` on both headline theorems unchanged.
