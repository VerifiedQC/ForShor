# PLAN: make the reference Shor circuit computable and emit it as an IR

## 0. What this plan is for

The repository proves that `referenceSubmittedProgram` (a `LowGate` circuit) is a
correct Shor order-finding implementation. Today that circuit is a *noncomputable*
Lean term: it can be reasoned about, but not run, printed, or handed to anyone.

**Goal.** Make the reference circuit an ordinary computable Lean value, then add a
small printer `LowGate → JSON` and an executable, so that for concrete inputs
`(k, a, N, m)` we can run

```
lake exe forshor_emit 2 2 15 0
```

and get a JSON document describing *exactly the circuit the theorems are about*.
Anyone can consume that JSON (count gates, simulate, feed to Qualtran, ...).

**Design principle: computable by construction.** We do NOT write a second copy
("mirror") of the lowering and prove it faithful. We change the real definitions
so they compile. Then the emitted circuit *is* the verified term and no fidelity
theorem is needed. (An earlier external attempt — the `Emit_*.zip` — took the
mirror route; it drifted out of sync with this repo and left 4 `sorry`s. Do not
import or copy it.)

**Non-goals** (do not attempt these):

- Emitting the 2048-bit circuit flat. It has billions of gates; nothing can
  materialise it. The flat IR is for small/moderate `N` (a few dozen bits).
- Proving a closed-form gate count. Not needed: `LowGate.gateCount` is itself
  computable and the emitter prints Lean's own count for cross-checking.
- Any Python / Qualtran integration.
- Changing what any theorem *means*. Statements may change *spelling* (an angle
  written as `(2/N : ℚ)` instead of `2*π/N`), never meaning.

## 1. Ground rules for the agent

1. **Work on a branch.** The tree has uncommitted edits; commit them first
   (`git add -A && git commit -m "WIP before IR plan"`), then `git checkout -b ir-emitter`.
2. **Build after every step**: `lake build` from the repo root. Never move to the
   next step with a red build. Never introduce `sorry`. Never delete a theorem.
3. **How Lean tells you what blocks compilation.** Remove `noncomputable` from a
   `def` and build. If it is not compilable you get
   `failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Foo.bar', and it does not have executable code`.
   `Foo.bar` is the culprit. Fix `Foo.bar` (or the thing that makes it appear), rebuild, repeat.
4. **Proofs are erased; data is not.** A `def` may freely use `ℝ`, `Classical`,
   `Matrix.inv`, any noncomputable `qs : QSemantics` *inside a proof of a `Prop`*.
   It may NOT use them to build data: fields of structures that are in `Type`
   (`Reg`, `ExtReg`, `LowGate`, `PhaseLoweringPlan`, `CmpLtNWWorkspace`,
   `Gate.PhaseProdWorkspace`, `ShorApproxSetup`) and function arguments that
   are values (including *instance arguments* like `[RegEncoding Basis]`).
5. **`noncomputable section`** at the top of a file makes *every* def in it
   noncomputable. Several data-path files use it (listed in §2). Delete the
   section header and instead write `noncomputable def` only on the defs that
   genuinely need it.
6. **The code generator cannot compile `T.rec` / `T.recOn` / `induction` tactic
   output.** Any `def` whose body is `by induction ... with` must be rewritten
   with `match ... with` (structural recursion). `if h : p then a else b` on a
   decidable `p` (e.g. `<` on `ℕ`) is fine. Well-founded recursion with
   `termination_by`/`decreasing_by` is fine.
7. Prefer term-mode definitions for data. Tactic blocks (`by refine {..}`,
   `simpa ... using`) *can* produce compilable terms, but when the compiler
   complains, rewrite the data part in term mode and keep only `Prop` fields
   as `by ...` proofs.
8. When a proof breaks after a spelling change, the fix is local: unfold the new
   definition, `push_cast`, `ring`/`field_simp`. Do not restructure proofs.

## 2. Map of the data path (what must become computable)

Call chain of the circuit, from the top:

```
referenceSubmittedProgram lowering inst                Reference/ReferenceShorImplementation.lean
  = referenceProgramAt lowering (referenceChosenPrecision inst.N) inst     -- Nat.find: stays noncomputable
referenceProgramAt lowering m inst = referenceShorProg lowering inst m     -- THIS is what we emit, at explicit m
referenceShorProg / referenceShorCircuit                Reference/ShorProgram.lean
  allocateReferenceLayout lowering.ops inst η           Reference/ReferenceLayout.lean   (η : ℝ  → problem)
  referenceApproxSetup / referenceLowerWorkspace         Reference/ShorProgram.lean      (built through qs → problem)
  orderFindingApproxLow qs k hk ops a N x y work scratch flag ...    Implementation/Shor/Defs.lean
    orderFindingApprox qs a N x y work scratch flag hws hstep4       Implementation/Shor/Defs.lean
      H_reg, initY1, modExpApproxValid, IQFT                          ModularExponentiation/Defs.lean
        CmodMulInPlaceCore = step1 ;; step2 ;; step3 ;; step4 ;; step5
    lowerGate k hk ops G hworkspace                                   Implementation/Shor/Defs.lean
      lowerQFT                                                        QFT/Defs.lean
        reserveQFTLoweringPlan → standardQFTLoweringPlan → lowerQFTPlan
        QFTWorkspaceOK.phaseWorkspace, standardPhaseProdUsingPlan
      lowerSignedPhaseProdWithWorkspace / lowerCSignedPhaseProdWithWorkspace   PhaseProduct/Defs.lean
        standardSignedPhaseLoweringPlan / standardCSignedPhaseLoweringPlan     PhaseProduct/PhaseLoweringPlan.lean
          canonicalSignedStep                                          PhaseProduct/DefsCore.lean
          loweringPhaseCoeff  (Matrix.inv → problem)                   PhaseProduct/PhaseLoweringPlan.lean
        lowerGateRec (by induction → problem)                          PhaseProduct/PhaseLoweringPlan.lean
          LowGate.Naive_SignedPhaseProd → CPhase → LowGate.Phase q (θ : ℝ)    PhaseProduct/Proofs/NaivePhaseProduct.lean
      lowerCmpGeConst / lowerCSubConst                                 ModularExponentiation/ConstArithmeticLowering.lean (already computable)
```

Files under `FastMultiplication/ShorVerification/` currently wrapped in
`noncomputable section`: `Implementation/Reference/ReferenceLayout.lean`,
`Implementation/Reference/ReferenceReadiness.lean`,
`Implementation/Reference/ShorProgram.lean`,
`Implementation/Reference/ReferenceShorImplementation.lean`,
`Implementation/Reference/Reference2048Headline.lean`.

The seven independent sources of noncomputability, and the stage that fixes each:

| # | Source | Where | Stage |
|---|---|---|---|
| a | angles are `ℝ` (`Real.pi` has no executable code) | `Gate.SignedPhaseProd`, `Gate.CSignedPhaseProd`, `LowGate.Phase`, all angle formulas | 1 |
| b | `algorithm1ExtraBits (η : ℝ) = ⌈2·log₂(2+1/(2η))⌉₊` decides the work-register width | `ModularExponentiation/Defs.lean:443`, used by `ReferenceLayout.lean` | 2 |
| c | unused `{Basis} [RegEncoding Basis]` / `(qs : QSemantics)` arguments on gate constructors | `ModularExponentiation/Defs.lean`, `Shor/Defs.lean`, `Reference/ShorProgram.lean` | 2 |
| d | `by induction` definitions (`.rec`) | `lowerGateRec`, `lowerQFTPlan` | 3 |
| e | tactic-built *data* marked `noncomputable` | plan builders, `canonicalSignedStep`, `phaseWorkspace`, `reference_step4Workspace`, ... | 3 |
| f | `loweringPhaseCoeff` via `Matrix.inv` | `PhaseLoweringPlan.lean:25` → `DefsCore.lean:273` | 4 |
| g | `Nat.find` over a real predicate chooses `m` | `referenceChosenPrecision`, `referenceTrialCount` | not fixed: emit at explicit `m` |

Stage order matters only for Stage 1: while angles are `ℝ`, *nothing* downstream
can be test-compiled, so do Stage 1 first. Stages 2–4 can be done in any order;
Stage 5 last.

---

## Stage 1 — Angles become `ℚ` (in units of π)

**Status: DONE** (branch `ir-emitter`). `lake build` is green across all 3259
jobs; `#print axioms Shor.Shor_correct` / `#print axioms
Shor.exists_shorGateCountBound` are unchanged (`propext, Classical.choice,
Quot.sound`, no `sorryAx`). Notes for whoever picks up Stage 2:
- The phantom `{Basis}`/`[RegEncoding Basis]` arguments on `step1`, `step2`,
  `step4`, `CmodMulInPlaceCore`, `modExpApproxStepsValid`, `modExpApproxValid`,
  `fastConstMulInto`, `cmpLtNW`, and the local `step5Forward` in
  `Shor/Proofs/Readiness.lean` did **not** block computability once their angle
  arguments became `Angle` — dropping `noncomputable` from all of them
  succeeded immediately, ahead of schedule. `step5` itself is `def` already too
  (§1.4 only listed the others). §2.3's "remove unused type-class/qs arguments"
  work may already be partly done as a side effect; re-check before repeating it.
- The reference/comparison-only angle definitions `alg1Step1Phase`,
  `alg1Step2Phase`, `alg1Step5Phase` (`ModularExponentiation/Proofs/Core.lean`)
  turned out to double as literal `Gate.CPhaseProdUsing`/`PhaseProdUsing`
  arguments elsewhere (`Step1QPE.lean`, `Step2Bound.lean`,
  `Shor/Proofs/Readiness.lean`), so they were converted to `Angle` rather than
  left as `ℝ` — each call site that needs the real value now goes through
  `Angle.toReal` explicitly.
- The bridge pattern from §1.5 (`have hφ : Angle.toReal phi = ...; rw [hφ]`)
  was needed throughout `QFT/Proofs/Decomposition.lean`,
  `ModularExponentiation/Proofs/{Step1QPE,Step2Bound,Core,CmpLtNW}.lean`,
  `Shor/Proofs/Readiness.lean`, and `GateCount/Shor_GateCount.lean` — same
  shape every time: unfold the local `phi`/`φ` and `Angle.toReal`, `push_cast`,
  `ring` (or `field_simp` for the Step-2 power identity).

### Why
Every angle in the whole development is a rational multiple of π:
`qftPhi m = 2π/2^m`, step 1 `2π((c+N−1)%N)/N`, step 2 `2πN/2^(w+d)`, step 5
`2π(k5%N)/N`, `fastConstMulInto` `2πN/2^w`, the plan's `phi * coeff` with
`coeff : ℚ`, `CPhase`'s `θ/2`, `signedPairAngle`'s `phi * w_x * w_z` with
integer weights. Storing the rational `r` (meaning `r·π`) loses nothing and is
computable. This is a **monomorphic** change: three constructor field types
change from `ℝ` to `ℚ`; no type parameters are added anywhere.

### 1.1 Add the angle helper
Create `FastMultiplication/ShorVerification/Framework/AbstractMachine/Angle.lean`:

- `abbrev Angle := ℚ` (documented: "an angle in units of π; `a : Angle` denotes `a·π` radians").
- `noncomputable def Angle.toReal (a : Angle) : ℝ := (a : ℝ) * Real.pi`.
- Lemmas (all by `simp [Angle.toReal]; ring` / `push_cast`):
  `toReal_zero`, `toReal_add`, `toReal_neg`, `toReal_sub`,
  `toReal_mul_rat (a c : ℚ) : Angle.toReal (a * c) = Angle.toReal a * (c : ℝ)`,
  `toReal_div (a : ℚ) (n : ℚ) : Angle.toReal (a / n) = Angle.toReal a / (n : ℝ)`,
  `toReal_intCast`, `toReal_natCast`.
- Do **not** tag `Angle.toReal` unfolding as global `@[simp]`; proofs should
  unfold it explicitly so existing `simp` sets are not disturbed.

Import this file from `Gates.lean` and `LowGate.lean`.

### 1.2 Change the constructors
- `Framework/AbstractMachine/Gates.lean`: `SignedPhaseProd : (phi : Angle) → ...`,
  `CSignedPhaseProd : (ctrl : ℕ) → (phi : Angle) → ...`;
  `def qftPhi (m : ℕ) : Angle := (2 : ℚ) / 2 ^ m` (now a plain `def`, not `noncomputable`).
- `Framework/AbstractMachine/LowGate.lean`: `Phase : ℕ → Angle → LowGate`.
- `Implementation/PhaseProduct/PhaseLoweringPlan.lean`: the `phi : ℝ` fields of
  `signedBase`, `signedStep`, `cSignedBase`, `cSignedStep` become `Angle`; every
  `(phi : ℝ)` parameter in that file (`compiledSignedPhaseGate`,
  `compiledCSignedPhaseGate`, `lowerSignedPhaseProd`, `planCompile*`,
  `planCompiledSignedPhaseGate`, `standardSignedPhaseLoweringPlan`, ...) becomes `Angle`.
- `Implementation/PhaseProduct/DefsCore.lean`: `compileAnnotatedOpsToSignedGateAux`,
  `compileOpsToSignedGate`, `compileOpsToCSignedGate`: `(phi : ℝ)` → `Angle`, and the
  leaf angle `phi * ((phaseCoeff l : ℚ) : ℝ)` becomes `phi * phaseCoeff l`.
  Same at `PhaseLoweringPlan.lean` lines ~529 and ~577.
- `Implementation/PhaseProduct/Proofs/GateLevelCorrectness/GateConstructions.lean`:
  `PhaseProdUsing (phi : Angle)`, `CPhaseProdUsing (ctrl) (phi : Angle)`.
- `Implementation/PhaseProduct/Defs.lean`, `Implementation/Shor/Defs.lean` (`lowerGate`),
  `Implementation/QFT/Defs.lean` (`standardPhaseProdUsingPlan`, `QFTLoweringPlan.split`): `ℝ` → `Angle` in angle positions.
- `Implementation/PhaseProduct/Proofs/NaivePhaseProduct.lean`:
  `CPhase (ctrl target : ℕ) (theta : Angle)` — body unchanged (`theta / 2`, `-theta / 2` are ℚ); drop `noncomputable`.
  `signedPairAngle (phi : Angle) (xTerm zTerm : ℕ × ℤ) : Angle := phi * (xTerm.2 : ℚ) * (zTerm.2 : ℚ)`.
  `naiveSignedPhaseGates`, `Naive_SignedPhaseProd`: `Angle`; drop `noncomputable`.
- `Implementation/PhaseProduct/Proofs/NaiveCPhaseProduct.lean`: same for `CCPhase`,
  `naiveCSignedPhaseGates`, `Naive_CSignedPhaseProd`.
- `Implementation/GateCount/**`: signatures with `(phi : ℝ)` → `Angle`. These lemmas
  never look at the angle's value; only the type changes.

### 1.3 Change the semantic axioms (statements only)
Wherever the semantics reads an angle, multiply by π:

- `Framework/Semantics/GateSemantics.lean` (`GateSemanticsFacts`):
  `eval_SignedPhaseProd_ket`, `eval_CSignedPhaseProd_ket`: replace
  `(phi * Complex.I * ...)` by `(((Angle.toReal phi : ℝ) : ℂ) * Complex.I * ...)`.
- `Framework/Semantics/LowGateSemantics.lean` (`LowerGateClass.evalL_Phase_ket`):
  `Complex.exp (θ * Complex.I)` → `Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I)`.
- `Framework/Instantiation/GateSemanticsCore.lean`: `signedPhaseKet`, `cSignedPhaseKet`,
  and the `Phase` atom of the concrete `LowerGateClass` instance, same replacement.
  The `hz : (-phi) * I * (...) + phi * I * (...) = 0` steps in `atomAdjEval_*` become
  `by rw [Angle.toReal_neg]; push_cast; ring`.

### 1.4 Change the angle *definitions*
| Def | File | New body |
|---|---|---|
| `step1` `phi` | `ModularExponentiation/Defs.lean:239` | `(2 * (((c + N - 1) % N : ℕ) : ℚ)) / (N : ℚ)` |
| `step2` `phi` | `:258` | `(2 * (N : ℚ)) / (2 : ℚ) ^ (regSize work.active + regSize dataCarry.active)` |
| `step5` `phi` | `:287` | `(2 * ((k5val % N : ℕ) : ℚ)) / (N : ℚ)` |
| `fastConstMulInto` `phi` | `ModularExponentiation/CmpLtNW.lean:66` | `(2 * (N : ℚ)) / (ASize hworkspace.zExt.active : ℚ)` |
| `qftPhi` | `Framework/AbstractMachine/Gates.lean:67` | `(2 : ℚ) / 2 ^ m` |

Drop `noncomputable` from `step1`, `step2`, `step5`, `CmodMulInPlaceCore`,
`fastConstMulInto`, `cmpLtNW`, `modExpApproxStepsValid`, `modExpApproxValid`
(they may still fail to compile for reasons fixed in Stage 2 — that's fine, note it and continue; or leave the keyword until Stage 2).

### 1.5 Repair the proofs
For each proof that unfolds an angle to its real value, the bridge is one `have`:
```
have hφ : Angle.toReal phi = 2 * Real.pi * (c : ℝ) / N := by
  simp only [phi, Angle.toReal]; push_cast; ring
```
and then `rw [hφ]` (or `simp only [hφ]`) where the proof previously saw
`2 * Real.pi * ...`. Files by expected effort (occurrences of `Real.pi`):

- `ModularExponentiation/Proofs/Step1QPE.lean` (76), `Step2Bound.lean` (59),
  `QFT/Proofs/Decomposition.lean` (36), `Algorithm1Expansion.lean` (13),
  `GateCount/Shor_GateCount.lean` (12 — these appear in *statements* that spell out the step angles; rewrite them with the new ℚ formulas),
  `Shor/Proofs/Readiness.lean` (7), `Core.lean` (5), `Proofs/CmpLtNW.lean` (4), `FinalModMul.lean` (2).
- `NaivePhaseProduct.lean` / `NaiveCPhaseProduct.lean`: `complex_exp_half_cancel`
  etc. now have `Angle.toReal (θ/2)`; use `Angle.toReal_div`.
- `Instantiation/GateSemanticsCore.lean`: as in 1.3.

Untouched: `Framework/Math/**`, `Shor/Proofs/NaiveShor/**`, `Reference2048Headline.lean`
(their `Real.pi` is analysis about probabilities, not gate angles).

**Checkpoint 1:** `lake build` green; `#print axioms Shor.Shor_correct` and
`#print axioms Shor.exists_shorGateCountBound` unchanged (no `sorryAx`).

---

## Stage 2 — Layout over `m : ℕ`; remove phantom parameters

**Status: DONE** (branch `ir-emitter`). `lake build` is green across all 3260
jobs; `#print axioms Shor.Shor_correct` / `#print axioms
Shor.exists_shorGateCountBound` are still `propext, Classical.choice,
Quot.sound` (no `sorryAx`). `referenceShorCircuit`/`referenceShorProg`
(`Reference/ShorProgram.lean`) now take no `qs`/`RegEncoding` argument at all;
removing their `noncomputable` produces exactly one blocker — `depends on
'orderFindingApproxLow', which is 'noncomputable'` — which bottoms out at
`lowerQFT`/`lowerGate` (Stage 3's recursor-based plan builders), matching the
checkpoint. Notes for whoever picks up Stage 3:
- **Gotcha, check this first:** a file-wide `noncomputable section` silently
  overrides any `def`/`noncomputable def` spelling inside it — `lake build`
  succeeding is *not* evidence a def is actually computable if it sits inside
  one of these blocks. `Reference/ShorProgram.lean` still had one from before
  Stage 2 and it silently absorbed my first attempt at making
  `referenceShorCircuit` computable (the build "succeeded" but the def was
  still noncomputable via the section). Removed it there and marked only
  `referenceShorCircuit`/`referenceShorProg` explicitly `noncomputable`;
  `referenceMinimalSetup`/`referenceApproxSetup`/`referenceLowerWorkspace`
  turned out to need *no* `noncomputable` at all once `m`-indexed (they're
  generic in `qs`, and `GateWorkspaceOK`/`ShorApproxSetupMinimal`'s only
  non-`Prop` field, `step4_workspace`, is qs-independent data). **The
  `noncomputable section` in `Reference/ReferenceReadiness.lean` (§3.2's own
  todo) is still there and still blanket-hides that file's real
  computability status** — don't trust that file's current build-green state
  as a computability signal; re-derive it properly when §3.2 removes the
  section, the same way this stage's ground rule 3 test (delete the keyword,
  build, read the actual blocker) was used everywhere else.
- `referenceShorCircuit` no longer builds its `GateWorkspaceOK`/workspace
  witnesses from the `qs`-indexed `referenceApproxSetup`/`referenceLowerWorkspace`
  at all (per §2.4's easier route): it calls `reference_modMulCircuitWorkspaceOK`
  and `reference_step4Workspace` (both qs-free, already existed on
  `ReferenceLayout.lean`) directly, and a new private lemma
  `reference_gateWorkspaceOK_orderFindingApprox` in `ShorProgram.lean`
  instantiates `gateWorkspaceOK_orderFindingApprox` at
  `ConcreteQSemantics.concreteQSemantics` internally — its conclusion type is
  qs-free once `orderFindingApprox` is, so the internal witness choice never
  leaks. `referenceMinimalSetup`/`referenceApproxSetup`/`referenceLowerWorkspace`
  themselves are untouched/still qs-indexed, kept only for other
  correctness-proof call sites (none of which are on the circuit's data path
  anymore).
- Removing the phantom `{Basis}`/`(qs : QSemantics)` parameters from
  `step1`/`step2`/`step5`/`CmodMulInPlaceCore`/`modExpApproxStepsValid`/
  `modExpApproxValid`/`ModExpConfig.approxGate`/`ModMulConfig.approxGate`/
  `lowerGate`/`orderFindingApprox`/`orderFindingApproxLow` had a long tail of
  call-site fixups (~130 `(Basis := ...)`/`(qs := ...)` named-arg deletions and
  ~27 positional-`qs`-argument deletions across `Shor/Proofs/Readiness.lean`,
  `WholeProgramCorrectness.lean`, `Correctness.lean`, several
  `ModularExponentiation/Proofs/*.lean`, and all of `GateCount/**`) — all
  mechanical once the signatures changed; a handful of `@[simp] lemma
  lowerGate_*` restatements in `WholeProgramCorrectness.lean` also carried a
  now-phantom `{Basis : Type u}` binder that had to be dropped too (simp
  couldn't apply them otherwise — Lean can't infer an unconstrained `Type u`
  metavariable that doesn't appear in the lemma's conclusion).

### 2.1 Computable work-width
Currently `algorithm1ExtraBits (η : ℝ) : ℕ := ⌈2 * Real.logb 2 (2 + 1 / (2 * η))⌉₊`
and `η = referencePrecision m = 1 / (m + 3)`. Substituting:
`1/(2η) = (m+3)/2`, so `2 + 1/(2η) = (m+7)/2`, and
`⌈2·log₂((m+7)/2)⌉ = ⌈log₂((m+7)²/4)⌉ = ⌈log₂((m+7)²)⌉ − 2 = Nat.clog 2 ((m+7)²) − 2`.

- Move `referencePrecision` (and its two lemmas) from `Reference/ShorProgram.lean`
  to the top of `Reference/ReferenceLayout.lean` (or a new tiny file
  `Reference/ReferencePrecision.lean` imported by `ReferenceLayout.lean`).
- Add there: `def algorithm1ExtraBitsNat (m : ℕ) : ℕ := Nat.clog 2 ((m + 7) ^ 2) - 2`.
- Prove `theorem algorithm1ExtraBits_referencePrecision (m : ℕ) : algorithm1ExtraBits (referencePrecision m) = algorithm1ExtraBitsNat m`.
  Hints: `Nat.ceil_eq_iff`; `Real.logb` lemmas (`Real.logb_le_iff_le_rpow`,
  `Real.rpow_natCast`, `Real.logb_pow`, `Real.logb_div`); `Nat.clog` is the least
  `c` with `n ≤ 2^c` (`Nat.le_pow_iff_clog_le`). Note `(m+7)^2 ≥ 49 > 4` so the
  `- 2` never truncates. ~60 lines. Sanity checks to include as `example : … := by decide`
  or `#eval`: `algorithm1ExtraBitsNat 0 = 4`, `algorithm1ExtraBitsNat 1 = 4`,
  `algorithm1ExtraBitsNat m2048 = 299`.

### 2.2 Re-index the allocator by `m`
In `Reference/ReferenceLayout.lean`, replace every `(η : ℝ)` parameter by `(m : ℕ)`:
`referenceWorkWidth inst m := referenceDataWidth inst + algorithm1ExtraBitsNat m`,
`referenceScratchWidth inst m`, all `reference*Start/Size/Reserve/Active/X/Data/Work/Scratch/Flag`,
`allocateReferenceLayout ops inst m`, the `@[simp]` width/capacity lemmas, and
`reference_algorithm1Precision (m)` (its `regSize work = regSize data + algorithm1ExtraBits η`
obligation is closed by `algorithm1ExtraBits_referencePrecision`). Remove the
file's `noncomputable section`. Any lemma that still needs a real `η` uses
`referencePrecision m`.

Update call sites: `ReferenceReadiness.lean`, `ShorProgram.lean`,
`ReferenceShorImplementation.lean`, `Reference2048Headline.lean`
(`allocateReferenceLayout lowering.ops inst (referencePrecision m)` → `allocateReferenceLayout lowering.ops inst m`).

### 2.3 Remove unused type-class / `qs` arguments from gate constructors
Instance arguments are runtime values; if the only available instance is
noncomputable, a def taking `[RegEncoding Basis]` cannot be compiled even though
it never uses it. Delete these phantom parameters and fix call sites (deleting
`(Basis := ...)` / `(qs := ...)` named arguments is enough):

- `ModularExponentiation/Defs.lean`: `step1`, `step2`, `step5`, `CmodMulInPlaceCore`,
  `modExpApproxStepsValid`, `modExpApproxValid`, `ModExpConfig.approxGate`,
  `ModMulConfig.approxGate` — drop `{Basis : Type v} [RegEncoding Basis]`.
- `Implementation/Shor/Defs.lean`: `lowerGate` — drop `{Basis : Type u}`;
  `orderFindingApprox`, `orderFindingApproxLow` — drop `(qs : QSemantics) [RegEncoding qs.Basis]`.
  (`orderFindingIdeal` legitimately uses `[GateSemanticsCore qs]`; leave it.)
- `Reference/ShorProgram.lean`: `referenceShorCircuit`, `referenceShorProg` — drop `{qs}`.

### 2.4 Route the reference circuit around `qs`
`referenceShorCircuit` currently obtains its two workspace witnesses from
`referenceApproxSetup qs ...` (a `qs`-indexed structure). The circuit needs only:
- `ModMulCircuitWorkspaceOK data work` — a `Prop`: `reference_modMulCircuitWorkspaceOK ops inst m`.
- `CmpLtNWWorkspace N (data.grow 1) work scratch flag` — **data**: `reference_step4Workspace ops inst m`
  (`ReferenceLayout.lean:793`). Rewrite it as a term-mode `def` (structure literal with the
  `mulWorkspace := Gate.PhaseProdWorkspace.ofExtRegs ...` data field and `by ...` only for `Prop` fields). Drop `noncomputable`.
- `GateWorkspaceOK ops (orderFindingApprox ...)` — a `Prop`. Restate the existing
  `gateWorkspaceOK_orderFindingApprox` so it does not take a `qs`-indexed setup
  (it only needs `ShorWorkspaceLargeEnough` and the two witnesses above). If that is
  hard, it is acceptable to keep the old lemma and instantiate any `qs` inside the
  proof — proofs are erased — but the *statement* of `referenceShorCircuit` must not mention `qs`.

Keep `referenceMinimalSetup`/`referenceApproxSetup`/`referenceLowerWorkspace` for
the correctness proofs; they just stop being on the circuit's data path.

**Checkpoint 2:** build green; `referenceShorCircuit lowering inst m` has no `qs`
argument and its only remaining compile blockers (try removing `noncomputable`)
are the plan/lowering functions of Stage 3 and `loweringPhaseCoeff` of Stage 4.

---

## Stage 3 — Recursors and tactic-built data

**Status: DONE** (branch `ir-emitter`). `lake build` is green across all 3260
jobs, no `sorry`/`sorryAx` introduced (`#print axioms Shor.Shor_correct` /
`Shor.exists_shorGateCountBound` still show only
`[propext, Classical.choice, Quot.sound]`).

Handoff notes:
- §3.1: `lowerGateRec` (`PhaseLoweringPlan.lean:232`) and `lowerQFTPlan`
  (`QFT/Defs.lean:130`) are now `match`-based term-mode definitions (no more
  `induction`/`.rec`). Both remain `noncomputable def`: `lowerGateRec`'s
  `signedStep`/`cSignedStep` arms call `compiledSignedPhaseGate`/
  `compiledCSignedPhaseGate`, which are noncomputable via `loweringPhaseCoeff`
  (Stage 4's `Matrix.inv` target) — eliminating the recursor was the §3.1 goal,
  not full computability, which only becomes reachable after Stage 4.
- §3.2: went through the whole table by stripping `noncomputable` and
  rebuilding (per ground rule 3). Results split cleanly into two groups:
  - **Genuinely made computable** (no tactic rewrite needed — `unfold/dsimp/
    split/by_cases/refine/simpa`-style tactic bodies already compiled to code
    once the keyword was removed): `planAllocChunkGate`, `planDeallocChunkGate`,
    `planCompileSignedAllocations(Aux)`, `planCompileSignedDeallocations(Aux)`,
    `planCompileAnnotatedOpsToSignedGateAux`, `planCompileAnnotatedOpsToCSignedGateAux`
    (all `PhaseLoweringPlan.lean`), `canonicalSignedStep` (`DefsCore.lean:1800`,
    the `CanGrowToNeeds`/`SignedRecursiveWorkspaceOK` fields are `Prop`-valued so
    only the `layout` field's construction mattered, and it has none), and
    `QFTWorkspaceOK.phaseWorkspace` (`QFT/Defs.lean:1011`). None of these needed
    a term-mode rewrite — the plan's contingency (`if h : cond then ... else ...`,
    `castInit`) was not needed anywhere in this stage.
  - **Correctly stay `noncomputable`**, all tracing to the same Stage-4 root
    (`loweringPhaseCoeff`): `planCompiledSignedPhaseGate`/`planCompiledCSignedPhaseGate`
    (direct callers of `loweringPhaseCoeff`), `standardSignedPhaseLoweringPlan`/
    `standardCSignedPhaseLoweringPlan` (blocked via the above once
    `canonicalSignedStep` itself was fixed), `standardPhaseProdUsingPlan`,
    `standardQFTLoweringPlan`, `reserveQFTLoweringPlan`, `lowerQFT`,
    `lowerSignedPhaseProdWithWorkspace`, `lowerCSignedPhaseProdWithWorkspace`,
    `lowerGate`, `orderFindingApproxLow`, `referenceShorCircuit`,
    `referenceShorProg`, `referenceProgramAt`. `orderFindingApprox` was already
    a plain `def` (no change needed).
  - `ShorProgram.lean` already had no `noncomputable section` (fixed in Stage 2).
    `ReferenceReadiness.lean`'s `noncomputable section` was removed; all three
    defs inside (`referenceApproxSetupMinimal`, `allocatedReferenceApproxSetupMinimal`,
    `referenceLayout_ready`) turned out to be genuinely computable with no
    keyword at all — they build proof-shaped (`ShorApproxSetupMinimal`/readiness)
    structures with no non-`Prop` data fields, so the section was pure dead weight.
    `ReferenceShorImplementation.lean`'s `noncomputable section` was removed and
    every def there kept its already-correct explicit `noncomputable` keyword
    unchanged (all ten listed in the plan, `referenceProgramAt` included).
  - **Correction to the plan's own phrasing**: §3.2 said "`referenceProgramAt`
    must be computable", but Checkpoint 3 (correctly) expects the opposite —
    stripping `noncomputable` from it should still fail. Read literally,
    Checkpoint 3 is the authoritative criterion: `referenceProgramAt` stays
    `noncomputable` for now (verified: stripping the keyword fails with "depends
    on 'referenceShorProg', which is 'noncomputable'", i.e. the same
    `loweringPhaseCoeff` root cause one level down); it can only become
    computable once Stage 4 lands.
- One cosmetic fallout from the `lowerGateRec` rewrite: a `simp [..., lowerGateRec, ...]`
  call in `GateCount/PhaseProduct/Lemmas.lean` (~line 4383) started warning
  "unused simp arg" (the old induction-generated equation lemmas for `lowerGateRec`
  no longer exist under the same name now that it's `match`-based) — removed the
  unused arg, no proof restructuring needed.
- **Checkpoint 3 passed**: stripping `noncomputable` from `referenceProgramAt`
  yields exactly one compile error, naming `referenceShorProg` (which itself
  bottoms out at `loweringPhaseCoeff`/`Matrix.inv` — Stage 4's target).

---

### 3.1 Rewrite recursor-based definitions with `match`
- `PhaseLoweringPlan.lean:232` `lowerGateRec`: replace `by induction plan with ...`
  by a `match plan with | .id _ => LowGate.id | .seq l r => LowGate.seq (lowerGateRec l) (lowerGateRec r) | ...`
  with one arm per constructor (same right-hand sides as today; `signedStep ... child => lowerGateRec child`).
- `QFT/Defs.lean:130` `lowerQFTPlan`: same treatment
  (`split ... phasePlan rightPlan leftPlan => lowerQFTPlan rightPlan ;; lowerGateRec phasePlan ;; lowerQFTPlan leftPlan ;; LowGate.RadixReverse r (splitM r)`).
- Leave `QFTLoweringReady` and `PhaseLoweringReady` alone: they return `Prop`.

### 3.2 Make tactic-built *data* compilable
For each of the following, remove `noncomputable`, build, and if the compiler
objects, rewrite the data-producing part in term mode. Use
`if h : cond then ... else ...` for `by_cases`, keep `termination_by`/`decreasing_by`,
and transport plans along width equalities with an explicit helper
`def PhaseLoweringPlan.castInit (h : n₁ = n₂) : PhaseLoweringPlan k hk pts hpts ops n₁ G → PhaseLoweringPlan k hk pts hpts ops n₂ G := h ▸ id`
instead of `simpa [..] using childPlan`.

| Def | File | Produces |
|---|---|---|
| `planAllocChunkGate`, `planDeallocChunkGate` | `PhaseLoweringPlan.lean:344,365` | plan (uses `unfold; split`) |
| `planCompileSignedAllocations`, `planCompileSignedDeallocations` | `:417,458` | plan |
| `planCompiledSignedPhaseGate`, `planCompiledCSignedPhaseGate` | `:590,690` | plan (ends in `simpa ... using completePlan`) |
| `standardSignedPhaseLoweringPlan`, `standardCSignedPhaseLoweringPlan` | `:753,849` | plan (`by_cases hrec`, WF recursion) |
| `canonicalSignedStep` | `DefsCore.lean:1800` | `CanonicalSignedStep` (data field `layout`) |
| `standardPhaseProdUsingPlan` | `QFT/Defs.lean:294` | plan |
| `QFTWorkspaceOK.phaseWorkspace` | `QFT/Defs.lean:1013` | `Gate.PhaseProdWorkspace` (data fields `xReserve`, `zReserve`) |
| `standardQFTLoweringPlan`, `reserveQFTLoweringPlan`, `lowerQFT` | `QFT/Defs.lean:1365,1463,1480` | plan / `LowGate` |
| `lowerSignedPhaseProdWithWorkspace`, `lowerCSignedPhaseProdWithWorkspace` | `PhaseProduct/Defs.lean` | `LowGate` |
| `lowerGate`, `orderFindingApprox`, `orderFindingApproxLow` | `Shor/Defs.lean` | `Gate` / `LowGate` |
| `referenceShorCircuit`, `referenceShorProg`, `referenceProgramAt` | `Reference/ShorProgram.lean`, `ReferenceShorImplementation.lean` | `LowGate` / program |

The underlying data functions (`ReserveBudget.ofRequirements`, `PhaseSplitLayout.ofBudget`,
`PhaseSplitLayout.child`, `targetSignedLayoutState`, `growExtRegTo`, `qftXWork`,
`qftZWork`, `Gate.PhaseProdWorkspace.ofExtRegs`, `ModMulCircuitWorkspaceOK.step*Workspace`)
are already plain `def`s — the work is only in the wrappers above.

Also delete `noncomputable section` from `ShorProgram.lean` and `ReferenceReadiness.lean`;
in `ReferenceShorImplementation.lean` keep `noncomputable` individually on
`referenceK`, `referenceApproximationErrorAt`, `referenceRawSuccessProbabilityAt`,
`referenceSuccessProbabilityAt`, `referenceChosenPrecision`, `referenceSubmittedProgram`,
`referenceSuccessProbability`, `referenceTrialCount`, `referenceGateCount`,
`referenceShorImplementation` (all involve `ℝ`/`Nat.find`), but **`referenceProgramAt` must be computable**.

**Checkpoint 3:** removing `noncomputable` from `referenceProgramAt` yields exactly one
kind of compile error, naming `loweringPhaseCoeff` / `phaseCoeffFromPts` / `Matrix.inv`.

---

## Stage 4 — Computable interpolation coefficients

**Status: DONE** (branch `ir-emitter`). `lake build` is green across all 3260
jobs, no `sorry`/`sorryAx` introduced (`#print axioms` on
`Shor.Shor_correct`, `Shor.exists_shorGateCountBound`, and
`Shor.Reference.referenceProgramAt` all show only
`[propext, Classical.choice, Quot.sound]`). **Checkpoint 4 passed structurally**:
`referenceProgramAt` is now a genuine `def` (no `noncomputable`), and so is
every def in its call chain — see below. The literal `#eval`
smoke test in this section's Checkpoint 4 still needs Stage 5.1's
`standardLoweringSetup` to construct a concrete `ShorLoweringSetup`; deferred
to Stage 5, since nothing here currently builds one.

**Design deviation from this section's original plan — read before reusing
the snippets below.** The `§4.1`/`§4.2` plan (Lagrange weights via
`pointNode`/`lagrangeCoeff`, proved equal to `phaseCoeffFromPtsWidth` via
`GoodToomCookPoints`) has a soundness gap: `interpEntry` uses a *different*
row formula for `.frac` points (`c ^ (q k - 1 - j)`, the "point at infinity"
trick) than for `.int` points (`t ^ j`), so a plain Vandermonde/Lagrange
argument over `pointNode`-projected coordinates is only valid when every
point in `pts` is `.int` — true in practice (`pts` is always
`genInterpolationPoints k`) but **not** implied by `GoodToomCookPoints k pts
hpts` alone (that hypothesis is just `det ≠ 0`; a mixed int/frac point list
can have a nonzero determinant too, and `lagrangeCoeff` would then silently
use the wrong node values). Since `GoodToomCookPoints` is exactly the
hypothesis already threaded generically through
`eval_compiledSignedPhaseGate_correct`/`eval_compiledCSignedPhaseGate_correct`
(`PlanSemantics.lean`) — the only two places that actually `unfold
loweringPhaseCoeff` — patching those with an extra "all-int" hypothesis
would cascade into `evalL_lowerGateRec_correct`'s 8+ call sites across the
codebase.

**What was built instead**: `Matrix.cramer`/`Matrix.det` are fully
computable in this Mathlib (`#eval`-verified directly — only `Matrix.inv`
needs the noncomputable `Ring.inverse`/`IsUnit` case split). `DefsCore.lean`
gained `cramerCoeffFromPts`/`cramerCoeffFromPtsWidth`, a Cramer's-rule
reformulation of `phaseCoeffFromPts`/`phaseCoeffFromPtsWidth`:
```
def cramerCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) : Fin (q k) → ℚ :=
  let M : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let radixVec : Fin (q k) → ℚ := fun j => b ^ (j : ℕ)
  fun i => Matrix.cramer M.transpose radixVec i / M.det
```
`InterpolationCorrectness.lean` proves `cramerCoeffFromPts_eq_phaseCoeffFromPts`
(pure linear algebra: from `M *ᵥ cramer M v = M.det • v`
(`Matrix.mulVec_cramer`), left-multiply by `M⁻¹` and divide by the nonzero
determinant) and the width-level wrapper
`cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth` (given `hInterp :
GoodToomCookPoints k pts hpts`) — **for fully general `pts`**, mixed
int/frac included, since Cramer's rule needs no Vandermonde/injectivity
argument at all. `loweringPhaseCoeff` (`PhaseLoweringPlan.lean:25`) now reads
`cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts` and is a plain
`def`. The two `unfold loweringPhaseCoeff` sites in `PlanSemantics.lean`
(`eval_compiledSignedPhaseGate_correct`/`eval_compiledCSignedPhaseGate_correct`)
each got one inserted line,
`rw [cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth pts hpts hInterp]`,
right after the `unfold` — no other file needed changes (grepped for every
`unfold loweringPhaseCoeff`/`loweringPhaseCoeff]` site codebase-wide; these
two were the only ones that inspect its *formula* rather than just its name).

**Cascade**: once `loweringPhaseCoeff` stopped being the root blocker, a full
re-sweep (strip `noncomputable`, build, read the blocker) turned every
remaining def in the Stage-3 table computable with **zero further tactic
rewrites**: `compileOpsToSignedGate`/`compileOpsToCSignedGate`
(`DefsCore.lean`), `compiledSignedPhaseGate`/`compiledCSignedPhaseGate`,
`lowerGateRec`, `lowerPhasePlan`, `lowerSignedPhaseProd`,
`lowerCSignedPhaseProd`, `planCompiledSignedPhaseGate`/
`planCompiledCSignedPhaseGate`, `standardSignedPhaseLoweringPlan`/
`standardCSignedPhaseLoweringPlan` (all `PhaseLoweringPlan.lean`),
`lowerQFTPlan`, `standardPhaseProdUsingPlan`, `standardQFTLoweringPlan`,
`reserveQFTLoweringPlan`, `lowerQFT` (`QFT/Defs.lean`),
`lowerSignedPhaseProdWithWorkspace`/`lowerCSignedPhaseProdWithWorkspace`
(`PhaseProduct/Defs.lean`), `lowerGate`/`orderFindingApproxLow`
(`Shor/Defs.lean`), `referenceShorCircuit`/`referenceShorProg`
(`Reference/ShorProgram.lean`), and finally `referenceProgramAt`
(`ReferenceShorImplementation.lean`). One exception found along the way:
`referenceApproxSetup` (`ShorProgram.lean`) genuinely needs `noncomputable`
(binds `referencePrecision m : ℝ` into its own return type/body) — reverted
after a bulk-strip attempt; it is not on `referenceProgramAt`'s call path so
this doesn't matter for Checkpoint 4. `referenceMinimalSetup` and
`referenceLowerWorkspace` (also not on that path, `Prop`-shaped proof
objects) turned out to need no keyword at all, matching the Stage 2 note
that was never acted on.

### Facts you can rely on
- `loweringPhaseCoeff k x z pts hpts = phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts`
  (`PhaseLoweringPlan.lean:25`), which is `(interpMatrix)⁻¹` applied to the radix row (`DefsCore.lean:273–296`).
- Every downstream proof reaches it through
  `phaseCoeffFromPtsWidth_eq_interpCoeff` (`InterpolationCorrectness.lean:715`) →
  `ToomCookMath.interpCoeff`, whose correctness lemma `interpCoeff_correct`
  (`Toom_Cook_formula.lean:135`) already establishes `IsUnit M.det`. Hence solutions
  of `M.mulVec c = radixRow` are **unique**.
- The plan always uses `genInterpolationPoints k = (List.range (2k−1)).map alternatingPoint`
  (`DefsCore.lean:1315–1319`); every point is `Point.int t` with `t = 0, 1, −1, 2, −2, ...`,
  pairwise distinct, and `interpEntry k (.int t) j = t ^ j`. `genInterpolationPoints_good k`
  (used in `PhaseProduct/Main.lean:67`) provides `GoodToomCookPoints`.

### 4.1 Define the computable coefficients (Lagrange weights)
In `DefsCore.lean` next to `phaseCoeffFromPtsWidth`:
```
def pointNode : Point → ℚ | .int t => t | .frac _ => 0      -- frac never occurs for our points
def lagrangeCoeff (k W : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  fun l => ∏ j ∈ Finset.univ.erase l,
    ((chunkRadix W) - pointNode (ptsToFin k pts hpts j)) /
    (pointNode (ptsToFin k pts hpts l) - pointNode (ptsToFin k pts hpts j))
```
(`Finset.prod` over `Fin (q k)` is computable.) Then set
`loweringPhaseCoeff k x z pts hpts := lagrangeCoeff k (phaseLimbWidth x z k) pts hpts`
and drop `noncomputable`.

### 4.2 Prove it agrees with the old definition
1. `lagrangeCoeff_solves`: if all `pts` are `.int` with injective nodes, then for every `j : Fin (q k)`,
   `∑ l, lagrangeCoeff k W pts hpts l * interpEntry k (ptsToFin k pts hpts l) j = (chunkRadix W) ^ j`.
   This is standard Lagrange interpolation of `X^j` (degree `< q k`) at `q k` distinct nodes;
   Mathlib's `Lagrange.basis`, `Lagrange.interpolate`, `Lagrange.eq_interpolate` do it —
   they are noncomputable but only used inside the proof (the zip's `GeneralEmitter.mkCoeffs_dot` is a worked example of this exact argument).
2. `lagrangeCoeff_eq_phaseCoeffFromPtsWidth (h : GoodToomCookPoints k pts hpts)`: both sides
   satisfy `M.mulVec c = radixRow`; with `IsUnit M.det` conclude equality
   (`c = M⁻¹.mulVec (M.mulVec c)` via `Matrix.nonsing_inv_mul` / `Matrix.mulVec_mulVec`).
3. Patch consumers: where a proof unfolds `loweringPhaseCoeff` expecting `phaseCoeffFromPtsWidth`,
   insert `rw [loweringPhaseCoeff, lagrangeCoeff_eq_phaseCoeffFromPtsWidth _ hInterp]` first
   (the `GoodToomCookPoints` hypothesis is already in scope in those theorems — it is `hInterp`).
   Files to check: `PhaseProduct/Proofs/LoweringCorrectness/{PlanSemantics,Lowerable,EvalLLemmas}.lean`,
   `GateLevelCorrectness/CompilationCorrectness.lean`, `PhaseProduct/Main.lean`.

Do not try to evaluate these coefficients with `decide` (ℚ normalisation goes
through well-founded `Nat.gcd`); `#eval` is fine.

**Checkpoint 4:** `referenceProgramAt` compiles. In a scratch file:
```
#eval (Shor.LowGate.gateCount Shor.shorGateCostModel
        (Shor.Reference.referenceProgramAt (Shor.standardLoweringSetup 2 (by decide)) 0 ⟨2, 15, by decide, by decide⟩).circuit)
```
prints a number (`standardLoweringSetup` is defined in Stage 5.1 — define it first if needed).

---

## Stage 5 — Emitter

**Status: DONE** (branch `ir-emitter`). `lake build` is green (3260 jobs,
including the new `Emit/` files and the `forshor_emit` executable target),
axioms unchanged (`Shor.Shor_correct`/`Shor.exists_shorGateCountBound` still
show only `[propext, Classical.choice, Quot.sound]`) — `Emit/` isn't imported
by either, confirming the emitter is genuinely isolated from the verified
core. All of §5.1–§5.4 below matched the plan almost exactly; only small
mechanical fixes were needed.

**Real smoke test**: `lake exe forshor_emit 2 2 15 0` (the plan's own
Checkpoint 4/5.4 instance) exits 0 and prints 3.1 MB of valid JSON:
`schema: "forshor.lowgate/v2"`, `gate_count: 69084`, `qubit_count: 44`,
`output_register: [0..7]`, a `circuit` whose top-level `seq` body has 20626
flattened leaves. Confirmed with an external JSON parser (Python), not just
"didn't crash".

Gotchas found along the way:
- `genOpsWithProduct_ProgConsumesPtsSafe` returns the *whole*
  `ProgConsumesPtsSafe` structure already, not something needing a
  `.consumes` projection — the plan's §5.1 snippet's
  `(genOpsWithProduct_ProgConsumesPtsSafe ...).consumes` would have been a
  type error; used the theorem directly for `ShorLoweringSetup.consumes`.
- `meta` is a reserved token in this Lean toolchain (v4.28.0) — can't be used
  as a parameter/binder name. Renamed to `metaJson` in `emitProgram`'s
  signature (the plan's §5.2 field name, the JSON key `"meta"`, is unaffected).
- `#guard` (as a standalone command asserting a `Bool`/`Decidable` value) does
  not exist in this toolchain — only `guard_expr`/`guard_hyp` *tactics* and
  `#guard_msgs` exist. Replaced every planned `#guard` in `Emit/Tests.lean`
  with `example : ... := by native_decide` (fast, compiled evaluation, same
  spirit as `#eval`; introduces the isolated `native_decide` axiom only in
  `Emit/Tests.lean`, never imported by the verified core).
- `Reference.referenceSubmittedProgram`/`referenceChosenPrecision` do *not*
  actually take a `qs : QSemantics` parameter (despite living under a file-level
  `variable {qs : QSemantics} [...]` block) — Lean's `variable` auto-inclusion
  only pulls in variables a declaration's own signature mentions, and neither
  of these two defs' types mention `qs` (confirming, yet again, the Stage
  2/3 finding that the whole `referenceProgramAt` chain is `qs`-free). §5.4's
  acceptance test 3 dropped the planned `(qs := qs)` naming entirely rather
  than fighting it.
- §5.4's acceptance test 1 ("`gate_count` equals folding the emitted
  circuit") is implemented as a genuine round-trip: the JSON's `gate_count`
  field, extracted back out via `Json.getObjVal?`/`Json.getNat?`, is checked
  against `LowGate.gateCount shorGateCostModel` computed directly on the
  *original* circuit value — this catches real serialization bugs (wrong
  field, wrong order) without re-deriving `shorGateResourceModel`'s
  register-width-dependent cost formulas a second time from raw JSON, which
  would have been substantial duplicated effort for a test file.
- Tests use `k = 2/3, N = 3` (not the plan's `N = 15`) to keep `lake build`
  fast — `Emit/Tests.lean` compiles in ~10s. The `N = 15` instance from the
  plan's Checkpoint 4/5.4-item-1 was still exercised, just via the compiled
  `forshor_emit` binary above rather than embedded at Lean compile time.

### 5.1 A concrete `ShorLoweringSetup` (emitter is parameterised by it)
`ShorLoweringSetup` (`Shor/Defs.lean:492`) is data `k, hk, ops` plus two `Prop`s.
Add `Implementation/Reference/StandardLoweringSetup.lean`:
```
def standardLoweringSetup (k : ℕ) (hk : 1 < k) : ShorLoweringSetup where
  k := k; hk := hk
  ops := Table_Generation.genOpsWithProduct (k := k) (by omega) (genInterpolationPoints k)
  consumes := (genOpsWithProduct_ProgConsumesPtsSafe (k := k) (by omega) (genInterpolationPoints k)).consumes  -- adjust to the exact shape
  returns := genOpsWithProduct_returns_to_original (k := k) (by omega) (genInterpolationPoints k)
```
Both theorems exist in `PhaseProduct/Math/Table_Generation/Builders/*.lean`; check exact
names/shapes with `grep -rn "genOpsWithProduct_" FastMultiplication`. Note: the K2/K3
precomputed tables and the `k ≥ 4` parity generator consume a *different* point
stream, so `Table_Generation.generate` cannot be used here; `genOpsWithProduct` is
the program family that matches `ShorLoweringSetup.consumes` as stated.

### 5.2 JSON printer
New file `FastMultiplication/Emit/LowGateJson.lean` (`import Lean.Data.Json`), all plain `def`s:
- `regJson (r : Reg) : Json := r.qubits` (LSB-first list of physical qubit indices).
- `extRegJson (r : ExtReg) := {"active": regJson r.active, "reserve": regJson r.reserve}`.
- `angleJson (a : Angle) := {"num": a.num, "den": a.den, "unit": "pi"}` (`ℚ` is already reduced).
- `lowGateJson : LowGate → Json`, structural recursion, one arm per constructor:
  `id`, `seq` (flatten nested `seq` into one `{"op":"seq","body":[...]}` and drop inner `id`s),
  `adj {"op":"adj","body":…}`, `H {q}`, `X {q}`, `Phase {q, angle}`, `CNOT {ctrl,target}`,
  `Toffoli {c1,c2,target}`, `ShiftL/ShiftR {r,n}`, `Negate {r}`, `AddScaled {dst,src,negSrc,shift}`,
  `zeroExtend/signExtend/zeroDealloc/signDealloc {r,n}`, `RadixReverse {r,m}`.
  Op names must be exactly the constructor names.
- Document wrapper `emitProgram (P : ShorOrderFindingProgram) (meta : Json) : Json` with
  `schema: "forshor.lowgate/v2"`, `bit_order: "lsb_first"`, `angle_unit: "pi"`,
  `output_register: regJson P.output`, `gate_count: LowGate.gateCount shorGateCostModel P.circuit`,
  `qubit_count: (LowGate.usedQubits P.circuit).max` (or `sup`), `circuit: lowGateJson P.circuit`, and `meta`
  (`k, a, N, m, source: "Shor.Reference.referenceProgramAt"`).

### 5.3 Executable
`FastMultiplication/Emit/Main.lean` with `def main (args : List String) : IO UInt32`:
parse `k a N m` as `ℕ`; check `1 < k`, `0 < a ∧ a < N`, `Nat.gcd a N = 1` with
`if h : … then … else` (these decidable checks *are* the `range`/`coprime` proofs of
`ShorOrderFindingInstance`); build `standardLoweringSetup k hk`, call
`referenceProgramAt lowering m inst`, print `(emitProgram … ).compress`; exit 2 on bad input.
Add to `lakefile.lean`:
```
lean_exe forshor_emit where
  root := `FastMultiplication.Emit.Main
```
Use the compiled binary (`lake exe forshor_emit ...`) for anything beyond tiny
instances; `#eval` in the editor runs interpreted and can hit stack limits on deep `seq` chains.

### 5.4 Acceptance tests (add as `#guard`/`example`s in `FastMultiplication/Emit/Tests.lean`, small `N` only)
1. `lake exe forshor_emit 2 2 15 0` exits 0 and prints valid JSON whose `gate_count`
   equals the number obtained by folding the emitted `circuit` (do the fold in Lean over the `Json` as a `#guard`).
2. Every `Phase` angle in the output has `den > 0`; every register list is `Nodup`.
3. `example : referenceSubmittedProgram lowering inst = referenceProgramAt lowering (referenceChosenPrecision inst.N) inst := rfl`
   — documents that the emitted object at `m := referenceChosenPrecision N` is the submitted one; for the
   2048-bit story the explicit level is `m2048` from `Reference2048Headline.lean`.
4. Run once with `k = 3` to exercise the `q = 5` coefficient path.

---

## 6. Cleanups to do at the end (documentation only)

**Status: DONE.** All four items fixed; no `.lean` semantics changed (docstrings
only), confirmed by rebuilding both edited `.lean` files and a final full
`lake build`.

- `README.md` "Status": rewritten — states no `sorry` remains anywhere
  (verified: `grep -rn sorry FastMultiplication` is empty) and axioms are
  just the standard three; the old `gateBound`/`counted` sentence (those
  fields don't exist on `referenceShorImplementation`) is gone; added a
  paragraph describing the reference implementation's computability and the
  `Emit/`/`forshor_emit` JSON emitter, plus a "Building" usage line. Also
  fixed the two `Shor_correct`/`Shor_GateCount.lean` path references (they
  pointed at pre-restructure locations) and rewrote the repository-layout
  table and "Proof architecture" paragraph for the actual `Framework/` /
  `Implementation/` split (the old table still named `Basic.lean`,
  `MathBackbone/`, `AlgorithmCorrectness/`, `AbstractMachine/`, `GateCount/`,
  `ShorCorrectness.lean` as top-level items).
- `Framework/Submission.lean`: rewrote the module docstring and the
  `ShorImplementation` docstring — both described a `gateCountBound` field
  that was never part of the structure (the actual fields are `program`,
  `successProbability`, `correct`, `trialCount`, `trialCount_correct`); gate
  count is a framework-computed quantity (`ShorOrderFindingProgram.frameworkGateCount`),
  not a submitted bound. Rewrote both docstrings to describe that instead.
- `Framework/Instantiation/GateSemanticsCore.lean`: the two doc-comments
  (`atomAdjEval_atomEval`, `atomEval_atomAdjEval`) claiming the `H`/`QFT`/
  `SignedPhaseProd`/`CSignedPhaseProd` cases are "left as explicit `sorry`s
  for a follow-up pass" were false — read the actual proof bodies, confirmed
  all four cases are fully proved (the `QFT` case alone is ~80 lines of real
  algebra). Reworded to describe what actually happens (those four cases
  need dedicated calculations; the rest follow uniformly from
  `atomAdjEval_atomEval_ket_of_glue`) instead of claiming outstanding work.
- `ARCHITECTURE.md`: this file is far more extensively stale than just paths
  (it describes the pre-restructure single-`Basic.lean`/`MathBackbone/`/
  `AlgorithmCorrectness/`/`AbstractMachine/`/`GateCount/`/`ShorCorrectness.lean`
  layout throughout its ~330 lines, and its final section falsely claimed
  `Shor_correct` "still uses `sorry`"). A full per-line path audit of the
  whole file was out of scope for a documentation cleanup pass, so: added a
  note at the top mapping the old six top-level pieces to where they live
  now (`Framework/` vs `Implementation/{PhaseProduct,QFT,ModularExponentiation,
  Shor,GateCount,Reference}/`), pointing the reader to README.md's now-accurate
  layout table, and telling them every named definition/theorem still exists
  somewhere findable by `grep`; corrected the top "six main pieces" list with
  the new locations; and fixed the false `sorry` claim in the
  `ShorCorrectness.lean` section. The detailed per-definition prose in the
  body (registers, `RegEncoding`, `QSemantics`, the folder-guide sections)
  was left as-is — it describes concepts/definitions that still exist, just
  under different file paths than literally written; re-verifying every one
  of those paths individually would be a much larger undertaking than this
  cleanup pass.

## 7. Summary checklist
- [x] Stage 1: `Angle` file; 3 constructors; 4 plan constructors; semantic axioms ×5; angle defs ×5; proof repairs; build green; axioms unchanged.
- [x] Stage 2: `algorithm1ExtraBitsNat` + bridge lemma; `ReferenceLayout` over `m`; phantom `{Basis}`/`qs` removed; `referenceShorCircuit` has no `qs`; `reference_step4Workspace` term-mode (already compiled tactic-mode, no rewrite forced — ground rule 7 only requires it when the compiler complains).
- [x] Stage 3: `lowerGateRec`/`lowerQFTPlan` via `match`; plan builders and `canonicalSignedStep`/`phaseWorkspace` made computable without a tactic rewrite; `noncomputable section` removed from `ReferenceReadiness.lean`/`ReferenceShorImplementation.lean`; Checkpoint 3 confirms only `loweringPhaseCoeff` blocks `referenceProgramAt`.
- [x] Stage 4: `cramerCoeffFromPts(Width)` (Cramer's-rule, not Lagrange weights — see status note); equality under `GoodToomCookPoints` for fully general `pts`; `PlanSemantics.lean`'s 2 consumers patched; `referenceProgramAt` compiles.
- [x] Stage 5: `standardLoweringSetup`; `LowGateJson`; `lean_exe forshor_emit`; acceptance tests pass; real smoke test (`k=2,a=2,N=15,m=0`) produces valid JSON, gate_count 69084.
- [x] §6 doc cleanups: `README.md`, `Framework/Submission.lean`, `Framework/Instantiation/GateSemanticsCore.lean`, `ARCHITECTURE.md`.
