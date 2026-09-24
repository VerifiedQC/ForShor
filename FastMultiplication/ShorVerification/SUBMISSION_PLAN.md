# PLAN: a submission is a table and a set of interpolation points

Status: 2026-09-24. Owner decisions in §1. **All stages done** (S1 committed
as `b4856a5`; S2–S6 committed on top of it on `ir-reflection-r0`); see the
checklist in the last section. Open follow-up outside this repo: the
submissions repo's own lakefile around its copy of `Submission/Template.lean`.
The S1 site inventory (§5) was taken from the tree at commit `c045219`.

## 0. What changes and why

Until now the public boundary was `Framework/Submission.lean`'s
`ShorImplementation`: a submitter hands in an arbitrary `LowGate` circuit
family plus its own correctness proof, and the framework computes the gate
count in Lean (`frameworkGateCount`). Resource estimation is moving to
Qualtran, fed by `Emit/`'s reflected IR. The IR extractor only understands
the *reference* construction (`referenceProgramAt`), so an arbitrary
circuit can no longer be scored. The challenge therefore narrows to the one
degree of freedom the reference construction actually exposes:

> A submission is a Toom-Cook table (`ops : Prog k`) together with the
> interpolation points it evaluates at (`pts : List Point`), packaged as a
> `ShorLoweringSetup`. Lean checks the pair, the reference construction turns
> it into `referenceProgramAt`, the emitter turns that into IR, Qualtran
> prices the IR.

Correctness is then *one* theorem proven once for every submission
(`referenceProgramAt_success` is already generic in the `ShorLoweringSetup`).
Per submission, Lean only has to discharge four decidable side conditions
(§3). The `ShorImplementation` structure survives as the framework's internal
correctness contract: every accepted submission yields one
(`referenceShorImplementation lowering`), it just stops being what a
submitter writes.

Two structural changes make this work:

1. **The points become a parameter (S1, done).** The lowering chain used to
   hard-wire the canonical ladder `genInterpolationPoints k`
   (`0, -1, 1, -2, 2, …`) into the types of the plan builders and every
   correctness hypothesis. S1 threaded `pts` through.
2. **The rules move below the implementation (S2.0).** Under P1 the challenge
   is *defined* in terms of tables and points, so the vocabulary needed to
   state a submission — the table language, the point rows, the
   interpolation condition, and the `ShorLoweringSetup` record itself — is
   part of the rules, not of one implementation. It moves into a single
   implementation-free file, `Framework/ToomCookTable.lean`, that imports
   only Mathlib. Everything that *uses* those definitions (lemmas, the table
   generator, the compiler, the correctness proofs) stays in
   `Implementation/`.

## 1. Decisions (owner)

| # | decision |
|---|---|
| P1 | **Submitter-chosen points.** Both `ops` and `pts` are submission data. The canonical ladder becomes the reference's choice, not the framework's. (The points are in fact recoverable from `ops` via C3; keeping them as an explicit field, checked by `native_decide`, was preferred over a `pointsOf ops` function plus its bridging lemma.) |
| P2 | **A submission is a PR** to a separate submissions repo. That repo depends on this one. This repo's job is to make "clone, drop in one Lean file, `lake build`" the whole check. No JSON table parser on the Lean side: the kernel checks the table, not a parser. |
| P3 | **Fixed precision `m`.** The organiser fixes one `m` (default: the existing `m2048 = 2^150 - 3`). The declared success bound is `referenceSuccessProbabilityAt m N`, the trial count is the smallest amplifying that to 99%. Both are *independent of the table*, so they are a per-`N` constant, computed once. |
| P4 | **Score** `= trialCount × (Qualtran single-run gate count of the emitted IR)`. Lean's `frameworkGateCount`/`headlineGateCount` stop being the scored quantity; they remain as the verified asymptotic story. |
| P5 | **No per-submission IR theorem.** Acceptance is the evaluation tier (§9, S4.2): kernel-checked side conditions plus `instantiate = real` verified by evaluation at sampled widths. The R6 extractor-correctness proofs (k = 2 reference table only) were archived to branch `emit-proofs-archive` (commit `2218ba6`) and removed; they are not a submission requirement. |
| P6 | `FastMultiplication/Qualtran/` deleted (done, staged). Qualtran-side code lives in the submissions repo. |
| P7 | **The submission is the `ShorLoweringSetup` record itself** (data + the four proof fields), not a data-only wrapper converted by a checker. The template pre-fills every proof field with `by native_decide`, so a submitter edits three definitions (`k`, `pts`, `ops`). A `{k, pts, ops}` record with `toSetup?` stays possible later if raw `native_decide` failures prove confusing. |
| P8 | **The rules live in `Framework/`, as one file.** `Framework/ToomCookTable.lean` holds the minimal definitions needed to state `ShorLoweringSetup` and the record itself; it imports only Mathlib. Lemmas, generator, compiler and proofs stay in `Implementation/` and import it back. The certificate theorem, which necessarily mentions the reference construction, lives in `Submission/Correct.lean`. |

## 2. Ground rules

1. Commit S1 on `ir-reflection-r0` before starting S2.0. Build after every
   stage with `lake build` (whole library) and `lake build EmitTests
   forshor_emit`. No `sorry`. `#print axioms` on `Shor.Shor_correct`,
   `referenceSubmittedProgram_correct`, `exists_shorGateCountBound` must stay
   `propext`/`Classical.choice`/`Quot.sound` only.
2. Generalisations and moves preserve definitional behaviour: the standard
   setup stays `pts := genInterpolationPoints k`, and moved definitions keep
   their fully-qualified names, so every pinned `Doc`, every R2
   `native_decide` test and `template 2`'s output stay byte-identical.
3. Layering (see §4). `Framework/` never imports `Implementation/`, `Submission/`
   or `Emit/`. `Submission/Decide`, `Correct` and `Score` sit above
   `Implementation/Reference/` and below `Emit/`; `Submission/Template` sits
   above `Emit/`. The layer scripts under `scripts/check_*_layers.sh` must
   stay green (they already allow `Framework/` imports).
4. Delete superseded mechanisms in the stage that supersedes them (the
   Emit-side `Table/Decide.lean` copy in S2.1; the old definition sites in
   S2.0).

## 3. The specification: what Lean checks about a submission

Let `k > 1` be the table arity and `q k = 2k - 1`. A submission is a value of
the record (after S2.0 it lives in `Framework/ToomCookTable.lean`)

```lean
structure ShorLoweringSetup where
  k        : ℕ
  hk       : 1 < k
  pts      : List Point
  hpts     : pts.length = q k                                                    -- (C1)
  good     : GoodToomCookPoints k pts hpts                                       -- (C2)
  ops      : Prog k
  consumes : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts  -- (C3)
  returns  : run? ops State.start_state = some State.start_state                -- (C4)

abbrev ShorSubmission := ShorLoweringSetup
```

and the four conditions, all decidable at concrete `k`, `ops`, `pts`:

| | condition | meaning | where it is consumed |
|---|---|---|---|
| C1 | `pts.length = 2k - 1` | one point per product coefficient | every `PhaseLoweringPlan` index |
| C2 | `det (interpMatrix k pts) ≠ 0` | the points interpolate a degree-`2k-2` polynomial. Row for `int z` is `[1, z, …, z^(2k-2)]`; `frac c` means the point `1/c`, row `[c^(2k-2), …, c, 1]`; `frac 0` is the point at infinity | `evalL_lowerGateRec_correct`'s `hInterp`, `PhaseProductProgramOK` |
| C3 | `ProgConsumesPtsSafe … ops pts` | running `ops` from the start state, the `i`-th `phaseProduct r` checkpoint finds register `r` holding exactly the `k`-entry row of `pts[i]` (`[1, z, …, z^(k-1)]` or `[c^(k-1), …, 1]`), all points are consumed, and no `addScaled` has `dst = src`. **Order matters**: leaf `l` receives coefficient `l`. | every `hC` hypothesis on the chain |
| C4 | `run? ops start = some start` | the table uncomputes itself; every right shift is exact | every `hRun` hypothesis |

Nothing else looks at the points: the compiler only scales the phase angle by
the rational coefficient (`Compile.lean:133`), and `Widths`, `Workspace`,
`Layout` never mention them. The emitted IR does not depend on the point
values either: a leaf's angle is the opaque `AExpr.coeff l m`, resolved only
at instantiation. `PhaseProductProgramOK`'s extra clause
`phaseProductCount ops = q k` follows from C1 + C3.

Decidability: C3 and C4 already have instances (`Emit/Table/Decide.lean`,
R5). C2 needs one new instance (S2.1); `det` over `ℚ` is a finite sum over
`(2k-1)!` permutations, so `native_decide` is instant through `k = 5`
(9! = 362 880 terms) and slow but feasible at `k = 6`. C1 is `rfl`.

## 4. Where things live (target layout)

```
Framework/                    what "correct Shor" means; imports no Implementation/
  ToomCookTable.lean          NEW (S2.0): table language, point rows, C1–C4 vocabulary,
                              ShorLoweringSetup, ShorSubmission. Mathlib only.
  Contract.lean               renamed from Submission.lean (S3.3): ShorImplementation
Implementation/…              the Toom-Cook construction; imports Framework/ToomCookTable
  Reference/                  setup ↦ referenceProgramAt, referenceProgramAt_success
Submission/                   the public surface the submissions repo builds against
  Decide.lean                 S2.1: decision procedures for C2–C4
  Correct.lean                S2.2: submissionPrecision, submission_correct (imports Reference/)
  Score.lean                  S3: success bound, computable trial count
  Template.lean               S4: the file a submitter copies (imports Emit/)
  Main.lean                   S4: forshor_submission's printer (not edited by submitters)
Emit/                         setup ↦ IR
```

## 5. Stage S1 — thread the points through the verified chain (done)

Site inventory as taken at `c045219`: occurrences of `genInterpolationPoints`
/ `generatedInterpolationPoints_length` / `genInterpolationPoints_good`
outside `Math/Table_Generation/` (which legitimately builds the canonical
table and stays as is):

| file | count | kind of edit |
|---|---|---|
| `Implementation/Shor/Spec/Setup.lean` | 1 | the record itself (§3) |
| `Implementation/PhaseProduct/Lowering/PlanBuilders.lean` | 20 | `standardSignedPhaseLoweringPlan` / `standardCSignedPhaseLoweringPlan` take `pts hpts`; `recurse`'s stated type uses them |
| `Implementation/PhaseProduct/Lowering/Plan.lean` | 3 | `generatedInterpolationPoints_length` stays; `StandardPhaseLoweringPlan` abbreviation gains `pts` |
| `Implementation/PhaseProduct/Spec/Assertions.lean` | 2 | `hC` against `pts` |
| `Implementation/PhaseProduct/Main.lean` | 2 | `hInterp` from the setup instead of `genInterpolationPoints_good` |
| `Implementation/PhaseProduct/Proofs/Lowering/Correctness.lean` | 3 | same |
| `Implementation/PhaseProduct/Proofs/Lowering/Linearity.lean` | 3 | same |
| `Implementation/PhaseProduct/Proofs/Lowering/PlanReadiness/RecursiveReadiness.lean` | 13 | same, plus `pts` argument to the plan builder calls |
| `Implementation/QFT/Spec/Assertions.lean` | 1 | `hC` against `pts` |
| `Implementation/QFT/Proofs/Lowering/PlanSemantics.lean` | 4 | `hInterp` from the setup |
| `Implementation/QFT/Proofs/Lowering/Readiness.lean` | 9 | same |
| `Implementation/QFT/Lowering/PlanBuilders.lean` | 0 direct | `standardQFTLoweringPlan` gains `pts hpts` and forwards them to `standardPhaseProdUsingPlan` |
| `Implementation/Shor/Proofs/Lowering.lean` | 1 | `lowerGate_correctness`'s `hC` |
| `Implementation/Shor/Proofs/Correctness.lean` | 1 | `probability_of_success_lowerGate_eq`'s `hC`; passes `lowering.good` alongside `lowering.consumes` |
| `Implementation/GateCount/Definitions.lean` | 2 | `PhaseProductProgramOK k hk pts hpts ops` |
| `Implementation/GateCount/PhaseProduct/Lemmas.lean` | 31 | plan-builder instantiations inside cost proofs gain `pts`; no bound depends on the point values |
| `Implementation/GateCount/Shor_GateCount.lean` | 6 | `exists_phaseProductProgramOK` picks the canonical points; unchanged in content |
| `Implementation/Reference/StandardLoweringSetup.lean` | 4 | supplies `pts := genInterpolationPoints k`, `good := genInterpolationPoints_good k` |
| `Implementation/PhaseProduct/Compiler/Coefficients.lean` | 12 | definitions of the canonical points; unchanged |
| `Emit/Reflect/Verify.lean`, `Emit/Reflect/Targets.lean` | 1 + 3 | read `setup.pts` |
| `Emit/Table/Source.lean`, `Emit/Main.lean` | 5 | `TableSource` retired |
| `Emit/Tests.lean` | 6 | `coeff` fields and real terms read the setup's points |

The `Shor/Proofs/Readiness/*.lean` call sites gained `lowering.good`.

**S1.1** `ShorLoweringSetup` gained `pts`, `hpts`, `good`; `consumes` is
stated against `pts`.

**S1.2–S1.3** `standardSignedPhaseLoweringPlan`,
`standardCSignedPhaseLoweringPlan`, `standardPhaseProdUsingPlan`, the
`StandardPhaseLoweringPlan` abbreviation and `standardQFTLoweringPlan` take
`(pts : List Point) (hpts : pts.length = q k)`. This is what makes the
lowering build a different circuit for different points.

**S1.4** Every proof file on the chain takes
`{pts} {hpts} (hInterp : GoodToomCookPoints k pts hpts) (hC : … ops pts)`
instead of pinning `genInterpolationPoints k`; the proofs themselves were
already generic (`evalL_lowerGateRec_correct` is stated over arbitrary `pts`).

**S1.5** `PhaseProductProgramOK` takes `pts hpts`; cost lemmas gain `pts`
arguments where they build a plan; the asymptotic theorems still choose the
canonical points.

**S1.6** `standardLoweringSetup` supplies the canonical points.
`Emit/Reflect/Verify.lean`'s `coeffDispatch` (and
`phaseProductAgrees`/`cPhaseProductAgrees`/`qftAgrees`) take `pts hpts`,
callers pass `setup.pts`/`setup.hpts`. `Emit/Reflect/Targets.lean` quotes
`setup.pts` as a literal (`setupPtsExprs`, length by `decide`) instead of
pinning `genInterpolationPoints k` in the three `.eq_1` applications.
`Emit/Table/Source.lean`: `TableInstance` shrinks to `(ops, points, hlen)`,
built by `ShorLoweringSetup.tableInstance`; `TableSource`, `checkTable`,
`progConsumesPtsCheck`, `--table` and the `.generate` value-table path are
deleted. `Emit/Proofs/` and `lean_lib EmitProofs` were archived (P5) before
S1, so there were no R6 statements to rewrite.

**Exit (met).** `lake build` (3305 jobs) and `lake build EmitTests
forshor_emit` (6609 jobs) green, no `sorry`. `#print axioms` on the three
headline theorems is `[propext, Classical.choice, Quot.sound]`, unchanged.
`lake exe forshor_emit template 2` prints a byte-identical `Doc` (68 985
bytes, sha1 `25081f41…`). `bundle`/`schedule`/`coeff_poly`/`width`/
`qft_plan`/`shor_plan` differ in exactly one leaf, `provenance.table`;
`pp`/`cpp`/`qft`/`phases`/`shor` are byte-identical. The `R2_7_*_CustomTable`
tests pass unchanged. The five `scripts/check_*_layers.sh` stay green.

## 6. Stage S2.0 — `Framework/ToomCookTable.lean`: the rules, implementation-free (done)

One new file, imports Mathlib only, containing exactly the definitions needed
to state `ShorLoweringSetup`, and the record. Definitions keep their current
namespaces (the file opens each in turn), so every fully-qualified name is
unchanged and no use site outside the import lines changes.

**S2.0.1 Contents**, in dependency order:

| group | declarations (namespace) | moved from |
|---|---|---|
| registers and states | `Register`, `State` (root); `Register.zero`, `negate`, `shiftL`, `shiftR?`, `addScaled`; `State.start_state`, `setReg`, `negateReg`, `shiftLReg`, `shiftRReg?`, `addScaledReg` | `Math/Table_Generation/Core/Registers.lean` |
| operation language | `Operations.Point`, `Operations.valid_ops` | `Core/Registers.lean` |
| programs (C4) | `Prog`, `applyOp?`, `run?` (root) | `Core/Language.lean` |
| point rows and consumption (C3) | `expectedRow`, `regEqExpected`, `MatchesAtState`, `matchesAt_pointRow_state`, `ProgConsumesPts` (root); `SafeProg`, `ProgConsumesPtsSafe` (root) | `Core/Language.lean`, `Core/Coverage.lean` |
| interpolation (C1, C2) | `ToomCookMath.listToFin`, `ToomCookMath.interpMatrix`, `ToomCookMath.GoodInterpolationPoints` (generic in the point type); `Shor.q`, `Shor.interpEntry`, `Shor.GoodToomCookPoints` | `Math/ToomCook.lean` (≈ lines 43–56), `Compiler/Coefficients.lean` |
| the submission | `Shor.ShorLoweringSetup`, `abbrev Shor.ShorSubmission := ShorLoweringSetup`, with §3's table of C1–C4 as the module docstring | `Implementation/Shor/Spec/Setup.lean` |

Checked while planning: `matchesAt_pointRow_state` needs only `expectedRow`
and `regEqExpected` (not `expectedRow2`/`pointAnchor`/`finLast`), and
`GoodToomCookPoints` needs only `q`, `interpEntry` and the three generic
`ToomCookMath` definitions — not `Coefficients.lean`'s compiler imports
(`Compiler/Layout`). None of the moved definitions uses a lemma, so the file
is definitions only.

**S2.0.2 What stays in `Implementation/`.** Every lemma in those files
(`shiftR?_shiftL`, `ops_inv_involutive`, `apply_Op_inverse`, the coverage and
block-decomposition theorems, …); `Operations.inv`; `OpOK`/`WellFormed`, the
`SHL`/`ADD` shorthands, `demoProg`/`r0`/`r1`, `PhaseProductCoverage(M)`,
`expectedRow2`, `pointAnchor`; the rest of `ToomCook.lean` (`ToomCookMath.Point`,
`pointRow`, the invertibility and interpolation proofs); `Shor.interpMatrix`
and the rest of `Coefficients.lean` (`genInterpolationPoints`, Cramer
coefficients, `toMathPoint`); the table generator; `ShorApproxSetup` and the
other records in `Setup.lean`. Each of these files replaces its moved
definitions with an import of `Framework.ToomCookTable`.

**S2.0.3 Mechanics.** Move bottom-up (`Registers` → `Language` → `Coverage`
→ `ToomCook` → `Coefficients` → `Setup`), building after each. Watch for:
`deriving` clauses and `@[simp]`/`@[reducible]` attributes (carry them over
verbatim, or equation lemmas and `simp` sets change); `open` statements the
remaining lemmas relied on implicitly; and the two `interpMatrix`s
(`ToomCookMath.interpMatrix`, generic, moves; `Shor.interpMatrix`, compiler,
stays).

**S2.0.4 Exit** (met). `lake build` (3306 jobs) and `lake build EmitTests
forshor_emit` (6611 jobs) green, no `sorry`; axioms on the three headline
theorems unchanged; `template 2` byte-identical; the five layer scripts
green; `Framework/ToomCookTable.lean` imports `Mathlib.Data.Int.Basic`,
`Mathlib.Data.Fin.Basic`, `Mathlib.Algebra.EuclideanDomain.Basic`,
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` and `Mathlib.Tactic`, and
nothing else. No call site changed: every moved definition kept its
fully-qualified name, so the six source files gained an import line and lost
the definitions, and nothing else in the tree moved.

Two notes. `MatchesAt`, `matchesAt_pointRow` and `MatchesAtState.ofRegister`
stayed in `Core/Language.lean` even though `MatchesAtState` moved — only the
state-aware matcher is C3 vocabulary. And the new file is reached by `lake
build` explicitly: `FastMultiplication.lean` imports it and the two
`Submission/` files, rather than relying on the transitive path through
`Core/Registers.lean`. (That matters — see S2.2 on what happened to the one
`Reference/` file nothing imported.)

## 7. Stage S2 — decidability and the certificate (done)

**S2.1 `Submission/Decide.lean`.** Move `Emit/Table/Decide.lean` here (it
already has the `consumes` and `safe-add` instances) and add the C2 instance.
Today it imports `Emit/Table/Source.lean` (and through it the compiler, plan
builders and standard setup), but its code only uses `Prog`, `run?`,
`applyOp?`, `SafeProg`, `ProgConsumesPts(Safe)`, `matchesAt_pointRow_state`
and `State.start_state` — all moved by S2.0 — so after the move it imports
only `Framework/ToomCookTable` (and Mathlib). The checking side of a
submission is then implementation-free; only `Correct.lean` and the
template reach into `Implementation/`.
`GoodToomCookPoints` unfolds to `Matrix.det (ToomCookMath.interpMatrix
(interpEntry k) (listToFin pts hpts)) ≠ 0`, which is decidable outright
(`det` over `ℚ` with a `Fin (q k)` index is computable):

```lean
instance (k pts hpts) : Decidable (GoodToomCookPoints k pts hpts) :=
  inferInstanceAs (Decidable (Matrix.det _ ≠ 0))
```

*Done.* The instance is the one-liner above: `GoodToomCookPoints` and
`GoodInterpolationPoints` are plain `def`s, so `isDefEq` unfolds both and
typeclass search finds `Matrix.det`'s `DecidableEq ℚ` by itself. The move went
through unchanged — after S2.0 the file's one import is
`Framework/ToomCookTable`.

Smoke tests (in the same file, over literals, so it keeps that one import):
`standardLoweringSetup 3 _`'s data restated as literals closes all four
fields and assembles into a `ShorSubmission`; and the K3 precomputed table is
*rejected* against the canonical points (C3 fails) while being accepted
against its own point order, with C2 and C4 holding either way — C2 cannot
see the order at all, since a permutation only flips the determinant's sign.
That pair is the concrete evidence for P1: the same five points in a
different order are a different table.

**S2.2 `Submission/Correct.lean`.** The certificate: `def
submissionPrecision : ℕ := m2048` (one place to change; defined here so S3
can import it) and

```lean
theorem submission_correct (s : ShorSubmission) :
    ∀ T, ContinuedFractionSearchComplete T → ∀ inst, … :=
  referenceProgramAt_success s submissionPrecision
```

restating the already-generic theorem at the fixed `m`, so every accepted
submission gets one named certificate. This is the only `Submission/` file
besides `Score` and `Template` that must import `Implementation/Reference/`.

*Done*, with one repair on the way in. `m2048` lives in
`Reference/Reference2048Headline.lean`, which turned out to be an **orphan**:
nothing imported it, so it sat outside `lake build` and had gone stale — five
call sites passed `(qs := qs)` to `referenceProgramAt`/`headlineGateCount`,
which no longer take a `qs` (the reference program is classical data). The
fix was deleting those five named arguments, nothing else; the file is now
reached through `Submission/Correct.lean` and stays built. `#print axioms
Shor.submission_correct` is `propext`/`Classical.choice`/`Quot.sound` — the
smoke tests' `native_decide` does not leak into it.

## 8. Stage S3 — fixed-`m` scoring on the Lean side (done)

**S3.1 `Submission/Score.lean`** (imports `Correct`). *Done.*
`noncomputable def submissionSuccessBound (N) := referenceSuccessProbabilityAt
submissionPrecision N`, plus `submissionSuccessBound_bounds`/`_nonneg`/`_le_one`.

On "state and prove that it does not depend on the setup": there is no
non-vacuous theorem to write. The definition takes a modulus and nothing
else, so a literal independence statement
(`∀ s₁ s₂, submissionSuccessBound N = submissionSuccessBound N`) is `rfl` on
a goal that never mentions `s₁` or `s₂` — it reads as a theorem but asserts
nothing. What is citable instead is `submissionSuccessBound_le_success`:
`submission_correct` restated with the bound named, so that where `s` occurs
is visible in the statement — only on the right. That is the form a
leaderboard should quote.

**S3.2 Computable trial count.** `headlineTrialCount` is `Nat.find`, which
the submissions repo cannot evaluate. Provide

```lean
def submissionTrialCount (N : ℕ) : ℕ := ⌈ 5 / pLower N ⌉₊
```

with `pLower N : ℚ` a rational lower bound on `submissionSuccessBound N`
(for 2048-bit `N` the existing `headlineP = 0.99 · κ / 2047^4` and
`kappa_ge_one_div_25` give one immediately), and

```lean
theorem submissionTrialCount_correct (N) (hN : Is2048Bit N) :
    (99/100 : ℝ) ≤ 1 - (1 - submissionSuccessBound N) ^ submissionTrialCount N
```

via `(1-p)^t ≤ exp(-p t) ≤ 1/100` when `p t ≥ ln 100 < 5`. This number is the
same for every submission; it is published once, not recomputed per PR.

*Done*, as planned and with no slack worth tightening.
`pLower _N : ℚ := 99 / (2500 * 2047 ^ 4)` composes `headline_success_bound`
with `kappa_ge_one_div_25`; the chain is `1 - p ≤ 1 - c ≤ exp (-c)`, so
`(1-p)^t ≤ exp (-(c·t)) ≤ exp (-5) ≤ 1/100`, the one analytic input being
`100 ≤ e⁵` (`hundred_le_exp_five`, from `Real.exp_one_gt_d9`). `pLower`
takes an `N` it does not use: `log₂ N = 2047` across the whole 2048-bit
range, so the bound really is constant there, and the argument is kept so a
sharper `N`-dependent bound can replace it without touching call sites.

Both are computable: `#eval submissionTrialCount N` gives
`2 216 900 437 333 460`. That is large because the baseline `κ / (log₂ N)⁴`
being amplified is weak — a property of the correctness bound this repository
proves, not of any table.

One thing found on the way: `Is2048Bit` is defined **twice**, as
`Shor.Is2048Bit` (`Framework/Contract.lean`, used by
`ShorImplementation.trialCount_correct`) and `Reference.Is2048Bit`
(`Reference2048Headline.lean`, used by `headline_success_bound`). They are
the same proposition definitionally, so nothing breaks and no transport is
needed; `reference_is2048Bit_eq` in `Score.lean` records that by `rfl`
rather than leaving a reader of the scoring API to rediscover it. Collapsing
the two is a tidy-up for S6, not a blocker.

**S3.3 `Framework/Submission.lean` → `Framework/Contract.lean`.** *Done.*
Rename (the
name now collides conceptually with `Submission/` and with
`ShorSubmission`), fix its importers, and rewrite the module and
`ShorImplementation` docstrings: it is the framework's semantic contract,
instantiated for every accepted submission by `referenceShorImplementation
s`; the leaderboard score is `submissionTrialCount N × (external Qualtran
count)`. Remove the sentence "the leaderboard score is `trialCount N *
frameworkGateCount`". Keep `frameworkGateCount` itself (the asymptotic
theorems are stated with it).

`git mv` plus eight import lines; all three docstrings (module,
`frameworkGateCount`, `ShorImplementation`) rewritten as described, and the
score sentence is gone from both places it appeared.
`Implementation/README.md`'s path reference was repointed too — the rename
broke it, so that is a consequence of this stage rather than S6 work.

## 9. Stage S4 — the surface the submissions repo builds against (done)

**S4.1 `Submission/Template.lean`.** *Done.* The one file a submitter copies
and fills:

```lean
import FastMultiplication.ShorVerification.Framework.ToomCookTable
import FastMultiplication.ShorVerification.Submission.Decide
import FastMultiplication.ShorVerification.Submission.Correct
import FastMultiplication.Emit.Reflect.Driver

namespace Submission
def k   : ℕ := 3
def pts : List Point := [.int 0, .int 1, .int (-1), .int 2, .frac 0]
def ops : Prog k := [ … ]

def setup : Shor.ShorSubmission :=
  { k := k, hk := by decide, pts := pts, hpts := by rfl
    good := by native_decide, ops := ops
    consumes := by native_decide, returns := by native_decide }

set_option maxHeartbeats 0 in
extract_ir_doc doc setup                     -- the IR Qualtran reads
example : IR.Doc.wellFormed doc = true := by native_decide
-- evaluation checks at sampled widths (S4.2)
end Submission
```

`lakefile.lean` gains `lean_lib «Submission» where roots := #[`FastMultiplication.ShorVerification.Submission.Template]`
and `lean_exe forshor_submission` whose `main` prints `(docJson Submission.doc).compress`
plus the fixed `m`, `submissionTrialCount` for the benchmark `N`, and the
provenance block. The submissions repo's CI is then exactly:

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

Built and run: `lake build Submission` green (6601 jobs), `lake exe
forshor_submission` prints 74 507 bytes of `forshor.submission/v1` — table,
IR (all eight templates), precision, benchmark trial count, provenance, and
an explicit `checks` block saying which tier established what.

Notes on the shape it actually took:

- `k` is an `abbrev`, not a `def`. `ops : Prog k` needs `Fin k` to reduce to
  `Fin 2` for the register indices to be plain numerals; a `def` leaves
  `OfNat (Fin k) 0` unsynthesizable.
- The `main` went in a separate `Submission/Main.lean` rather than at the
  bottom of `Template.lean`. P2's promise is "drop in **one** Lean file", so
  the file a submitter replaces should hold nothing but their table and the
  checks on it.
- The shipped default is the canonical `k = 2` ladder plus one inert
  `shiftL 0 0 ;; shiftR 0 0` pair — a real table, distinct from
  `standardLoweringSetup 2`, so the default build is a worked example of an
  edit rather than a copy of the reference. `k = 2` and not the sketch's
  `k = 3` to keep the `shor`-at-smallest-instance check cheap; a submitter
  raising `k` may need a larger heartbeat budget, which the template says.
- The certificate handle is a `def` (`Submission.correct`), not a `theorem`:
  `theorem` demands an explicit type, and restating
  `submission_correct`'s conclusion in full would put twenty lines of
  boilerplate in the file a submitter is supposed to find legible.

**S4.2 Evaluation checks in the template.** Generic versions of `Tests.lean`'s
`R2_7_*_CustomTable` sections (`instantiate doc "phase_product" … =
lowerSignedPhaseProdWithWorkspace …` at `n = 8, 16`; `qft` at `w = 4, 8`;
`shor` at the smallest instance) as `native_decide` examples parameterised by
`setup`, so a submitter does not write them. `Reflect/Verify.lean`'s canary
already runs unconditionally on any setup reaching `buildDoc`, and since S1.6
checks against the submitter's own points.

*Done*, and it lives in `Emit/Reflect/Verify.lean` rather than a new file:
`phaseProductAgrees`/`cPhaseProductAgrees`/`qftAgrees` were already exposed
there "so `pp`'s own CLI command can run the same check at whatever width the
caller actually asked for", which is exactly this. `checkPhaseProduct`/
`checkCPhaseProduct`/`checkQft` were split into width-taking `…At` forms with
the old `4k` versions as one-line wrappers (so `verifyDoc` and the CLI are
untouched), and `evaluationChecks`/`submissionChecks` fold them into one
`Bool` the template pins with a single `native_decide` line.

**The second width is not belt-and-braces.** Negative control: run the
template's table against a `Doc` extracted from the canonical ladder
*without* its inert pair. `n = 8` **passes** — the compiled circuits really
do coincide there — and `n = 16` fails, because the recursive case computes
`nextWidth`/`reserveNeed` from the op list and the two lists differ. `qft` at
both widths, `shor` and `shor_gate` all pass too. A single representative
width below the recursion guard would have certified two different tables'
IR as interchangeable.

**S4.3 No CLI table input.** `forshor_emit template <k>` keeps extracting the
standard setup only. This is deliberate and unchanged from R5: a table enters
through a Lean declaration, never through a parser. *Done by doing nothing*:
verified unchanged, and `template 2` is still byte-identical to the pre-S1
baseline.

**Exit** (met). `lake build` (3311), `lake build EmitTests forshor_emit`
(6611) and `lake build Submission forshor_submission` (6601) all green, no
`sorry`; axioms unchanged on the five tracked theorems; `template 2`
byte-identical; layer scripts green; and the submissions-repo CI one-liner
runs end to end.

## 10. S5 — scratched: no per-submission IR theorem (decision P5)

Considered and rejected. R6 proved `instantiate <doc> … = .ok <verified
term>` for the `k = 2` standard table only; the proofs were hand-written,
table-specific (they `rfl`-ground-truth the extracted body node by node), and
not a function of the setup, because the extractor is a `MetaM` program
rather than a Lean function. Making that per submission would need either a
proof-generating tactic replaying R6's scripts against each fresh `Doc`, or a
verified Lean-level emitter (the design D1–D3 rejected). Neither is a
reasonable bar for a PR, and a proof about one table says little about the
others, so R6 itself was archived (`emit-proofs-archive`, `2218ba6`) rather
than kept as reference-only evidence.

What stands instead:

- **Acceptance bar = route A.** The four side conditions (§3), hence
  `submission_correct`, plus S4.2's `instantiate = real` evaluation checks at
  sampled widths and one full `shor` instance. This is the same standard the
  reference table was accepted at (D7).
- The template's provenance string says `"checked by evaluation"` for every
  submission, exactly as D7 does today.

## 11. Stage S6 — documentation (done)

Two plan files were **deleted** rather than rewritten (owner's call):

- `RESTRUCTURE_PLAN.md` — the v2 Framework/Implementation split, long since
  carried out and superseded by this file's §4 layout. Its one live claim
  (`Compilation/` as a planned folder; the compiler actually landed at
  `Shor/Lowering/`) is now recorded where it was cited, in
  `REORG_COMPILATION.md`.
- `Emit/PLAN.md` — 4 312 lines, most of it the R6 engineering log for work
  that P5 scratched and that is archived on `emit-proofs-archive`.

Deleting the second one was not free: 33 `.lean` docstrings and 7 markdown
files cited it, usually as "`Emit/PLAN.md` §7" or "(R3/R4)". Leaving 40
dangling references would have been worse than keeping the file, so before
deleting, `Emit/README.md` gained a **round history** section defining
R0–R6 in a table — which is what the `R`-labels scattered through the
emitter's docstrings now mean — and every citation was rewritten to drop the
dead `§`-numbers and point there where a target is needed. Both files remain
in git history.

The rest, as planned:

- `README.md` (top level): "Status" note that the reference is no longer the
  only admissible implementation; "Repository layout" rows for
  `Framework/` (now naming `Contract.lean` and `ToomCookTable.lean`),
  `Reference/` (re-described as table ↦ circuit family), `Submission/` (new)
  and `Emit/`; a new **"Submitting a table"** section with the C1–C4 table
  and the two-command workflow; the build section lists the new targets.
- `ARCHITECTURE.md`: a new **"The submission boundary"** section — the §4
  layout as a table, and the consequence stated plainly (correctness proved
  once, generic in the table; a submission is *checked*, not proved).
- `Implementation/README.md`: the opening no longer says "this folder *is*
  the submission" — it is the construction, and a submission is a
  `ShorSubmission` in `Framework/`. The `Reference/` section is retitled
  "table ↦ circuit family" and now leads with `referenceProgramAt_success`'s
  genericity rather than with `referenceShorImplementation`.
- `PhaseProduct/Math/Table_Generation/Core/README.md`,
  `PhaseProduct/Compiler/README.md` and `PhaseProduct/Math/README.md` each
  note which of their definitions moved to `Framework/ToomCookTable.lean`
  and that the lemmas stayed. The third was not on the original list but
  documents `listToFin`/`interpMatrix`/`GoodInterpolationPoints`, which
  moved.
- `Emit/README.md`: "Using a custom table" now opens by redirecting to the
  S4 workflow and keeps the `extract_ir_doc` path below it for callers who
  want the `Doc` alone. Two claims that S2/S4 had falsified were corrected
  while there — "nothing under `ShorVerification/` was changed to support
  it" and "the only edits outside this folder are two `lakefile.lean`
  entries".
- `Submission/README.md` (new, written during S2–S4) covers the new folder.

Still open, and not documentation:

- Collapse the duplicate `Is2048Bit` (`Shor.Is2048Bit` in
  `Framework/Contract.lean` vs `Reference.Is2048Bit`) into one.
  `Score.lean`'s `reference_is2048Bit_eq` records that they agree until then.
- The top-level `PLAN.md` (the "make the reference circuit computable and
  emit it" plan) and `REORG_COMPILATION.md` are both finished-work logs of
  the same kind as the two files deleted here. They were left alone because
  no one asked for them; the same argument would retire them.

## 12. Risks

- **S2.0 attribute and `open` drift.** Moving a definition can silently drop
  a `@[simp]`/`@[reducible]` attribute or a `deriving` instance, or change
  which names an `open` brings into scope for the lemmas left behind. The
  byte-identical `template 2` and the green test suite are the check; build
  after each file.
- **`decide` vs `native_decide`.** C2 through `Matrix.det` and C3 through
  `run?` on `Fin k → Fin k → ℤ` states are far too big for kernel `decide`
  beyond `k = 2`. The acceptance bar therefore trusts the compiler
  (`Lean.ofReduceBool`) on exactly the four fields, and on nothing else in
  the correctness theorem. Say so in the template.
- **`frac` points.** The row for `frac c` is not a Vandermonde row, so the
  distinctness shortcut does not apply; C2 is checked by determinant, which
  is why it must be decidable rather than proven by lemma.
- **Duplicate `Point` types.** `Operations.Point` (compiler; moves to
  `Framework/`) and `ToomCookMath.Point` (math; stays) are bridged by
  `toMathPoint`. `GoodInterpolationPoints` is generic in the point type, so
  only `Operations.Point` is needed to state the rules.
- **Large `k`.** `(2k-1)!` determinant terms and the `Tests.lean`-scale
  heartbeat budgets for extraction grow fast; state `k ≤ 6` as the supported
  range in the template until a Gaussian-elimination checker with a
  soundness proof replaces `Matrix.det`.

## 13. Deliverable checklist

- [x] S1.1 `ShorLoweringSetup` generalised
- [x] S1.2–S1.3 plan builders take `pts`
- [x] S1.4 proof files re-hypothesised
- [x] S1.5 GateCount predicates and lemmas
- [x] S1.6 `standardLoweringSetup`, `coeffDispatch`, `Targets.lean`, `TableInstance`, tests
- [x] S1 exit: builds green, axioms unchanged, `template 2` byte-identical
- [x] S1 committed on `ir-reflection-r0` (`b4856a5`)
- [x] S2.0 `Framework/ToomCookTable.lean` (definitions + `ShorLoweringSetup` + `ShorSubmission`), old sites import it, exit checks
- [x] S2.1 `Submission/Decide.lean` incl. `Decidable (GoodToomCookPoints …)`, smoke tests
- [x] S2.2 `Submission/Correct.lean`: `submissionPrecision`, `submission_correct` (+ repaired the orphaned `Reference2048Headline.lean` it depends on)
- [x] S3.1–S3.2 `Submission/Score.lean`: success bound, computable trial count, proofs
- [x] S3.3 `Framework/Submission.lean` → `Framework/Contract.lean`, docstrings
- [x] S4.1 `Submission/Template.lean` (+ `Submission/Main.lean`), `lean_lib Submission`, `lean_exe forshor_submission`
- [x] S4.2 generic evaluation checks (`Reflect/Verify.lean`'s `submissionChecks`), with a negative control
- [x] S5 scratched (P5): acceptance bar is the evaluation tier; R6 archived
- [x] S6 docs (+ `RESTRUCTURE_PLAN.md` and `Emit/PLAN.md` deleted, their live content preserved in `Emit/README.md`'s round history)
