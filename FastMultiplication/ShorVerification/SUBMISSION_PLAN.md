# PLAN: a submission is a table and a set of interpolation points

Status: revised 2026-09-23. Owner decisions in §1. **S1 is done** (in the
working tree on `ir-reflection-r0`, not yet committed); next is **S2.0**, the
move of the table definitions into `Framework/` (§6). The S1 site inventory
(§5) was taken from the tree at commit `c045219`.

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

## 6. Stage S2.0 — `Framework/ToomCookTable.lean`: the rules, implementation-free

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

**S2.0.4 Exit.** Same as S1's: `lake build` and `lake build EmitTests
forshor_emit` green, axioms unchanged, `template 2` byte-identical, layer
scripts green, and `Framework/ToomCookTable.lean` has no import outside
Mathlib.

## 7. Stage S2 — decidability and the certificate

**S2.1 `Submission/Decide.lean`.** Move `Emit/Table/Decide.lean` here (it
already has the `consumes` and `safe-add` instances; its proofs may keep
importing the `Table_Generation` lemmas), and add the C2 instance.
`GoodToomCookPoints` unfolds to `Matrix.det (ToomCookMath.interpMatrix
(interpEntry k) (listToFin pts hpts)) ≠ 0`, which is decidable outright
(`det` over `ℚ` with a `Fin (q k)` index is computable):

```lean
instance (k pts hpts) : Decidable (GoodToomCookPoints k pts hpts) :=
  inferInstanceAs (Decidable (Matrix.det _ ≠ 0))
```

Smoke tests: `native_decide` closes all four fields for
`standardLoweringSetup 3 _`'s data restated as literals, and *rejects* the K3
precomputed table paired with the canonical points (C3 fails) while
accepting it paired with its own point order.

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
besides `Template` that must import `Implementation/Reference/`.

## 8. Stage S3 — fixed-`m` scoring on the Lean side

**S3.1 `Submission/Score.lean`** (imports `Correct`).
`noncomputable def submissionSuccessBound (N) := referenceSuccessProbabilityAt
submissionPrecision N`. State and prove that it does not depend on the setup
(it is literally a function of `m, N` only, so this is `rfl`-level, but say
it in a theorem so the leaderboard can cite it).

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

**S3.3 `Framework/Submission.lean` → `Framework/Contract.lean`.** Rename (the
name now collides conceptually with `Submission/` and with
`ShorSubmission`), fix its importers, and rewrite the module and
`ShorImplementation` docstrings: it is the framework's semantic contract,
instantiated for every accepted submission by `referenceShorImplementation
s`; the leaderboard score is `submissionTrialCount N × (external Qualtran
count)`. Remove the sentence "the leaderboard score is `trialCount N *
frameworkGateCount`". Keep `frameworkGateCount` itself (the asymptotic
theorems are stated with it).

## 9. Stage S4 — the surface the submissions repo builds against

**S4.1 `Submission/Template.lean`.** The one file a submitter copies and
fills:

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

**S4.2 Evaluation checks in the template.** Generic versions of `Tests.lean`'s
`R2_7_*_CustomTable` sections (`instantiate doc "phase_product" … =
lowerSignedPhaseProdWithWorkspace …` at `n = 8, 16`; `qft` at `w = 4, 8`;
`shor` at the smallest instance) as `native_decide` examples parameterised by
`setup`, so a submitter does not write them. `Reflect/Verify.lean`'s canary
already runs unconditionally on any setup reaching `buildDoc`, and since S1.6
checks against the submitter's own points.

**S4.3 No CLI table input.** `forshor_emit template <k>` keeps extracting the
standard setup only. This is deliberate and unchanged from R5: a table enters
through a Lean declaration, never through a parser.

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

## 11. Stage S6 — documentation

- `README.md` (top level): "Status" and "Repository layout" rows for
  `Framework/ToomCookTable.lean`, `Framework/Contract.lean`, `Reference/`,
  `Submission/`, `Emit/`; add a "Submitting a table" section pointing at
  `Submission/Template.lean`.
- `ARCHITECTURE.md`: a paragraph on the §4 layout — the rules in
  `Framework/ToomCookTable.lean`, the certificate in `Submission/Correct.lean`.
- `Implementation/README.md`: the opening paragraph and the `Reference/`
  section no longer say "this folder is the submission"; the submission is a
  `ShorLoweringSetup` (defined in `Framework/`), `Reference/` is the
  construction that consumes one. `PhaseProduct/Math/Table_Generation/Core/README.md`
  and `PhaseProduct/Compiler/README.md` note which definitions now live in
  `Framework/ToomCookTable.lean`.
- `RESTRUCTURE_PLAN.md` Phase 5: rewrite in terms of P1–P8.
- `Emit/README.md`: point "Using a custom table" at the S4 workflow, and drop
  its `good`-has-no-`Decidable`-instance caveat once S2.1 lands one.
- `Emit/PLAN.md`: add a §13 pointer to this file; mark the ground rule "no
  edits under `ShorVerification/`" as lifted; mark §12 (R6) archived, with
  the branch and commit.

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
- [ ] S1 committed on `ir-reflection-r0`
- [ ] S2.0 `Framework/ToomCookTable.lean` (definitions + `ShorLoweringSetup` + `ShorSubmission`), old sites import it, exit checks
- [ ] S2.1 `Submission/Decide.lean` incl. `Decidable (GoodToomCookPoints …)`, smoke tests
- [ ] S2.2 `Submission/Correct.lean`: `submissionPrecision`, `submission_correct`
- [ ] S3.1–S3.2 `Submission/Score.lean`: success bound, computable trial count, proofs
- [ ] S3.3 `Framework/Submission.lean` → `Framework/Contract.lean`, docstrings
- [ ] S4.1 `Submission/Template.lean`, `lean_lib Submission`, `lean_exe forshor_submission`
- [ ] S4.2 generic evaluation checks in the template
- [x] S5 scratched (P5): acceptance bar is the evaluation tier; R6 archived
- [ ] S6 docs
