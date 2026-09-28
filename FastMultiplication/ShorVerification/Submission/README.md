# `Submission/`

The public surface a submissions repo builds against. A submission is a
Toom-Cook table — an arithmetic program `ops : Prog k`, the interpolation
points `pts` its `phaseProduct` checkpoints evaluate at, **and the submitter's
proofs that the pair is admissible** — and this folder is everything that
happens to one: the checking, the audit, the certificate, the score, and the
file a submitter copies.

The rules themselves are not here. They are in
[`../Framework/ToomCookTable.lean`](../Framework/ToomCookTable.lean), which
imports Mathlib and nothing else: the record `Shor.ShorSubmission` (an
`abbrev` for `Shor.ShorLoweringSetup`) and the four conditions C1–C4 it
bundles. A submissions repo can read the specification without reading the
construction that satisfies it.

| file | what it is | reaches into `Implementation/`? |
|---|---|---|
| `Decide.lean` | decision procedures for C1–C4, so `by decide +kernel` discharges a concrete table's proof fields | no — `Framework/` + Mathlib only |
| `Audit.lean` | `#assert_axioms`: fails the build unless a declaration's axioms are `propext` / `Classical.choice` / `Quot.sound` | no — `Lean` only |
| `Correct.lean` | `submissionPrecision` (the one fixed `m`) and `submission_correct`, the certificate every accepted submission gets | yes (`Reference/`) |
| `Score.lean` | the declared success bound at that `m`, and a **computable** trial count amplifying it past 99% | yes |
| **`Template.lean`** | **the file a submitter owns**: three definitions and the `ShorSubmission` record with C1–C4 proved | no — `Framework/` + `Decide.lean` |
| `Check.lean` | the acceptance check, repo-owned: the axiom audit, the IR extraction, the evaluation tier, the certificate | yes (`Emit/`) |
| `Main.lean` | `forshor_submission`: prints the table, the IR, the precision and the trial count as one JSON document | yes (`Emit/`) |

## `Decide.lean`

Four side conditions, all decidable at a concrete `k`, `ops`, `pts`:

- **C1** `pts.length = q k` — `Nat` equality; `rfl` in practice.
- **C2** `GoodToomCookPoints k pts hpts` — unfolds to `Matrix.det (…) ≠ 0`
  over `ℚ`. The determinant is computable, but it is a sum over `(2k-1)!`
  permutations — 39 916 800 of them at `k = 6` — and the kernel will not
  evaluate that. It does not have to. In the projective coordinates
  `int z ↦ (z : 1)` and `frac c ↦ (1 : c)` the interpolation matrix is
  *literally* Mathlib's `Matrix.projVandermonde`, whose determinant factors
  as `∏_{i < j} (v j * w i - v i * w j)`, so over the domain `ℚ`

      GoodToomCookPoints k pts hpts  ↔  PointsDistinct pts

  (`goodToomCookPoints_iff_distinct`) — the points are pairwise distinct *as
  projective points*: two `int`s differ, two `frac`s differ, and `int z` with
  `frac c` needs `z * c ≠ 1`, which is why `frac 0` (the point at infinity)
  is distinct from every `int` while `int 1` and `frac 1` are the same point.
  That is a quadratic scan the kernel closes instantly at every supported
  `k`, and `goodToomCookPoints_of_distinct` is the direction a submission
  uses. Because it is an equivalence, a rejection is a verdict: a table
  `PointsDistinct` refuses is inadmissible, not merely unproven.
- **C3** `ProgConsumesPtsSafe … ops pts` — `ProgConsumesPts` (term-mode,
  mirroring its own recursion on `ops`) and `SafeProg` (a Boolean scan plus
  a transport lemma). Neither had an instance anywhere in the repo before.
- **C4** `run? ops State.start_state = some State.start_state` — already
  decidable via `DecidableEq (State k)`.

Its smoke tests, stated over literals so the file keeps its one import, check
that the instances decide what they claim: the reference table at `k = 3`
passes all four and assembles into a `ShorSubmission`, and the `k = 3`
precomputed table is *rejected* against the canonical point ladder while
being accepted against its own point order — C3 is about the order, not just
the set, which is why the points are genuine submission data. Every one of
them is `decide +kernel`, never `native_decide`: they are the same lines a
submitter writes, so they are also the evidence that a submission can be
discharged by the kernel alone. `refSubmission` is therefore a worked example
of a fully kernel-checked submission at `k = 3`.

## `Audit.lean`

`#assert_axioms c` fails the build unless every axiom `c` depends on is one
of `propext`, `Classical.choice`, `Quot.sound`. It is `Lean.collectAxioms` —
the traversal behind `#print axioms` — turned into a check, and it is what
makes "kernel-checked" a checked claim instead of a documented intention.

It catches `native_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`),
`sorry` (`sorryAx`), and any `axiom` a submitter declares, naming the
offender. It does **not** catch `set_option debug.skipKernelTC true`, which
skips the kernel without adding an axiom — nothing visible in the environment
does. That is what `lean4checker` is for; see the CI rules at the end of this
file.

## `Correct.lean`

`referenceProgramAt_success` is already generic in the setup it is handed, so
there is no per-submission proof obligation. What this file adds is the
organiser's choice of precision (`submissionPrecision := m2048`, fixed so the
declared bound and the trial count are per-`N` constants a submitter cannot
tune) and one named certificate, `submission_correct`, for the submissions
repo to point at.

## `Score.lean`

Both factors of the leaderboard score are settled here, and
neither is something a submitter can influence.

`submissionSuccessBound N` is `referenceSuccessProbabilityAt` at the fixed
precision. Its definition takes a modulus and nothing else, so every accepted
table declares the same bound at the same `N`;
`submissionSuccessBound_le_success` is `submission_correct` restated with
that name, and `s` occurs only on its right-hand side.

`submissionTrialCount N` is a computable `ℕ` — `Reference.headlineTrialCount`
is a `Nat.find` witness, which a submissions repo can cite but not evaluate.
It is `⌈5 / pLower N⌉₊`, where `pLower N : ℚ` is a rational lower bound on
the declared bound for 2048-bit moduli, composed from
`headline_success_bound` (at least 99% of the `κ / 2047⁴` baseline) and
`kappa_ge_one_div_25`. `submissionTrialCount_correct` proves it suffices,
by `(1 - p)^t ≤ exp (-p·t) ≤ exp (-5) ≤ 1/100`, the one analytic input being
`100 ≤ e⁵`.

At 2048 bits that is `2 216 900 437 333 460` runs — large because the
single-run baseline `κ / (log₂ N)⁴` it amplifies is itself weak, which is a
property of the correctness bound this repository proves and not of any
particular table. It is published once, not recomputed per pull request.

The other factor, the single-run gate count, is measured by Qualtran on the
IR `Emit/` extracts, not computed in Lean.
`ShorOrderFindingProgram.frameworkGateCount` survives as what the asymptotic
theorems are stated with; it is no longer the scored number.

## `Template.lean`, `Check.lean` and `Main.lean`

The submitter-facing set, and the two `lakefile.lean` targets that go with
them:

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

That is the acceptance check. `lean_lib Submission` is rooted at
`Check.lean`, so **building it is the check**. `forshor_submission` is a
printer — it re-decides nothing, which is why the two commands are joined
with `&&` rather than the executable guarding itself.

**`Template.lean` is the only file a submitter owns.** It holds three
definitions (`k`, `pts`, `ops`), the C1 lemma, and the `ShorSubmission`
record with all four side conditions proved:

```lean
hk       := by decide
hpts     := hpts                                                    -- C1
good     := goodToomCookPoints_of_distinct hpts (by decide +kernel) -- C2
consumes := by decide +kernel                                       -- C3
returns  := by decide +kernel                                       -- C4
```

`decide +kernel`, not `native_decide`. `native_decide` closes a goal by
running the compiled evaluator and asserting the answer through
`Lean.ofReduceBool`, an axiom; `decide +kernel` makes Lean's kernel reduce
the decision procedure itself. This is not a claim that the proofs are hard —
for most tables each field is one line and the kernel does the work. What it
buys is that the work really was the kernel's, and `Check.lean`'s
`#assert_axioms Submission.setup` is what holds a submission to it.

It imports `Framework/ToomCookTable.lean` and `Decide.lean` and nothing else,
so a submitter never builds `Implementation/` to iterate on a table.

`Template.lean` ships with a working table: `k = 2` at the canonical points
`0, -1, 1`, reaching each row by negating register 1 rather than subtracting.
Nine operations where the reference's is seven, and not a permutation of it —
a worked example of an edit rather than a copy of the reference.

`Check.lean` is repo-owned and is where everything that used to sit below the
edit line in `Template.lean` now lives: `#assert_axioms Submission.setup`,
`extract_ir_doc doc setup`, the two `native_decide` evaluation examples, and
`correct`.

### The two tiers, and which is which

**Kernel-checked, and audited.** C1–C4 on the table, proved by the submitter
and reduced by Lean's kernel, with `#assert_axioms` confirming that no other
axiom crept in. Passing them is not evidence that the submission is
admissible, it *is* admissibility — `Shor.submission_correct` is generic in
the table, so it applies with no further work and no per-submission proof.

**Checked by evaluation.** `Shor.Reflect.submissionChecks` compares the
extracted IR against the real compiled circuit at `n = 8, 16` (phase
products), `w = 4, 8` (QFT) and the smallest reference Shor instance. The IR
is *not* proved equal to the circuit at every width; that project (R6)
concerns the reference table only and was archived. Sampling two widths
rather than one is not belt-and-braces: at `k = 2`, `n = 8` is the base case
and `n = 16` the recursive one, and two different tables have now been
observed to agree at `n = 8` and disagree at `n = 16`. One width below the
guard would have called them interchangeable.

These two lines stay on `native_decide` deliberately. They are repo-owned
`example`s about the *extractor*, not fields of `setup`, so they do not enter
the audit; making the evaluation tier kernel-checked is a separate project.

### A known limitation of the evaluation tier

A table whose `phaseProduct` checkpoints do not all sit on register 0 is
admissible — C1–C4 all pass — but its extracted `phase_product` and
`cphase_product` IR disagrees with the real compiled term at `n = 16`. This
is a limitation of the IR extractor, not of the rules, and it is why the
shipped table keeps every checkpoint on register 0.

It is also why the shipped table uses no `frac` points: at `k = 2` the row of
`frac 0` is `[0, 1]`, which is register 1's start value and cannot be built
in register 0, so exercising `frac 0` at `k = 2` requires a checkpoint on
register 1. `frac` points are fine as far as C1–C4 are concerned —
`Decide.lean`'s smoke tests cover them, and the `k = 3` precomputed table
consumes a `frac 0` — but a submission that uses one must currently place its
checkpoints so that the IR check still passes.

`forshor_emit template <k>` still extracts the standard table and only the
standard table. A table enters through a Lean declaration, never through a
parser: its side conditions need the kernel.

## CI for a submissions repo

This repository has no CI of its own. A submissions repo enforcing the
acceptance check should run, per pull request:

1. **The diff rule.** A PR may change only its copy of
   `Submission/Template.lean`. Everything else — `Decide.lean`,
   `Audit.lean`, `Check.lean`, `Correct.lean`, `Score.lean`, `Main.lean`,
   `Framework/`, `Implementation/`, `lakefile.lean` — is repo-owned. A PR
   touching any of it changes the rules rather than answering them.

2. **The build and the print**, as now:

   ```bash
   lake build Submission && lake exe forshor_submission > ir.json
   ```

   This is where the four side conditions are checked, where
   `#assert_axioms` runs, and where the IR is pinned against the real
   circuit. `ir.json` is what the resource estimator reads.

3. **`lean4checker` on the `.olean`s step 2 built.** `#assert_axioms` reads
   the axioms a declaration depends on; it does not see
   `set_option debug.skipKernelTC true`, which skips the kernel without
   adding an axiom, and nothing else visible in the environment does either.
   Replaying the built environment through the kernel does. A submission is
   not accepted until this passes.
