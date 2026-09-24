# `Submission/`

The public surface a submissions repo builds against (`SUBMISSION_PLAN.md`
§4). A submission is a Toom-Cook table — an arithmetic program `ops : Prog k`
plus the interpolation points `pts` its `phaseProduct` checkpoints evaluate
at — and this folder is everything that happens to one: the checking, the
certificate, the score, and the file a submitter copies.

The rules themselves are not here. They are in
[`../Framework/ToomCookTable.lean`](../Framework/ToomCookTable.lean), which
imports Mathlib and nothing else: the record `Shor.ShorSubmission` (an
`abbrev` for `Shor.ShorLoweringSetup`) and the four conditions C1–C4 it
bundles. A submissions repo can read the specification without reading the
construction that satisfies it.

| file | stage | what it is | reaches into `Implementation/`? |
|---|---|---|---|
| `Decide.lean` | S2.1 | decision procedures for C1–C4, so `by native_decide` discharges a concrete table's proof fields | no — `Framework/` + Mathlib only |
| `Correct.lean` | S2.2 | `submissionPrecision` (the one fixed `m`, decision P3) and `submission_correct`, the certificate every accepted submission gets | yes (`Reference/`) |
| `Score.lean` | S3 | the declared success bound at that `m`, and a **computable** trial count amplifying it past 99% | yes |
| `Template.lean` | S4 | the file a submitter copies: three definitions to edit, every proof field pre-filled with `by native_decide` | yes (`Emit/`) |
| `Main.lean` | S4 | `forshor_submission`: prints the table, the IR, the precision and the trial count as one JSON document | yes (`Emit/`) |

## `Decide.lean`

Four side conditions, all decidable at a concrete `k`, `ops`, `pts`:

- **C1** `pts.length = q k` — `Nat` equality; `rfl` in practice.
- **C2** `GoodToomCookPoints k pts hpts` — unfolds to `Matrix.det (…) ≠ 0`
  over `ℚ`, computable outright, so the instance is one `inferInstanceAs`.
  The determinant is a sum over `(2k-1)!` permutations: instant through
  `k = 5`, slow but feasible at `k = 6`.
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
the set, which is why the points are genuine submission data.

## `Correct.lean`

`referenceProgramAt_success` is already generic in the setup it is handed, so
there is no per-submission proof obligation. What this file adds is the
organiser's choice of precision (`submissionPrecision := m2048`, fixed so the
declared bound and the trial count are per-`N` constants a submitter cannot
tune) and one named certificate, `submission_correct`, for the submissions
repo to point at.

## `Score.lean`

Both factors of the leaderboard score (decision P4) are settled here, and
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

## `Template.lean` and `Main.lean`

The submitter-facing pair, and the two `lakefile.lean` targets that go with
them:

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

That is the whole acceptance check. `lean_lib Submission` is rooted at
`Template.lean`, so **building it is the check**: the four side conditions go
through the kernel, and `native_decide` pins `IR.Doc.wellFormed doc` and
`Shor.Reflect.submissionChecks setup doc`. `forshor_submission` is a printer
— it re-decides nothing, which is why the two commands are joined with `&&`
rather than the executable guarding itself.

`Template.lean` has exactly three definitions to edit (`k`, `pts`, `ops`),
marked as such. Everything below them, including every `by native_decide`,
stays as it is. It ships with a working table: the canonical `k = 2` ladder
plus a semantically inert `shiftL 0 0 ;; shiftR 0 0` pair, so the default
build is green and is a real edit rather than a copy of the reference.

### The two tiers, and which is which

**Kernel-checked.** C1–C4 on the table. Passing them is not evidence that the
submission is admissible, it *is* admissibility — `Shor.submission_correct`
is generic in the table, so it applies with no further work and no
per-submission proof.

**Checked by evaluation.** `Shor.Reflect.submissionChecks` compares the
extracted IR against the real compiled circuit at `n = 8, 16` (phase
products), `w = 4, 8` (QFT) and the smallest reference Shor instance. The IR
is *not* proved equal to the circuit at every width; that project (R6)
concerns the reference table only and was archived (decision P5). Sampling
two widths rather than one is not belt-and-braces: at `k = 2`, `n = 8` is the
base case and `n = 16` the recursive one, and a `Doc` extracted from the
canonical ladder passes at `n = 8` against the template's table — the extra
ops really are inert there — while failing at `n = 16`. One width below the
guard would have called two different tables' IR interchangeable.

`forshor_emit template <k>` still extracts the standard table and only the
standard table (S4.3). A table enters through a Lean declaration, never
through a parser: its side conditions need the kernel.
