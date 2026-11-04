# `Submission/`

The public surface a submissions repo builds against. A submission is a
Toom-Cook table — an arithmetic program `ops : Prog k`, the interpolation
points `pts` its `phaseProduct` checkpoints evaluate at, **and the submitter's
proofs that the pair is admissible** — and this folder is everything that
happens to one: the checking, the audit, the certificate, the score, and the
file a submitter copies.

There are two kinds of submission. A **table** submission is one table, used
at every width; a **policy** submission is a width-indexed list of them, a
wide table at the top of the recursion and narrower ones below it. They share
everything: the same four side conditions per table, the same audit, the same
certificate, and in fact the same theorem — a table submission *is* the
one-band policy at threshold `0`, and [`Policy submissions`](#policy-submissions)
below says what the second kind adds.

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
| **`PolicyTemplate.lean`** | **the file a policy submitter owns**: the per-band definitions and the `ShorPolicySubmission` record | no — `Framework/` + `Decide.lean` |
| `PolicyDecide.lean` | `bandShrinks`, an **advisory** performance check on a policy's bands; not an admissibility condition | yes (`Implementation/`) |
| `PolicyCheck.lean` | the kernel-checked half of a policy's acceptance check, repo-owned: the axiom audit, the IR extraction (one body per distinct table), its well-formedness, the certificate. Nothing in it names the shipped bands, so it builds for any admissible policy | yes (`Emit/`) |
| `PolicyTests.lean` | worked examples on the shipped policy template (`choose` at particular widths, the advisory shrink check firing at threshold `12`); built by `lean_lib PolicyTests`, never by the acceptance check | no |
| `PolicyMain.lean` | `forshor_policy_submission`: extracts the IR, runs the evaluation tier natively, then prints the bands, the IR, the precision and the trial count; prints nothing and exits `1` if the tier fails. Flags: `--exact-widths`, `--balanced`, `--probe-exact`, `--width-table` (see the file) | yes (`Emit/`) |

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

It catches `native_decide` (the auxiliary axiom recording the compiled evaluator's answer),
`sorry` (`sorryAx`), and any `axiom` a submitter declares, naming the
offender. It does **not** catch `set_option debug.skipKernelTC true`, which
skips the kernel without adding an axiom — nothing visible in the environment
does. The lexical gate rejects `set_option debug` in a template for that
reason.

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
`headline_success_bound` (at least 99% of the `κ / log 2048` baseline),
`kappa_ge_one_div_ten` and `log 2048 ≤ 7.63`. `submissionTrialCount_correct` proves it suffices,
by `(1 - p)^t ≤ exp (-p·t) ≤ exp (-5) ≤ 1/100`, the one analytic input being
`100 ≤ e⁵`.

At 2048 bits that is `386` runs: the single-run baseline
`κ / log(log₂ N + 1)` it amplifies is about `1.3 · 10⁻²` there, from the
Mertens-type totient bound `φ(r)/r ≥ 1/(4 · log(log₂ N + 1))`. That is a
property of the correctness bound this repository proves and not of any
particular table. It is published once, not recomputed per pull request.

The other factor, the single-run gate count, is measured by Qualtran on the
IR `Emit/` extracts, not computed in Lean.
`ShorOrderFindingProgram.frameworkGateCount` is what the asymptotic
theorems are stated with; it is not the scored number.

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
running the compiled evaluator and asserting the answer through an
axiom; `decide +kernel` makes Lean's kernel reduce
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

`Check.lean` is repo-owned and holds the acceptance check itself:
`#assert_axioms _root_.Submission.setup`,
`extract_ir_doc doc setup`, the two `native_decide` evaluation examples, and
`correct`.

### The two tiers, and which is which

**Kernel-checked, and audited.** C1–C4 on the table, proved by the submitter
and reduced by Lean's kernel, with `#assert_axioms` confirming that no other
axiom crept in. Passing them is not evidence that the submission is
admissible, it *is* admissibility — `Shor.submission_correct` is generic in
the table, so it applies with no further work and no per-submission proof.

**Checked by evaluation.** `Shor.Reflect.submissionChecks` compares the
extracted IR against the real compiled circuit at ladders of widths derived
from the submitted table itself: the phase products at `ppWidthLadder
setup.ops`, in each of two reserve regimes; the hand-stated leaf templates at
three unequal `(xw, zw)` pairs; the QFT at `qftWidthLadder setup.ops`; and
`shor_gate`/`shor` at two reference Shor instances. The IR is *not* proved
equal to the circuit at every width; agreement at sampled widths is
evaluation, not a theorem.

The ladders are not a fixed list, and that is the point. `ppWidthLadder`
returns the largest base-case width together with the smallest widths
reaching one, two and three levels of recursion, computed from the table's
own `nextWidth` chain — for the shipped `k = 2` table, `[13, 14, 15, 17]`.
Sampling a single width per template is what let a real extractor bug sit
unseen: the top chunk receives all the slack in the reserve split, so a fault
in its child capacity shows up only at a *grandchild*, three levels down, and
only when a `phaseProduct` checkpoint sits on register `k - 1` with slack
available. Hence three levels, and hence two reserve regimes rather than one.

A submitter should know what this costs. The ladder is derived from the
table, and a table that recurses later is checked at larger widths: the
shipped `k = 2` table's acceptance build is about a minute, while a `k = 3`
table reaches `n = 35` and runs for roughly **35 minutes**; `k = 4` reaches
`n = 87` and is not a build anyone will wait for. Capping the ladder depth is
an open decision, not a bug.

These two lines stay on `native_decide` deliberately. They are repo-owned
`example`s about the *extractor*, not fields of `setup`, so they do not enter
the audit; making the evaluation tier kernel-checked is a separate project.

### Where a checkpoint sits, and where `frac` points can go

Nowhere in particular: any register, any points. The recursion's reserve
split gives the *top* chunk (register `k - 1`) every qubit left over after
each child's requirement is paid, and the emitted IR passes the recursive
call that topped-up figure, so a checkpoint on that register is handled like
any other. Both of `Emit/Tests.lean`'s `TopChunkReserve` tables — one
with its checkpoints on register 1, one at the points `0, -1, frac 0` —
exercise this.

At `k = 2` the row of `frac 0` (the point at infinity) is `[0, 1]`, which is
register 1's start value and cannot be built in register 0, so exercising
`frac 0` at `k = 2` *requires* a checkpoint on register 1; that is an
ordinary table. `frac` points are fine as far as C1–C4 are concerned —
`Decide.lean`'s smoke tests cover them, and the `k = 3` precomputed table
consumes a `frac 0`.

`forshor_emit template <k>` still extracts the standard table and only the
standard table. A table enters through a Lean declaration, never through a
parser: its side conditions need the kernel.

## Policy submissions

The score is a gate count at one fixed size, not an asymptotic exponent, and
at a fixed size the optimum is generally a cascade rather than a single
radix: a wide table while the operands are wide, narrower ones as the
recursion descends, the schoolbook leaf at the bottom. A **policy** is that
cascade, and it is the second kind of submission.

```bash
lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
```

`lean_lib PolicySubmission` is rooted at `PolicyCheck.lean`, so **building
it is the kernel-checked half of the check**: the per-band side conditions
and the axiom audit. The IR is extracted inside `forshor_policy_submission`,
at run time, and its well-formedness and the evaluation tier
(`Shor.Reflect.policySubmissionChecks`) are checked there, compiled natively,
before anything is printed; a failing submission prints nothing on stdout
and exits `1`, so the `&&` line above yields a `policy.json` only for a
submission that passed both.

By default the policy is compiled on the scan width rule, as it always was.
`--exact-widths` compiles the same bands at exact widths
(`WidthRule.exact`, `Framework/Policy.lean`): the same certificate covers it
(`PolicySubmission.correct_exact`), the IR templates are the same, the
evaluation tier compiles the real circuit at exact widths, and the document's
`ir.width_rule` gives the widths a consumer must use.

**`PolicyTemplate.lean` is the only file a policy submitter owns.** Per band
it holds exactly what `Template.lean` holds for one table — `k`, `pts`,
`ops`, the C1 lemma and the `ShorLoweringSetup` record with C1–C4 proved —
and then one thing more, once:

```lean
def policy : ShorPolicySubmission where
  bands := [(40, band0), (14, band1)]
  sorted := by decide
```

`sorted` says the thresholds strictly decrease. That is the only obligation a
policy adds on top of its bands' own C1–C4, and it is what makes "band `i`
covers `[tᵢ, tᵢ₋₁)`" literally true, so every width is served by exactly one
band and the width dispatcher is a clean chain of guards. It is decidable, so
`by decide` closes it. Widths below the last threshold take the schoolbook
leaf.

There is deliberately **no** condition requiring a band's table to shrink the
width on its own band. The recursion already falls back to the leaf when the
chosen table does not shrink (`ShorLoweringPolicy.Stops`), so a
non-shrinking band is dead weight rather than unsoundness: it is selected, it
declines to recurse, and the leaf runs instead. `Shor.Policy.bandShrinks` in
`PolicyDecide.lean` reports exactly that, and `policy.json` carries it per
band as `bands[].shrinks`. It is a warning a submitter should act on by
raising a threshold, never a reason to reject a policy.

The shipped example is a worked instance of that warning. Its lower band is
the `k = 2` table from `Template.lean` at threshold `14`, not `12`: that
table's `nextWidth` maps `12 ↦ 12` and `13 ↦ 13`, so at the bottom two widths
of a band starting at `12` it would decline to recurse. `PolicyTests.lean`
records the failing check at `12`, so the advisory has a test as well as a
definition; the passing one at `14` is what `policy.json` reports.

### A policy gets the same two tiers a table does

**The certificate.** `Shor.policy_submission_correct` is generic in the
policy, so a policy existing is the whole argument; there is no
per-submission proof, exactly as for a table. `Shor.submission_correct` is
literally its one-band case, via `Shor.ShorPolicySubmission.ofSetup`.

**The IR, and its agreement with the circuit.** `Shor.Reflect.buildPolicyDoc`,
run by the executable, builds one dispatcher per phase-product flavour, one body template per band,
and the shared `qft`/`shor_gate`/`shor`/leaf templates; the dispatcher is the
entry point and carries the policy's guard chain.
`Shor.Reflect.policySubmissionChecks` then pins that document against the
real compiled circuit. **The dispatchers are checked exactly:** the
document's `phase_product` and `cphase_product` must be
`dispatcherTemplate` of the submitted policy, whose routing is a theorem
(`Emit/Symbolic/Dispatcher.lean`), not a sampled check. **The bodies are
checked on a probe:** a band body names its table, its `coeff` offset and
the opaque oracles, never a threshold, so the sampled checks run on the
*probe submission* — the same setups in the same band order at the smallest
strictly decreasing thresholds where each table shrinks, a band whose table
never shrinks being probed at the leaf as the compiler treats it — with the
dispatchers rebuilt for it. There, **one level per distinct table:** the
first band with a given table has its body instantiated at its probe
threshold with child calls treated as the phase-product leaves the compiler
emits there — each call's width and capacity arguments checked against the
registers it passes — and compared with the compiler's one-level step on the
real layout; every later band with the same table must be that body with its
`coeff` indices shifted by the offset difference, which is what the extractor
emits for it. **Full depth where cheap:** the entry template is instantiated
and compared with the fully lowered circuit at the widths reaching one, two
and three levels of the probe's recursion, in both reserve regimes, provided
they fit `policyFullDepthLeafBudget` (100 leaves). Then `qft` at odd widths
straddling the lowest probe threshold, the leaves, and the reference Shor
instances, as for a single table. The widths sampled depend on the tables
only, so the cost of the tier does not grow with the submission's
thresholds.

What the one-level check sees and does not see: it sees a band's
allocations, its table's arithmetic, every checkpoint's angle and register
arguments including each child's reserve slice, and it rejects an IR that
hands a child a capacity other than the reserve it sliced (the bug class
`Emit/Tests.lean`'s `TopChunkReserve` section anchors). It does not
unroll the child. Cross-level composition is exercised
at full depth only at the budgeted widths of the probe.

As for a table, this tier is **evaluation at sampled widths, not a theorem**.
One part of it is a theorem and is worth naming: `IR.dispatcherCallAt_dispatcherTemplate`
proves the emitted guard chain picks the same band as
`ShorLoweringPolicy.choose` at *every* width, so which body a width routes to
is not something the sampling has to establish.

A consumer needs no new oracles: the same ten opaque names with the same
arities serve a policy document, because `Policy.reserveNeed P` is already a
function of the operand widths alone. One convention changes — `coeff`'s
point index is a position in the bands' interpolation points *concatenated*,
band 0 first — because two bands with different `k` would otherwise both emit
`coeff 0` meaning different numbers.

## CI for a submissions repo

This repository's own CI (`.github/workflows/ci.yml`) builds the lake
targets, runs the layer script and checks the docs graph. It does not apply
the diff rule or the lexical gate below as an acceptance control — those are
about a *submission*, and this repository has none to police. Step 1 is
therefore enforced only by a submissions repo.

Such a repo should run, per pull request:

1. **The diff rule.** A PR may change only its copy of
   `Submission/Template.lean` — or, for a policy submission,
   `Submission/PolicyTemplate.lean`, and only one of the two. Everything
   else — `Decide.lean`, `Audit.lean`, `Check.lean`, `Correct.lean`,
   `Score.lean`, `Main.lean`, `PolicyDecide.lean`, `PolicyCheck.lean`,
   `PolicyMain.lean`, `Framework/`, `Implementation/`, `lakefile.lean` — is
   repo-owned. A PR touching any of it changes the rules rather than
   answering them.

   Together with a lexical gate on what `Template.lean` may contain. The
   patterns are anchored at code positions, so the file's own prose
   describing the restriction does not trip it:

   ```bash
   ! grep -nE \
     '^[[:space:]]*(@\[|attribute[[:space:]]*\[)[^]]*(implemented_by|extern|csimp)|^[[:space:]]*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(unsafe|run_cmd|run_meta|initialize|elab|macro|syntax|notation)\b|^import[[:space:]]+Lean\b|^[[:space:]]*set_option[[:space:]]+debug' \
     Submission/Template.lean    # or Submission/PolicyTemplate.lean
   ```

   The gate applies unchanged to a policy template, which is why
   `scripts/check_template_lexical.sh` takes the file as an argument and this
   repository's CI runs it on both.

   The reason is that two tiers read the table and they can be made to
   disagree. C1–C4 are reduced by the *kernel*, which sees a definition's
   body; the IR extraction (`Lean.Meta.evalExpr`), the two `native_decide`
   lines and `lake exe forshor_submission` all run *compiled* code, which
   sees whatever the compiler was told to emit. An
   `@[implemented_by fakeOps] def ops := realOps` is kernel-checked on
   `realOps` while `ir.json` is computed from `fakeOps` — so the accepted
   table and the scored circuit are different objects. `implemented_by` and
   `extern` add no axiom, so step 2's `#assert_axioms` cannot see them;
   nothing in step 2 catches this. `csimp` needs a proof of
   `realOps = fakeOps`, so it is only an opening if that proof is itself
   unsound. The remaining tokens (`unsafe`, `run_cmd`/`run_meta`,
   `initialize`, `elab`/`macro`/`syntax`/`notation`, `import Lean`,
   `set_option debug`) are the metaprogramming surface that can reach the
   environment directly.

   A submitter's table needs none of this: the template is three
   definitions and one record.

2. **The build and the print**:

   ```bash
   lake build Submission && lake exe forshor_submission > ir.json
   # or, for a policy submission:
   lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
   ```

   This is where the four side conditions are checked — per band, for a
   policy, along with the thresholds' strict decrease — and where
   `#assert_axioms` runs, and where the IR is pinned against the real
   circuit (for a policy, the `lake exe` step runs that tier and prints
   nothing if it fails). `ir.json` / `policy.json` is what the resource
   estimator reads.

   Note what the two steps divide between them. Step 2's `#assert_axioms`
   certifies which axioms the proofs rest on. It says nothing about the
   compiled code the IR and `ir.json` come from — that is step 1's lexical
   gate, and it is the only thing standing there.
