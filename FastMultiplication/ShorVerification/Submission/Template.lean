import FastMultiplication.ShorVerification.Framework.ToomCookTable
import FastMultiplication.ShorVerification.Submission.Decide

/-!
# The file a submitter copies

A submission to this challenge is a Toom-Cook table: an arithmetic program
`ops` over `k` limb registers, plus the interpolation points `pts` its
`phaseProduct` checkpoints evaluate at, **and a proof that the pair is
admissible**. Everything else — the quantum construction, its correctness
proof, the precision, the trial count, the IR the resource estimate is
computed from — is fixed by this repository and is the same for every
submission.

This file is the whole of what a submitter owns. It is three definitions and
one record:

| | what to write |
|---|---|
| `k` | the number of limb registers, `1 < k ≤ 6` |
| `pts` | the interpolation points, in the order the checkpoints consume them |
| `ops` | the table |
| `setup` | the record, with C1–C4 proved |

Then run

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

and if the build is green the submission is admissible. Nothing outside this
file is edited.

## The proofs

The four side conditions C1–C4 are stated in
[`../Framework/ToomCookTable.lean`] and made
decidable by [`Decide.lean`], so at a concrete table each one is
a line:

```lean
theorem hpts : pts.length = q k := rfl                              -- C1

good     := goodToomCookPoints_of_distinct hpts (by decide +kernel) -- C2
consumes := by decide +kernel                                       -- C3
returns  := by decide +kernel                                       -- C4
```

`decide +kernel`, not `native_decide`: `native_decide` closes a goal by
running the *compiled evaluator* and asserting the result through
`Lean.ofReduceBool`, which is an axiom. `decide +kernel` makes Lean's kernel
reduce the decision procedure itself. `Submission/Check.lean` runs
`#assert_axioms Submission.setup`, so a submission that reaches for
`native_decide` — or for `sorry`, or for an `axiom` of its own — fails the
acceptance build with the offending axiom named.

This is not a claim that the proofs are hard. For most tables each field is
one line and the kernel does the work; what the audit buys is that the work
really was the kernel's.

C2 is the one condition that needed a lemma rather than a decision
procedure. `GoodToomCookPoints` is `det (interpMatrix …) ≠ 0`, a sum over
`(2k-1)!` permutations — 39 916 800 of them at `k = 6`. The interpolation
matrix is Mathlib's `Matrix.projVandermonde`, whose determinant factors, so
C2 is *equivalent* to the points being pairwise distinct as projective
points: `int z` is `z`, `frac c` is `1 / c`, and `frac 0` is the point at
infinity. That is the quadratic scan `PointsDistinct` performs and
`goodToomCookPoints_of_distinct` converts.

## The table shipped here

`k = 2` at the canonical points `0, -1, 1`, reaching each row by a different
route than `Shor.standardLoweringSetup 2` does: it negates register 1 rather
than subtracting, so the program is nine operations where the reference's is
seven, and the two op lists are not permutations of each other. It is a
worked example of an edit, not a copy of the reference.

A table whose checkpoints sit on a register other than 0 is *admissible* —
C1–C4 all pass — but currently fails the IR agreement check of
`Check.lean` at `n = 16`, the recursive width. This is a limitation of the
evaluation tier, not of the rules; it is why the table below keeps every
`phaseProduct` on register 0, and why `frac` points are not exercised here
(at `k = 2` the row of `frac 0` is `[0, 1]`, which is register 1's start
value and cannot be built in register 0).
-/

namespace Submission

open Shor Operations

/-! =========================================================
    EDIT HERE — and nowhere else
========================================================= -/

/-- **Edit me.** The number of limb registers. `k > 1`; `k ≤ 6` is the
supported range.

An `abbrev`, not a `def`, so that `Fin k` in `ops` below reduces to
`Fin 2` and the register indices can be written as plain numerals. -/
abbrev k : ℕ := 2

/-- **Edit me.** The interpolation points, in the order the `phaseProduct`
checkpoints consume them: leaf `l` receives coefficient `l`. Exactly
`q k = 2k - 1` of them. `Point.frac c` denotes `1/c`, and `Point.frac 0` the
point at infinity.

The order is part of the submission, not a formality: the same points
permuted are a different table, and C3 will reject the mismatch
(`Submission/Decide.lean`'s smoke tests demonstrate exactly that). -/
def pts : List Point :=
  [Point.int 0, Point.int (-1), Point.int 1]

/-- **Edit me.** The table itself.

Register 0 holds `x₀` and register 1 holds `x₁` at the start. The three
checkpoints see `[1, 0]`, `[1, -1]` and `[1, 1]` — the rows of `0`, `-1` and
`1` — and the last operation puts register 0 back, which is C4. -/
def ops : Prog k :=
  [ valid_ops.phaseProduct 0          -- reg 0 = [1, 0]  = row of 0
  , valid_ops.negate 1                -- reg 1 = [0, -1]
  , valid_ops.addScaled 0 1 false 0   -- reg 0 = [1, -1] = row of -1
  , valid_ops.phaseProduct 0
  , valid_ops.negate 1                -- reg 1 = [0, 1], back to its start
  , valid_ops.addScaled 0 1 false 0   -- reg 0 = [1, 0]
  , valid_ops.addScaled 0 1 false 0   -- reg 0 = [1, 1]  = row of 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0    -- reg 0 = [1, 0], back to its start
  ]

/-- **Edit me.** C1: one point per product coefficient. `rfl` whenever `pts`
has the right length; if it does not, that is the error to read. -/
theorem hpts : pts.length = 2 * k - 1 := rfl

/-- **Edit me.** The submission: the table together with its proofs. Each
field is one of C1–C4, and each is checked by Lean's kernel — see the module
docstring for why the spelling matters. A failure here means the table is
not admissible; read it as the check working, not as the template being
broken. -/
def setup : Shor.ShorSubmission where
  k := k
  hk := by decide
  pts := pts
  hpts := hpts
  good := goodToomCookPoints_of_distinct hpts (by decide +kernel)
  ops := ops
  consumes := by decide +kernel
  returns := by decide +kernel

end Submission
