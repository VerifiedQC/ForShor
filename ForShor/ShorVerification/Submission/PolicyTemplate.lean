import ForShor.ShorVerification.Framework.ToomCookTable
import ForShor.ShorVerification.Framework.Policy
import ForShor.ShorVerification.Submission.Decide

/-!
# The file a policy submitter copies

A **policy** submission is a list of Toom-Cook tables indexed by operand
width: a wide table at the top of the recursion, narrower ones below it, and
the schoolbook leaf under an explicit threshold. The score is a gate count at
one fixed size, not an asymptotic exponent, and at a fixed size the optimum is
a cascade rather than a single radix — which is the whole reason this second
kind of submission exists.

Everything a table submitter owns, a policy submitter owns once per band:

| | what to write, per band |
|---|---|
| `k` | the number of limb registers, `1 < k ≤ 6` |
| `pts` | the interpolation points, in the order the checkpoints consume them |
| `ops` | the table |
| `setup` | the `ShorLoweringSetup` record, with C1–C4 proved |

and then one thing more, once:

| | what to write |
|---|---|
| `policy` | the bands as `(threshold, setup)` pairs, widest first, with `sorted := by decide` |

Then run

```bash
lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
```

and if the build is green the policy is admissible. Nothing outside this file
is edited.

## What `sorted` is, and why it is the only new obligation

`ShorPolicySubmission.sorted` says the thresholds strictly decrease. That is
what makes "band `i` covers `[tᵢ, tᵢ₋₁)`" literally true, so every width is
served by exactly one band and `choose` is a clean chain of guards. It is
decidable — Batteries' `Decidable (l.IsChain R)` over `Nat.decLt` — so `by
decide` closes it. Everything else is per-band C1–C4, proved exactly as
[`Template.lean`](Template.lean) proves them for one table.

There is deliberately **no** admissibility condition saying each band's table
shrinks the width on its own band. The recursion already falls back to the
leaf when a table does not shrink (`ShorLoweringPolicy.Stops`), so a
non-shrinking band is a performance problem, not a soundness one.
`Policy.bandShrinks` in [`PolicyDecide.lean`](PolicyDecide.lean) is offered as
an advisory check for exactly that, and `policy.json` reports it per band.

## The policy shipped here

Two bands and a leaf:

* at width `≥ 40`, the `k = 3` reference table (five canonical points);
* at width `14 ≤ n < 40`, the `k = 2` table [`Template.lean`](Template.lean)
  ships;
* below `14`, no table — the schoolbook leaf.

Both tables are the ones `Submission/Decide.lean`'s smoke tests already
kernel-check. The thresholds are illustrative: choosing them well is the
submitter's optimisation problem, and nothing here constrains them beyond
strict decrease.

The lower threshold is `14` rather than `12` for a reason worth copying.
`nextWidth` for this `k = 2` table is `12 ↦ 12` and `13 ↦ 13`: at those two
widths the table does not shrink the operand, so the recursion would fall
straight through to the schoolbook leaf and the band would be selected only
to decline. That is sound but wasteful, and it is exactly what
`Policy.bandShrinks` reports; `PolicyTests.lean` records the failing check
at `12`, and `policy.json` carries the passing one at `14`.
-/

namespace PolicySubmission

open Shor Operations

/-! =========================================================
    EDIT HERE — band 0, used at the widest operands
========================================================= -/

/-- **Edit me.** Band 0's arity. -/
abbrev band0K : ℕ := 3

/-- **Edit me.** Band 0's interpolation points, in consumption order. -/
def band0Pts : List Point :=
  [Point.int 0, Point.int (-1), Point.int 1, Point.int (-2), Point.int 2]

/-- **Edit me.** Band 0's table. -/
def band0Ops : Prog band0K :=
  [ valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.addScaled 0 2 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 2 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.addScaled 0 1 true 1
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 2
  , valid_ops.addScaled 0 1 false 1
  , valid_ops.addScaled 0 1 false 1
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 2 true 2
  , valid_ops.addScaled 0 1 true 1
  ]

/-- **Edit me.** C1 for band 0. -/
theorem band0Hpts : band0Pts.length = q band0K := rfl

/-- **Edit me.** Band 0 as a submission record: the table with C1–C4 proved,
each field reduced by Lean's kernel. -/
def band0 : ShorLoweringSetup where
  k := band0K
  hk := by decide
  pts := band0Pts
  hpts := band0Hpts
  good := goodToomCookPoints_of_distinct band0Hpts (by decide +kernel)
  ops := band0Ops
  consumes := by decide +kernel
  returns := by decide +kernel

/-! =========================================================
    EDIT HERE — band 1, used on the middle widths
========================================================= -/

/-- **Edit me.** Band 1's arity. -/
abbrev band1K : ℕ := 2

/-- **Edit me.** Band 1's interpolation points. -/
def band1Pts : List Point :=
  [Point.int 0, Point.int (-1), Point.int 1]

/-- **Edit me.** Band 1's table. -/
def band1Ops : Prog band1K :=
  [ valid_ops.phaseProduct 0
  , valid_ops.negate 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.negate 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  ]

/-- **Edit me.** C1 for band 1. -/
theorem band1Hpts : band1Pts.length = q band1K := rfl

/-- **Edit me.** Band 1 as a submission record. -/
def band1 : ShorLoweringSetup where
  k := band1K
  hk := by decide
  pts := band1Pts
  hpts := band1Hpts
  good := goodToomCookPoints_of_distinct band1Hpts (by decide +kernel)
  ops := band1Ops
  consumes := by decide +kernel
  returns := by decide +kernel

/-! =========================================================
    EDIT HERE — the policy
========================================================= -/

/-- **Edit me.** The bands, widest first, each with the smallest operand
width it covers. `sorted` is the one obligation a policy adds on top of its
bands' own C1–C4, and `decide` closes it. -/
def policy : ShorPolicySubmission where
  bands := [(40, band0), (14, band1)]
  sorted := by decide

end PolicySubmission
