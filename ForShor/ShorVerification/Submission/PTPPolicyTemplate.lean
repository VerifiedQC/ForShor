import ForShor.ShorVerification.Framework.ToomCookTable
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement

/-!
# The file a PhaseTripleProduct policy submitter owns

This is the PhaseTripleProduct counterpart of [`PolicyTemplate.lean`](PolicyTemplate.lean), and like it
the only file a submitter edits. A policy is a width-indexed list of tables: each band is a threshold and
a `PTPTable` (its `k`, its `3 k - 2` evaluation points in consumption order, and its program of
reversible operations). The shipped content is the board's baseline policy `forshor_sub28`
(one band, `k = 4`: `2048:4 -> 519:4 -> 139:leaf`, 56 operations); replace the tables and the thresholds.

| Edit | What |
|---|---|
| `t0K`, `t0Pts`, `t0Ops`, `t0Hpts` (one set per distinct table) | `k` is the number of limb registers, `2 ≤ k ≤ 8`; `3 k - 2` points; the program over `Fin k` registers |
| `policy.bands` | the bands, widest first: `⟨threshold, table⟩`; thresholds strictly decrease |
| `policy.negation` (optional) | `.scratch` instead of the default `.oneQubit`; the boards price `oneQubit` only |

Nothing else is a submitter's: the proofs live in [`PTPPolicyCheck.lean`](PTPPolicyCheck.lean), which is
the repo-owned root of the check. That file proves the table contract and the strict decrease of the
thresholds (`PTPPolicy.check`), and the exact-width threshold rule from 2048 (`chainContractsTight`)
by `decide +kernel`, audits the axioms, and states the correctness, the census and the peak qubit count
at this policy. Do not use `#`-commands, `native_decide`, `sorry`, `axiom`, `set_option`, `unsafe`,
`implemented_by`, `extern`, `csimp`, macros or `IO.`/`System.`: `scripts/check_template_lexical.sh` refuses the
compiled-code and metaprogramming ones before anything is built, and the audit refuses the axioms.
-/

namespace PTPPolicySubmission

open Shor Operations

/-- Table 0: k = 4, 10 points, 56 operations. -/
abbrev t0K : ℕ := 4

def t0Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.frac (2), Point.frac (-2), Point.int 4, Point.int (-4)]

def t0Ops : Prog t0K :=
  [ valid_ops.addScaled 2 0 false 0
  , valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 3
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftR 2 1
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 1 3 true 0
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.shiftL 1 1
  , valid_ops.addScaled 1 3 false 3
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftL 0 1
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftR 0 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 3 true 3
  , valid_ops.shiftR 1 1
  , valid_ops.addScaled 0 2 true 2
  , valid_ops.addScaled 3 1 false 2
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 0 false 3
  , valid_ops.addScaled 2 3 false 0
  , valid_ops.shiftL 3 1
  , valid_ops.addScaled 3 2 true 0
  , valid_ops.phaseProduct 2
  , valid_ops.phaseProduct 3
  , valid_ops.addScaled 3 2 false 0
  , valid_ops.shiftR 3 1
  , valid_ops.addScaled 2 3 true 0
  , valid_ops.addScaled 2 0 true 3
  , valid_ops.shiftR 2 1
  , valid_ops.addScaled 3 1 true 2
  , valid_ops.addScaled 0 2 false 4
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 3 false 6
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftL 0 1
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftR 0 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 3 true 6
  , valid_ops.shiftR 1 2
  , valid_ops.addScaled 0 2 true 4 ]

theorem t0Hpts : t0Pts.length = PTP.pointCount t0K := by decide

/-- Table 0 as a `PTPTable`. -/
def tbl0 : PTP.PTPTable := ⟨t0K, t0Pts, t0Ops⟩

/-- **Edit me.** The policy: bands widest first, each a threshold and a table. The default negation is one
qubit; add `negation := .scratch` to ask for the other construction (not priced on the boards). -/
def policy : PTP.PTPPolicy where
  bands := [⟨519, tbl0⟩]

end PTPPolicySubmission
