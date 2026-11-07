import ForShor.ShorVerification.Submission.Policies.Common

/-!
# Board row `82eaf805f71c` (PhaseTripleProduct, n = 2048) as a `PTPPolicy`

Board row `82eaf805f71c` of the public results board: planner policy `forshor_sub1` (STO submission PR 3, `submission/search-ptp-k4`); its one table is the k = 4 target of `evaluation/engine/data/sto_archive/82eaf805f71cc6a0dd8154007729d14b9f63d601/operations.json`.
The bands (thresholds, k, point orders, operation programs) are the `policyJson` of the row's panel in the v2 epoch input
(`forshor-site-v2-page/infra/staging/seed-v2/epoch-input.json`, panels `.../policies/82eaf805f71c/ptp-*.json`, identical at all four deltas);
the programs are byte-identical to the archived tables named above (checked outside Lean).
Ladder printed on the row: `2048:4 -> 522:4 -> 142:leaf`; it is proved below to be this policy's exact-width ladder.

Generated from the policy JSON of the sister repository's exported results by a script that is not part of this repository.
The negation method is the default (`.oneQubit`); the policy states no override. No table of this policy contains a `negate`.
-/

namespace PolicySubmission.Policies.Board.Row82eaf805f71c

open Shor Operations

/-- Table 0: k = 4, 10 points, 49 operations. -/
abbrev t0K : ℕ := 4

def t0Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int 4, Point.int (-4), Point.int 8, Point.int (-8)]

def t0Ops : Prog t0K :=
  [ valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 2 0 false 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 3
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 1
  , valid_ops.addScaled 2 3 true 2
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 4
  , valid_ops.addScaled 2 3 true 5
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 7
  , valid_ops.addScaled 2 3 true 8
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftR 2 1
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 1 3 true 9
  , valid_ops.shiftR 2 6
  , valid_ops.shiftR 1 3 ]

theorem t0Hpts : t0Pts.length = PTP.pointCount t0K := by decide

/-- Table 0 as a `PTPTable` (contract checked below). -/
def tbl0 : PTP.PTPTable := ⟨t0K, t0Pts, t0Ops⟩

/-- The policy: bands widest first. -/
def policy : PTP.PTPPolicy where
  bands := [⟨522, tbl0⟩]

/-- The target width the threshold rule is checked from. -/
def target : ℕ := 2048

/-- The default negation method (nothing is overridden). -/
theorem negation_default : policy.negation = .oneQubit := rfl

/-- `PTPPolicy.check`: thresholds strictly decrease and every table passes the PTP contract. -/
theorem check : policy.check = true := by decide +kernel

/-- The exact-width threshold rule (`PTPPolicy.chainContractsTight`). -/
theorem chain_exact : policy.chainContractsTight target = true := by decide +kernel

/-- **Verdict**: both of the above (derived from them). -/
theorem accepted : ptpAccepts policy target = true := by
  simp [ptpAccepts, check, chain_exact]

/-- The exact-width ladder of the policy from 2048 is the ladder printed on board row `82eaf805f71c`: `2048:4 -> 522:4 -> 142:leaf`. -/
theorem ladder_exact : policy.ladderX target = [(2048, some 4), (522, some 4), (142, none)] := by decide +kernel

end PolicySubmission.Policies.Board.Row82eaf805f71c

open Shor.Audit

#assert_axioms _root_.PolicySubmission.Policies.Board.Row82eaf805f71c.t0Hpts
#assert_axioms _root_.PolicySubmission.Policies.Board.Row82eaf805f71c.negation_default
#assert_axioms _root_.PolicySubmission.Policies.Board.Row82eaf805f71c.check
#assert_axioms _root_.PolicySubmission.Policies.Board.Row82eaf805f71c.chain_exact
#assert_axioms _root_.PolicySubmission.Policies.Board.Row82eaf805f71c.accepted
#assert_axioms _root_.PolicySubmission.Policies.Board.Row82eaf805f71c.ladder_exact
#assert_axioms _root_.PolicySubmission.Policies.Board.Row82eaf805f71c.policy
