import ForShor.ShorVerification.Submission.Policies.Common

/-!
# Board row `c733baf3cd08` (PhaseTripleProduct, n = 2048) as a `PTPPolicy`

Board row `c733baf3cd08` of the public results board: baseline policy `forshor_sub30` (single arity k = 6); its table is the k = 6 target of `evaluation/engine/data/sto_archive/6f7d25984ff8f4db772a7449c097a6e16098f8be/operations.json`.
The bands (thresholds, k, point orders, operation programs) are the `policyJson` of the row's panel in the v2 epoch input
(`forshor-site-v2-page/infra/staging/seed-v2/epoch-input.json`, panels `.../policies/c733baf3cd08/ptp-*.json`, identical at all four deltas);
the programs are byte-identical to the archived tables named above (checked outside Lean).
Ladder printed on the row: `2048:6 -> 359:6 -> 80:leaf`; it is proved below to be this policy's exact-width ladder.

Generated from the policy JSON of the sister repository's exported results by a script that is not part of this repository.
The negation method is the default (`.oneQubit`); the policy states no override. No table of this policy contains a `negate`.
-/

namespace PolicySubmission.Policies.Board.Rowc733baf3cd08

open Shor Operations

/-- Table 0: k = 6, 16 points, 126 operations. -/
abbrev t0K : ℕ := 6

def t0Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.frac (2), Point.frac (-2), Point.int 4, Point.int (-4), Point.frac (4), Point.frac (-4), Point.int 8, Point.int (-8), Point.frac (8), Point.frac (-8)]

def t0Ops : Prog t0K :=
  [ valid_ops.addScaled 2 0 false 0
  , valid_ops.addScaled 2 4 false 0
  , valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 1 5 false 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 5
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftR 2 1
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 1 5 true 0
  , valid_ops.addScaled 1 3 true 0
  , valid_ops.addScaled 2 4 true 0
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.addScaled 0 4 false 4
  , valid_ops.shiftL 1 1
  , valid_ops.addScaled 1 3 false 3
  , valid_ops.addScaled 1 5 false 5
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftL 0 1
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftR 0 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 5 true 5
  , valid_ops.addScaled 1 3 true 3
  , valid_ops.shiftR 1 1
  , valid_ops.addScaled 0 4 true 4
  , valid_ops.addScaled 0 2 true 2
  , valid_ops.addScaled 5 1 false 4
  , valid_ops.addScaled 5 3 false 2
  , valid_ops.shiftL 4 1
  , valid_ops.addScaled 4 0 false 5
  , valid_ops.addScaled 4 2 false 3
  , valid_ops.addScaled 4 5 false 0
  , valid_ops.shiftL 5 1
  , valid_ops.addScaled 5 4 true 0
  , valid_ops.phaseProduct 4
  , valid_ops.phaseProduct 5
  , valid_ops.addScaled 5 4 false 0
  , valid_ops.shiftR 5 1
  , valid_ops.addScaled 4 5 true 0
  , valid_ops.addScaled 4 2 true 3
  , valid_ops.addScaled 4 0 true 5
  , valid_ops.shiftR 4 1
  , valid_ops.addScaled 5 3 true 2
  , valid_ops.addScaled 5 1 true 4
  , valid_ops.addScaled 0 2 false 4
  , valid_ops.addScaled 0 4 false 8
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 3 false 6
  , valid_ops.addScaled 1 5 false 10
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftL 0 1
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftR 0 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 5 true 10
  , valid_ops.addScaled 1 3 true 6
  , valid_ops.shiftR 1 2
  , valid_ops.addScaled 0 4 true 8
  , valid_ops.addScaled 0 2 true 4
  , valid_ops.addScaled 5 1 false 8
  , valid_ops.addScaled 5 3 false 4
  , valid_ops.shiftL 4 2
  , valid_ops.addScaled 4 0 false 10
  , valid_ops.addScaled 4 2 false 6
  , valid_ops.addScaled 4 5 false 0
  , valid_ops.shiftL 5 1
  , valid_ops.addScaled 5 4 true 0
  , valid_ops.phaseProduct 4
  , valid_ops.phaseProduct 5
  , valid_ops.addScaled 5 4 false 0
  , valid_ops.shiftR 5 1
  , valid_ops.addScaled 4 5 true 0
  , valid_ops.addScaled 4 2 true 6
  , valid_ops.addScaled 4 0 true 10
  , valid_ops.shiftR 4 2
  , valid_ops.addScaled 5 3 true 4
  , valid_ops.addScaled 5 1 true 8
  , valid_ops.addScaled 0 2 false 6
  , valid_ops.addScaled 0 4 false 12
  , valid_ops.shiftL 1 3
  , valid_ops.addScaled 1 3 false 9
  , valid_ops.addScaled 1 5 false 15
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftL 0 1
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftR 0 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 5 true 15
  , valid_ops.addScaled 1 3 true 9
  , valid_ops.shiftR 1 3
  , valid_ops.addScaled 0 4 true 12
  , valid_ops.addScaled 0 2 true 6
  , valid_ops.addScaled 5 1 false 12
  , valid_ops.addScaled 5 3 false 6
  , valid_ops.shiftL 4 3
  , valid_ops.addScaled 4 0 false 15
  , valid_ops.addScaled 4 2 false 9
  , valid_ops.addScaled 4 5 false 0
  , valid_ops.shiftL 5 1
  , valid_ops.addScaled 5 4 true 0
  , valid_ops.phaseProduct 4
  , valid_ops.phaseProduct 5
  , valid_ops.addScaled 5 4 false 0
  , valid_ops.shiftR 5 1
  , valid_ops.addScaled 4 5 true 0
  , valid_ops.addScaled 4 2 true 9
  , valid_ops.addScaled 4 0 true 15
  , valid_ops.shiftR 4 3
  , valid_ops.addScaled 5 3 true 6
  , valid_ops.addScaled 5 1 true 12 ]

theorem t0Hpts : t0Pts.length = PTP.pointCount t0K := by decide

/-- Table 0 as a `PTPTable` (contract checked below). -/
def tbl0 : PTP.PTPTable := ⟨t0K, t0Pts, t0Ops⟩

/-- The policy: bands widest first. -/
def policy : PTP.PTPPolicy where
  bands := [⟨359, tbl0⟩]

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

/-- The exact-width ladder of the policy from 2048 is the ladder printed on board row `c733baf3cd08`: `2048:6 -> 359:6 -> 80:leaf`. -/
theorem ladder_exact : policy.ladderX target = [(2048, some 6), (359, some 6), (80, none)] := by decide +kernel

end PolicySubmission.Policies.Board.Rowc733baf3cd08

open Shor.Audit

#assert_axioms _root_.PolicySubmission.Policies.Board.Rowc733baf3cd08.t0Hpts
#assert_axioms _root_.PolicySubmission.Policies.Board.Rowc733baf3cd08.negation_default
#assert_axioms _root_.PolicySubmission.Policies.Board.Rowc733baf3cd08.check
#assert_axioms _root_.PolicySubmission.Policies.Board.Rowc733baf3cd08.chain_exact
#assert_axioms _root_.PolicySubmission.Policies.Board.Rowc733baf3cd08.accepted
#assert_axioms _root_.PolicySubmission.Policies.Board.Rowc733baf3cd08.ladder_exact
#assert_axioms _root_.PolicySubmission.Policies.Board.Rowc733baf3cd08.policy
