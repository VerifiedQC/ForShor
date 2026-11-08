import ForShor.ShorVerification.Submission.Policies.Common

/-!
# `policies/threshold_degenerate_ptp.json` as a `PTPPolicy`

Generated from the sister repository's policy JSON by a script that is not part of this repository. Source: "FAULT: STO reference PTP, lowest k=2 band threshold 66 -> 5, plus the k=6 table as a band at threshold 1 (applied at width 4 < k = 6)"

The negation method is the default (`.oneQubit`); the policy states no override.
-/

namespace PolicySubmission.Policies.ThresholdDegeneratePtp

open Shor Operations

/-- Table 0: k = 6, 16 points, 109 operations. -/
abbrev t0K : ℕ := 6

def t0Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int 4, Point.int (-4), Point.int 8, Point.int (-8), Point.int 16, Point.int (-16), Point.int 32, Point.int (-32), Point.int 64, Point.int (-64)]

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
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 2
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 1
  , valid_ops.addScaled 2 3 true 2
  , valid_ops.addScaled 2 5 true 5
  , valid_ops.addScaled 2 5 false 1
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 3
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 6
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 4
  , valid_ops.addScaled 2 3 true 5
  , valid_ops.addScaled 2 5 true 10
  , valid_ops.addScaled 2 5 false 6
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 7
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 10
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 7
  , valid_ops.addScaled 2 3 true 8
  , valid_ops.addScaled 2 5 true 15
  , valid_ops.addScaled 2 5 false 11
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 11
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 14
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 10
  , valid_ops.addScaled 2 3 true 11
  , valid_ops.addScaled 2 5 true 20
  , valid_ops.addScaled 2 5 false 16
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 15
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 18
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 13
  , valid_ops.addScaled 2 3 true 14
  , valid_ops.addScaled 2 5 true 25
  , valid_ops.addScaled 2 5 false 21
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 19
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 22
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 16
  , valid_ops.addScaled 2 3 true 17
  , valid_ops.addScaled 2 5 true 30
  , valid_ops.addScaled 2 5 false 26
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 23
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.shiftR 1 7
  , valid_ops.addScaled 2 4 true 24
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 2 1 false 6
  , valid_ops.shiftR 2 12
  , valid_ops.addScaled 1 5 true 24
  , valid_ops.addScaled 1 3 true 12 ]

theorem t0Hpts : t0Pts.length = PTP.pointCount t0K := by decide

/-- Table 1: k = 4, 10 points, 48 operations. -/
abbrev t1K : ℕ := 4

def t1Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int 4, Point.int (-4), Point.int 8, Point.int (-8)]

def t1Ops : Prog t1K :=
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
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.shiftR 1 4
  , valid_ops.addScaled 2 1 false 3
  , valid_ops.shiftR 2 6
  , valid_ops.addScaled 1 3 true 6 ]

theorem t1Hpts : t1Pts.length = PTP.pointCount t1K := by decide

/-- Table 2: k = 2, 4 points, 8 operations. -/
abbrev t2K : ℕ := 2

def t2Pts : List Point :=
  [Point.int 1, Point.int 0, Point.int (-1), Point.frac 0]

def t2Ops : Prog t2K :=
  [ valid_ops.addScaled 1 0 false 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 1 false 0 ]

theorem t2Hpts : t2Pts.length = PTP.pointCount t2K := by decide

/-- Table 0 as a `PTPTable` (contract checked below). -/
def tbl0 : PTP.PTPTable := ⟨t0K, t0Pts, t0Ops⟩

/-- Table 1 as a `PTPTable` (contract checked below). -/
def tbl1 : PTP.PTPTable := ⟨t1K, t1Pts, t1Ops⟩

/-- Table 2 as a `PTPTable` (contract checked below). -/
def tbl2 : PTP.PTPTable := ⟨t2K, t2Pts, t2Ops⟩

/-- The policy: bands widest first. -/
def policy : PTP.PTPPolicy where
  bands := [⟨2048, tbl0⟩, ⟨398, tbl1⟩, ⟨122, tbl2⟩, ⟨5, tbl2⟩, ⟨1, tbl0⟩]

/-- The target width the threshold rule is checked from. -/
def target : ℕ := 2048

/-- `PTPPolicy.check`: thresholds strictly decrease and every table passes the PTP contract. -/
theorem check : policy.check = true := by decide +kernel

/-- The exact-width threshold rule (`PTPPolicy.chainContractsTight`). -/
theorem chain_exact : policy.chainContractsTight target = false := by decide +kernel

/-- **Verdict**: both of the above (derived from them). -/
theorem accepted : ptpAccepts policy target = false := by
  simp [ptpAccepts, check, chain_exact]

/-- The exact-width recursion ladder from the target. -/
theorem ladder_exact : policy.ladderX target = [(2048, some 6), (375, some 2), (189, some 2), (96, some 2), (50, some 2), (27, some 2), (15, some 2), (9, some 2), (6, some 2), (5, some 2), (4, none)] := by decide +kernel

/-- The policy names no negation method, so it is priced with the default one: `oneQubit` (one clean qubit). -/
theorem negation_default : policy.negation = .oneQubit := rfl

end PolicySubmission.Policies.ThresholdDegeneratePtp

open Shor.Audit

#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.t0Hpts
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.t1Hpts
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.t2Hpts
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.check
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.chain_exact
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.accepted
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.ladder_exact
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.policy
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDegeneratePtp.negation_default
