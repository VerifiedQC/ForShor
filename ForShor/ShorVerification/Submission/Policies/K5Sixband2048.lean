import ForShor.ShorVerification.Submission.Policies.Common

/-!
# `policies/k5_sixband_2048.json` as a `ShorPolicySubmission`

Generated from the sister repository's policy JSON by a script that is not part of this repository. Source: "six-band k5/k4/k3/k2/k2/k2 PhaseProduct from STO archive tables (thresholds = chain widths from 2048)"

The negation method is the default (`.oneQubit`); the policy states no override.
-/

namespace PolicySubmission.Policies.K5Sixband2048

open Shor Operations

/-- Table 0: k = 5, 9 points, 52 operations. -/
abbrev t0K : ℕ := 5

def t0Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int 4, Point.int (-4), Point.int 8]

def t0Ops : Prog t0K :=
  [ valid_ops.addScaled 2 0 false 0
  , valid_ops.addScaled 2 4 false 0
  , valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 1 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 4
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.addScaled 1 4 false 2
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 1
  , valid_ops.addScaled 2 3 true 2
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
  , valid_ops.addScaled 2 1 false 0
  , valid_ops.shiftL 1 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 2 0 true 1
  , valid_ops.addScaled 2 4 false 7
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.shiftR 1 3
  , valid_ops.addScaled 2 4 true 8
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 2 1 false 2
  , valid_ops.addScaled 1 3 true 4
  , valid_ops.shiftR 2 4
  , valid_ops.addScaled 0 1 false 3
  , valid_ops.addScaled 0 2 false 6
  , valid_ops.addScaled 0 3 false 9
  , valid_ops.addScaled 0 4 false 12
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 4 true 12
  , valid_ops.addScaled 0 3 true 9
  , valid_ops.addScaled 0 2 true 6
  , valid_ops.addScaled 0 1 true 3 ]

theorem t0Hpts : t0Pts.length = q t0K := rfl

/-- Table 0 as a submission record: C1-C4, reduced by the kernel. -/
def t0 : ShorLoweringSetup where
  k := t0K
  hk := by decide
  pts := t0Pts
  hpts := t0Hpts
  good := goodToomCookPoints_of_distinct t0Hpts (by decide +kernel)
  ops := t0Ops
  consumes := by decide +kernel
  returns := by decide +kernel

/-- Table 1: k = 4, 7 points, 45 operations. -/
abbrev t1K : ℕ := 4

def t1Pts : List Point :=
  [Point.int 0, Point.int 2, Point.int (-2), Point.frac (4), Point.frac (-4), Point.int 1, Point.int (-1)]

def t1Ops : Prog t1K :=
  [ valid_ops.shiftL 2 2
  , valid_ops.addScaled 2 0 false 0
  , valid_ops.shiftL 3 3
  , valid_ops.addScaled 3 1 false 1
  , valid_ops.addScaled 3 2 false 0
  , valid_ops.shiftL 2 1
  , valid_ops.addScaled 2 3 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 3
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 2 3 false 0
  , valid_ops.shiftR 2 1
  , valid_ops.addScaled 3 1 true 1
  , valid_ops.addScaled 3 2 true 0
  , valid_ops.shiftR 3 3
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.shiftR 2 2
  , valid_ops.shiftL 0 6
  , valid_ops.shiftL 1 4
  , valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.shiftL 1 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftR 1 1
  , valid_ops.addScaled 0 2 true 2
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.addScaled 1 3 true 0
  , valid_ops.shiftR 1 4
  , valid_ops.shiftR 0 6
  , valid_ops.addScaled 0 2 false 0
  , valid_ops.addScaled 1 3 false 0
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftL 0 1
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftR 0 1
  , valid_ops.addScaled 1 3 true 0
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 0 2 true 0 ]

theorem t1Hpts : t1Pts.length = q t1K := rfl

/-- Table 1 as a submission record: C1-C4, reduced by the kernel. -/
def t1 : ShorLoweringSetup where
  k := t1K
  hk := by decide
  pts := t1Pts
  hpts := t1Hpts
  good := goodToomCookPoints_of_distinct t1Hpts (by decide +kernel)
  ops := t1Ops
  consumes := by decide +kernel
  returns := by decide +kernel

/-- Table 2: k = 3, 5 points, 19 operations. -/
abbrev t2K : ℕ := 3

def t2Pts : List Point :=
  [Point.int 0, Point.int 1, Point.frac 0, Point.int 2, Point.int (-2)]

def t2Ops : Prog t2K :=
  [ valid_ops.addScaled 1 0 false 0
  , valid_ops.addScaled 1 2 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 2
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.addScaled 0 2 false 2
  , valid_ops.shiftL 1 1
  , valid_ops.addScaled 1 0 false 0
  , valid_ops.shiftL 0 1
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.shiftR 0 1
  , valid_ops.addScaled 1 0 true 0
  , valid_ops.shiftR 1 1
  , valid_ops.addScaled 0 2 true 2 ]

theorem t2Hpts : t2Pts.length = q t2K := rfl

/-- Table 2 as a submission record: C1-C4, reduced by the kernel. -/
def t2 : ShorLoweringSetup where
  k := t2K
  hk := by decide
  pts := t2Pts
  hpts := t2Hpts
  good := goodToomCookPoints_of_distinct t2Hpts (by decide +kernel)
  ops := t2Ops
  consumes := by decide +kernel
  returns := by decide +kernel

/-- Table 3: k = 2, 3 points, 5 operations. -/
abbrev t3K : ℕ := 2

def t3Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1]

def t3Ops : Prog t3K :=
  [ valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0 ]

theorem t3Hpts : t3Pts.length = q t3K := rfl

/-- Table 3 as a submission record: C1-C4, reduced by the kernel. -/
def t3 : ShorLoweringSetup where
  k := t3K
  hk := by decide
  pts := t3Pts
  hpts := t3Hpts
  good := goodToomCookPoints_of_distinct t3Hpts (by decide +kernel)
  ops := t3Ops
  consumes := by decide +kernel
  returns := by decide +kernel

/-- The policy: bands widest first (threshold, table), thresholds strictly decreasing. -/
def policy : ShorPolicySubmission where
  bands := [(2048, t0), (440, t1), (121, t2), (49, t3), (28, t3), (17, t3)]
  sorted := by decide

/-- Every band's table passes C1-C4 (the fields of the submission record). -/
theorem admissible : policy.policy.Admissible := policy.policy_admissible

/-- The target width the threshold rule is checked from. -/
def target : ℕ := 2048

/-- Threshold rule at exact widths (the benchmark's acceptance mode). -/
theorem chain_exact : chainContracts .exact policy.policy target = true := by decide +kernel

/-- Threshold rule at the scan widths. -/
theorem chain_scan : chainContracts .scan policy.policy target = true := by decide +kernel

/-- **Verdict** at exact widths: all of the above (derived from them). -/
theorem accepted_exact : accepts .exact policy.policy target none = true := by
  simp [accepts, chain_exact]

/-- The exact-width recursion ladder from the target. -/
theorem ladder_exact : ladder .exact policy.policy target = [(2048, some 5), (425, some 3), (147, some 3), (53, some 2), (28, some 2), (16, none)] := by
  decide +kernel

/-- The scan-width recursion ladder from the target. -/
theorem ladder_scan : ladder .scan policy.policy target = [(2048, some 5), (440, some 4), (121, some 3), (49, some 2), (28, some 2), (17, some 2), (12, none)] := by
  decide +kernel

end PolicySubmission.Policies.K5Sixband2048

open Shor.Audit

#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.t0Hpts
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.t1Hpts
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.t2Hpts
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.t3Hpts
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.admissible
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.chain_exact
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.chain_scan
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.accepted_exact
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.ladder_exact
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.ladder_scan
#assert_axioms _root_.PolicySubmission.Policies.K5Sixband2048.policy
