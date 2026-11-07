import ForShor.ShorVerification.Submission.Policies.Common

/-!
# `policies/threshold_declared_pp.json` as a `ShorPolicySubmission`

Generated from the sister repository's policy JSON by a script that is not part of this repository. Source: "FAULT (HG7 T1): bands k6@2048, k2@30, k6@27 (STO reference tables); declared ladder ends at 27 where the k6 band is chosen but does not shrink (exact width 27)"

The negation method is the default (`.oneQubit`); the policy states no override.
-/

namespace PolicySubmission.Policies.ThresholdDeclaredPp

open Shor Operations

/-- Table 0: k = 6, 11 points, 75 operations. -/
abbrev t0K : ℕ := 6

def t0Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1, Point.int (-1), Point.int 2, Point.int (-2), Point.int 4, Point.int (-4), Point.int 8, Point.int (-8), Point.int 16]

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
  , valid_ops.addScaled 1 2 true 0
  , valid_ops.shiftR 1 4
  , valid_ops.addScaled 2 4 true 12
  , valid_ops.addScaled 2 0 true 0
  , valid_ops.addScaled 2 1 false 3
  , valid_ops.shiftR 2 6
  , valid_ops.addScaled 1 5 true 12
  , valid_ops.addScaled 1 3 true 6
  , valid_ops.addScaled 0 1 false 4
  , valid_ops.addScaled 0 2 false 8
  , valid_ops.addScaled 0 3 false 12
  , valid_ops.addScaled 0 4 false 16
  , valid_ops.addScaled 0 5 false 20
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 5 true 20
  , valid_ops.addScaled 0 4 true 16
  , valid_ops.addScaled 0 3 true 12
  , valid_ops.addScaled 0 2 true 8
  , valid_ops.addScaled 0 1 true 4 ]

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

/-- Table 1: k = 2, 3 points, 5 operations. -/
abbrev t1K : ℕ := 2

def t1Pts : List Point :=
  [Point.int 0, Point.frac 0, Point.int 1]

def t1Ops : Prog t1K :=
  [ valid_ops.phaseProduct 0
  , valid_ops.phaseProduct 1
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0 ]

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

/-- The policy: bands widest first (threshold, table), thresholds strictly decreasing. -/
def policy : ShorPolicySubmission where
  bands := [(2048, t0), (30, t1), (27, t0)]
  sorted := by decide

/-- Every band's table passes C1-C4 (the fields of the submission record). -/
theorem admissible : policy.policy.Admissible := policy.policy_admissible

/-- The target width the threshold rule is checked from. -/
def target : ℕ := 2048

/-- The ladder of working widths this policy file declares. -/
def declared : List (ℕ × Option ℕ) := [(2048, some 6), (364, some 2), (184, some 2), (94, some 2), (49, some 2), (27, none)]

/-- Threshold rule at exact widths (the benchmark's acceptance mode). -/
theorem chain_exact : chainContracts .exact policy.policy target = true := by decide +kernel

/-- Threshold rule at the scan widths. -/
theorem chain_scan : chainContracts .scan policy.policy target = true := by decide +kernel

/-- The declared ladder never under-declares the exact working width. -/
theorem decl_exact : declOK .exact policy.policy declared = true := by decide +kernel

/-- The declared ladder obeys the threshold rule. -/
theorem decl_threshold : declThresholdOK policy.policy declared = false := by decide +kernel

/-- **Verdict** at exact widths: all of the above (derived from them). -/
theorem accepted_exact : accepts .exact policy.policy target (some declared) = false := by
  simp [accepts, chain_exact, decl_exact, decl_threshold]

/-- The exact-width recursion ladder from the target. -/
theorem ladder_exact : ladder .exact policy.policy target = [(2048, some 6), (364, some 2), (184, some 2), (94, some 2), (49, some 2), (26, none)] := by
  decide +kernel

end PolicySubmission.Policies.ThresholdDeclaredPp

open Shor.Audit

#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.t0Hpts
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.t1Hpts
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.admissible
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.chain_exact
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.chain_scan
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.decl_exact
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.decl_threshold
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.accepted_exact
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.ladder_exact
#assert_axioms _root_.PolicySubmission.Policies.ThresholdDeclaredPp.policy
