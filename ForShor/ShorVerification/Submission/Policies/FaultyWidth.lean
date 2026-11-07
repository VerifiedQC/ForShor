import ForShor.ShorVerification.Submission.Policies.Common

/-!
# `policies/faulty_width.json` as a `ShorPolicySubmission`

Generated from the sister repository's policy JSON by a script that is not part of this repository. Source: "width fault: accepted k=2 table (points 0,1,inf) whose declared ladder under-declares the working width at n=20 (11 < scanned 13)"

The negation method is the default (`.oneQubit`); the policy states no override.
-/

namespace PolicySubmission.Policies.FaultyWidth

open Shor Operations

/-- Table 0: k = 2, 3 points, 5 operations. -/
abbrev t0K : ℕ := 2

def t0Pts : List Point :=
  [Point.int 0, Point.int 1, Point.frac 0]

def t0Ops : Prog t0K :=
  [ valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 false 0
  , valid_ops.phaseProduct 0
  , valid_ops.addScaled 0 1 true 0
  , valid_ops.phaseProduct 1 ]

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

/-- The policy: bands widest first (threshold, table), thresholds strictly decreasing. -/
def policy : ShorPolicySubmission where
  bands := [(20, t0)]
  sorted := by decide

/-- Every band's table passes C1-C4 (the fields of the submission record). -/
theorem admissible : policy.policy.Admissible := policy.policy_admissible

/-- The target width the threshold rule is checked from. -/
def target : ℕ := 20

/-- The ladder of working widths this policy file declares. -/
def declared : List (ℕ × Option ℕ) := [(20, some 2), (11, none)]

/-- Threshold rule at exact widths (the benchmark's acceptance mode). -/
theorem chain_exact : chainContracts .exact policy.policy target = true := by decide +kernel

/-- Threshold rule at the scan widths. -/
theorem chain_scan : chainContracts .scan policy.policy target = true := by decide +kernel

/-- The declared ladder never under-declares the exact working width. -/
theorem decl_exact : declOK .exact policy.policy declared = false := by decide +kernel

/-- The declared ladder obeys the threshold rule. -/
theorem decl_threshold : declThresholdOK policy.policy declared = true := by decide +kernel

/-- **Verdict** at exact widths: all of the above (derived from them). -/
theorem accepted_exact : accepts .exact policy.policy target (some declared) = false := by
  simp [accepts, chain_exact, decl_exact, decl_threshold]

/-- The exact-width recursion ladder from the target. -/
theorem ladder_exact : ladder .exact policy.policy target = [(20, some 2), (12, none)] := by
  decide +kernel

/-- The scan-width recursion ladder from the target. -/
theorem ladder_scan : ladder .scan policy.policy target = [(20, some 2), (13, none)] := by
  decide +kernel

end PolicySubmission.Policies.FaultyWidth

open Shor.Audit

#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.t0Hpts
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.admissible
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.chain_exact
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.chain_scan
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.decl_exact
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.decl_threshold
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.accepted_exact
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.ladder_exact
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.ladder_scan
#assert_axioms _root_.PolicySubmission.Policies.FaultyWidth.policy
