import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Submission.Policies.ThresholdDeclaredPp

/-!
# Qubit count: kernel-evaluated peaks of `policies/threshold_declared_pp.json`, width rule `scan`

The 2048-bit reference circuit lowered by the policy `PolicySubmission.Policies.ThresholdDeclaredPp.policy` under
the width rule `scan` (the policy's own width-rule field, the default) and each negation method (`oneQubit`, `scratch`): the peak qubit
count is `xW + 8795 + N`, `xW` the exponent width (4095 or 4096), for

* the plain circuit (`ReferencePeakIs`, `N` = `Policy.orderFindingPeak`),
* the balanced circuit with the default rule (`ReferenceBalancedPeakIs`), whose budget needs no
  hypothesis on the allocator's capacities (`reference2048PeakBalanced_policyU`), and
* the circuit with every site split (`ReferenceBalancedUPeakIs`, the same circuit at the reference
  layout).

The eight budgets are closed by one `decide +kernel` (`numerals_scan`, so the kernel shares the width
recursion) and re-checked by the compiled interpreter (`#guard`). The policy's admissibility is
automatic (`admissible`); whether the *benchmark* accepts it is the separate threshold rule in
`Submission/Policies/`.
-/

namespace Shor
namespace QubitCount
namespace PolicyNumerals
namespace ThresholdDeclaredPp

/-- The policy under the width rule `r` and the negation method `m`. -/
abbrev under (r : WidthRule) (m : NegationMethod) : ShorLoweringPolicy :=
  (PolicySubmission.Policies.ThresholdDeclaredPp.policy.policy.withRule r).withNegation m

theorem under_admissible (r : WidthRule) (m : NegationMethod) : (under r m).Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.ThresholdDeclaredPp.admissible r) m

/-- The policy as submitted is `under .scan .oneQubit`. -/
theorem under_scan_oneQubit : under .scan .oneQubit = PolicySubmission.Policies.ThresholdDeclaredPp.policy.policy :=
  rfl

theorem numerals_scan :
    Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 = 23678 ∧
    Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 = 23678 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 = 23678 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 = 23678 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 = 892 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 = 892 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 = 4400 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 = 4400 := by
  decide +kernel

-- the same eight numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 == 23678
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 == 23678
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 == 892
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 == 892
#guard Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 == 23678
#guard Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 == 23678
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 == 4400
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 == 4400

/-- `scan` rule, `oneQubit` negation: the plain reference circuit peaks at `xW + 8795 + 23678`. -/
theorem plain_scan_oneQubit : ReferencePeakIs (under .scan .oneQubit) 23678 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.1 numerals_scan.2.1

/-- `scan` rule, `oneQubit` negation: the balanced reference circuit peaks at `xW + 8795 + 892`. -/
theorem balanced_scan_oneQubit : ReferenceBalancedPeakIs (under .scan .oneQubit) 892 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.1 numerals_scan.2.2.2.2.2.1

/-- `scan` rule, `oneQubit` negation: the every-site-split reference circuit peaks at `xW + 8795 + 892`. -/
theorem balancedU_scan_oneQubit : ReferenceBalancedUPeakIs (under .scan .oneQubit) 892 :=
  referenceBalancedUPeakIs_of _ balanced_scan_oneQubit

/-- `scan` rule, `scratch` negation: the plain reference circuit peaks at `xW + 8795 + 23678`. -/
theorem plain_scan_scratch : ReferencePeakIs (under .scan .scratch) 23678 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.2.2.1 numerals_scan.2.2.2.1

/-- `scan` rule, `scratch` negation: the balanced reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balanced_scan_scratch : ReferenceBalancedPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.2.2.1 numerals_scan.2.2.2.2.2.2.2

/-- `scan` rule, `scratch` negation: the every-site-split reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balancedU_scan_scratch : ReferenceBalancedUPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedUPeakIs_of _ balanced_scan_scratch

#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.ThresholdDeclaredPp.plain_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.ThresholdDeclaredPp.balanced_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.ThresholdDeclaredPp.balancedU_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.ThresholdDeclaredPp.plain_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.ThresholdDeclaredPp.balanced_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.ThresholdDeclaredPp.balancedU_scan_scratch

end ThresholdDeclaredPp
end PolicyNumerals
end QubitCount
end Shor
