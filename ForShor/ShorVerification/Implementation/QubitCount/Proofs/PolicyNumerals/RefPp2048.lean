import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Submission.Policies.RefPp2048

/-!
# Qubit count: kernel-evaluated peaks of `policies/ref_pp_2048.json`, width rule `scan`

The 2048-bit reference circuit lowered by the policy `PolicySubmission.Policies.RefPp2048.policy` under
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
namespace RefPp2048

/-- The policy under the width rule `r` and the negation method `m`. -/
abbrev under (r : WidthRule) (m : NegationMethod) : ShorLoweringPolicy :=
  (PolicySubmission.Policies.RefPp2048.policy.policy.withRule r).withNegation m

theorem under_admissible (r : WidthRule) (m : NegationMethod) : (under r m).Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.RefPp2048.admissible r) m

/-- The policy as submitted is `under .scan .oneQubit`. -/
theorem under_scan_oneQubit : under .scan .oneQubit = PolicySubmission.Policies.RefPp2048.policy.policy :=
  rfl

theorem numerals_scan :
    Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 = 23724 ∧
    Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 = 23724 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 = 23724 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 = 23724 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 = 936 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 = 936 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 = 4400 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 = 4400 := by
  decide +kernel

-- the same eight numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 == 23724
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 == 23724
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 == 936
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 == 936
#guard Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 == 23724
#guard Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 == 23724
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 == 4400
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 == 4400

/-- `scan` rule, `oneQubit` negation: the plain reference circuit peaks at `xW + 8795 + 23724`. -/
theorem plain_scan_oneQubit : ReferencePeakIs (under .scan .oneQubit) 23724 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.1 numerals_scan.2.1

/-- `scan` rule, `oneQubit` negation: the balanced reference circuit peaks at `xW + 8795 + 936`. -/
theorem balanced_scan_oneQubit : ReferenceBalancedPeakIs (under .scan .oneQubit) 936 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.1 numerals_scan.2.2.2.2.2.1

/-- `scan` rule, `oneQubit` negation: the every-site-split reference circuit peaks at `xW + 8795 + 936`. -/
theorem balancedU_scan_oneQubit : ReferenceBalancedUPeakIs (under .scan .oneQubit) 936 :=
  referenceBalancedUPeakIs_of _ balanced_scan_oneQubit

/-- `scan` rule, `scratch` negation: the plain reference circuit peaks at `xW + 8795 + 23724`. -/
theorem plain_scan_scratch : ReferencePeakIs (under .scan .scratch) 23724 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.2.2.1 numerals_scan.2.2.2.1

/-- `scan` rule, `scratch` negation: the balanced reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balanced_scan_scratch : ReferenceBalancedPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.2.2.1 numerals_scan.2.2.2.2.2.2.2

/-- `scan` rule, `scratch` negation: the every-site-split reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balancedU_scan_scratch : ReferenceBalancedUPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedUPeakIs_of _ balanced_scan_scratch

#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.RefPp2048.plain_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.RefPp2048.balanced_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.RefPp2048.balancedU_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.RefPp2048.plain_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.RefPp2048.balanced_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.RefPp2048.balancedU_scan_scratch

end RefPp2048
end PolicyNumerals
end QubitCount
end Shor
