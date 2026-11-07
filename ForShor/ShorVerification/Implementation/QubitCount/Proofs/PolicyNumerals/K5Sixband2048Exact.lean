import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Submission.Policies.K5Sixband2048

/-!
# Qubit count: kernel-evaluated peaks of `policies/k5_sixband_2048.json`, width rule `exact`

The 2048-bit reference circuit lowered by the policy `PolicySubmission.Policies.K5Sixband2048.policy` under
the width rule `exact` (the benchmark mode of the sister repositories' `JMC_VALIDATION.md`) and each negation method (`oneQubit`, `scratch`): the peak qubit
count is `xW + 8795 + N`, `xW` the exponent width (4095 or 4096), for

* the plain circuit (`ReferencePeakIs`, `N` = `Policy.orderFindingPeak`),
* the balanced circuit with the default rule (`ReferenceBalancedPeakIs`), whose budget needs no
  hypothesis on the allocator's capacities (`reference2048PeakBalanced_policyU`), and
* the circuit with every site split (`ReferenceBalancedUPeakIs`, the same circuit at the reference
  layout).

The eight budgets are closed by one `decide +kernel` (`numerals_exact`, so the kernel shares the width
recursion) and re-checked by the compiled interpreter (`#guard`). The policy's admissibility is
automatic (`admissible`); whether the *benchmark* accepts it is the separate threshold rule in
`Submission/Policies/`.
-/

namespace Shor
namespace QubitCount
namespace PolicyNumerals
namespace K5Sixband2048Exact

/-- The policy under the width rule `r` and the negation method `m`. -/
abbrev under (r : WidthRule) (m : NegationMethod) : ShorLoweringPolicy :=
  (PolicySubmission.Policies.K5Sixband2048.policy.policy.withRule r).withNegation m

theorem under_admissible (r : WidthRule) (m : NegationMethod) : (under r m).Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.K5Sixband2048.admissible r) m

theorem numerals_exact :
    Policy.orderFindingPeak (under .exact .oneQubit) 4096 2048 2347 4398 = 18854 ∧
    Policy.orderFindingPeak (under .exact .oneQubit) 4095 2048 2347 4398 = 18854 ∧
    Policy.orderFindingPeak (under .exact .scratch) 4096 2048 2347 4398 = 18854 ∧
    Policy.orderFindingPeak (under .exact .scratch) 4095 2048 2347 4398 = 18854 ∧
    Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 = 554 ∧
    Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 = 554 ∧
    Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4096 2048 2347 4398 = 4400 ∧
    Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4095 2048 2347 4398 = 4400 := by
  decide +kernel

-- the same eight numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeak (under .exact .oneQubit) 4096 2048 2347 4398 == 18854
#guard Policy.orderFindingPeak (under .exact .oneQubit) 4095 2048 2347 4398 == 18854
#guard Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 == 554
#guard Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 == 554
#guard Policy.orderFindingPeak (under .exact .scratch) 4096 2048 2347 4398 == 18854
#guard Policy.orderFindingPeak (under .exact .scratch) 4095 2048 2347 4398 == 18854
#guard Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4096 2048 2347 4398 == 4400
#guard Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4095 2048 2347 4398 == 4400

/-- `exact` rule, `oneQubit` negation: the plain reference circuit peaks at `xW + 8795 + 18854`. -/
theorem plain_exact_oneQubit : ReferencePeakIs (under .exact .oneQubit) 18854 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_exact.1 numerals_exact.2.1

/-- `exact` rule, `oneQubit` negation: the balanced reference circuit peaks at `xW + 8795 + 554`. -/
theorem balanced_exact_oneQubit : ReferenceBalancedPeakIs (under .exact .oneQubit) 554 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_exact.2.2.2.2.1 numerals_exact.2.2.2.2.2.1

/-- `exact` rule, `oneQubit` negation: the every-site-split reference circuit peaks at `xW + 8795 + 554`. -/
theorem balancedU_exact_oneQubit : ReferenceBalancedUPeakIs (under .exact .oneQubit) 554 :=
  referenceBalancedUPeakIs_of _ balanced_exact_oneQubit

/-- `exact` rule, `scratch` negation: the plain reference circuit peaks at `xW + 8795 + 18854`. -/
theorem plain_exact_scratch : ReferencePeakIs (under .exact .scratch) 18854 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_exact.2.2.1 numerals_exact.2.2.2.1

/-- `exact` rule, `scratch` negation: the balanced reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balanced_exact_scratch : ReferenceBalancedPeakIs (under .exact .scratch) 4400 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_exact.2.2.2.2.2.2.1 numerals_exact.2.2.2.2.2.2.2

/-- `exact` rule, `scratch` negation: the every-site-split reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balancedU_exact_scratch : ReferenceBalancedUPeakIs (under .exact .scratch) 4400 :=
  referenceBalancedUPeakIs_of _ balanced_exact_scratch

#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.K5Sixband2048Exact.plain_exact_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.K5Sixband2048Exact.balanced_exact_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.K5Sixband2048Exact.balancedU_exact_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.K5Sixband2048Exact.plain_exact_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.K5Sixband2048Exact.balanced_exact_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumerals.K5Sixband2048Exact.balancedU_exact_scratch

end K5Sixband2048Exact
end PolicyNumerals
end QubitCount
end Shor
