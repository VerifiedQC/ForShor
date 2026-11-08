import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Submission.Policies.BoardPP.Rowc7f81cb40081

/-!
# Qubit count: kernel-evaluated peaks of board row `c7f81cb40081` (forshor_sub26), width rule `scan`

The 2048-bit reference circuit lowered by `PolicySubmission.Policies.BoardPP.Rowc7f81cb40081.policy` (a PhaseProduct policy of the public results board, deltas 1e-2, 3e-4, 1e-4, 1e-6; board ladder `2048:6 -> 354:6 -> 71:leaf`)
under the width rule `scan` and each negation method (`oneQubit`, `scratch`): the peak qubit count is `xW + 8795 + N`, `xW` the exponent width (4095 or 4096), for

* the plain circuit (`ReferencePeakIs`, `N` = `Policy.orderFindingPeak`),
* the balanced circuit with the default rule (`ReferenceBalancedPeakIs`; no hypothesis on the allocator's capacities, `reference2048PeakBalanced_policyU`), and
* the circuit with every site split (`ReferenceBalancedUPeakIs`, the same circuit at the reference layout).

The eight budgets are closed by one `decide +kernel` (`numerals_scan`) and re-checked by the compiled interpreter (`#guard`).
-/

namespace Shor
namespace QubitCount
namespace PolicyNumeralsBoard
namespace Rowc7f81cb40081

/-- The policy under the width rule `r` and the negation method `m`. -/
abbrev under (r : WidthRule) (m : NegationMethod) : ShorLoweringPolicy :=
  (PolicySubmission.Policies.BoardPP.Rowc7f81cb40081.policy.policy.withRule r).withNegation m

theorem under_admissible (r : WidthRule) (m : NegationMethod) : (under r m).Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.BoardPP.Rowc7f81cb40081.admissible r) m

/-- The policy as submitted is `under .scan .oneQubit`. -/
theorem under_scan_oneQubit : under .scan .oneQubit = PolicySubmission.Policies.BoardPP.Rowc7f81cb40081.policy.policy :=
  rfl

theorem numerals_scan :
    Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 = 23590 ∧
    Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 = 23590 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 = 23590 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 = 23590 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 = 996 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 = 996 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 = 4400 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 = 4400 := by
  decide +kernel

-- the same eight numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 == 23590
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 == 23590
#guard Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 == 23590
#guard Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 == 23590
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 == 996
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 == 996
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 == 4400
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 == 4400

/-- `scan` rule, `oneQubit` negation: the plain reference circuit peaks at `xW + 8795 + 23590`. -/
theorem plain_scan_oneQubit : ReferencePeakIs (under .scan .oneQubit) 23590 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.1 numerals_scan.2.1

/-- `scan` rule, `oneQubit` negation: the balanced reference circuit peaks at `xW + 8795 + 996`. -/
theorem balanced_scan_oneQubit : ReferenceBalancedPeakIs (under .scan .oneQubit) 996 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.1 numerals_scan.2.2.2.2.2.1

/-- `scan` rule, `oneQubit` negation: the every-site-split reference circuit peaks at `xW + 8795 + 996`. -/
theorem balancedU_scan_oneQubit : ReferenceBalancedUPeakIs (under .scan .oneQubit) 996 :=
  referenceBalancedUPeakIs_of _ balanced_scan_oneQubit

/-- `scan` rule, `scratch` negation: the plain reference circuit peaks at `xW + 8795 + 23590`. -/
theorem plain_scan_scratch : ReferencePeakIs (under .scan .scratch) 23590 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.2.2.1 numerals_scan.2.2.2.1

/-- `scan` rule, `scratch` negation: the balanced reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balanced_scan_scratch : ReferenceBalancedPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.2.2.1 numerals_scan.2.2.2.2.2.2.2

/-- `scan` rule, `scratch` negation: the every-site-split reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balancedU_scan_scratch : ReferenceBalancedUPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedUPeakIs_of _ balanced_scan_scratch

#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowc7f81cb40081.plain_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowc7f81cb40081.balanced_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowc7f81cb40081.balancedU_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowc7f81cb40081.plain_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowc7f81cb40081.balanced_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowc7f81cb40081.balancedU_scan_scratch

end Rowc7f81cb40081
end PolicyNumeralsBoard
end QubitCount
end Shor
