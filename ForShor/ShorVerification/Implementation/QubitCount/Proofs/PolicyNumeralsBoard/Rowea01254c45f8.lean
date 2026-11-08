import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Submission.Policies.BoardPP.Rowea01254c45f8

/-!
# Qubit count: kernel-evaluated peaks of board row `ea01254c45f8` (forshor_sub23), width rule `scan`

The 2048-bit reference circuit lowered by `PolicySubmission.Policies.BoardPP.Rowea01254c45f8.policy` (a PhaseProduct policy of the public results board, deltas 1e-2, 3e-4, 1e-4, 1e-6; board ladder `2048:3 -> 687:3 -> 232:3 -> 81:3 -> 30:leaf`)
under the width rule `scan` and each negation method (`oneQubit`, `scratch`): the peak qubit count is `xW + 8795 + N`, `xW` the exponent width (4095 or 4096), for

* the plain circuit (`ReferencePeakIs`, `N` = `Policy.orderFindingPeak`),
* the balanced circuit with the default rule (`ReferenceBalancedPeakIs`; no hypothesis on the allocator's capacities, `reference2048PeakBalanced_policyU`), and
* the circuit with every site split (`ReferenceBalancedUPeakIs`, the same circuit at the reference layout).

The eight budgets are closed by one `decide +kernel` (`numerals_scan`) and re-checked by the compiled interpreter (`#guard`).
-/

namespace Shor
namespace QubitCount
namespace PolicyNumeralsBoard
namespace Rowea01254c45f8

/-- The policy under the width rule `r` and the negation method `m`. -/
abbrev under (r : WidthRule) (m : NegationMethod) : ShorLoweringPolicy :=
  (PolicySubmission.Policies.BoardPP.Rowea01254c45f8.policy.policy.withRule r).withNegation m

theorem under_admissible (r : WidthRule) (m : NegationMethod) : (under r m).Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.BoardPP.Rowea01254c45f8.admissible r) m

/-- The policy as submitted is `under .scan .oneQubit`. -/
theorem under_scan_oneQubit : under .scan .oneQubit = PolicySubmission.Policies.BoardPP.Rowea01254c45f8.policy.policy :=
  rfl

theorem numerals_scan :
    Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 = 10586 ∧
    Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 = 10586 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 = 10586 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 = 10586 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 = 568 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 = 568 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 = 4400 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 = 4400 := by
  decide +kernel

-- the same eight numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 == 10586
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 == 10586
#guard Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 == 10586
#guard Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 == 10586
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 == 568
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 == 568
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 == 4400
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 == 4400

/-- `scan` rule, `oneQubit` negation: the plain reference circuit peaks at `xW + 8795 + 10586`. -/
theorem plain_scan_oneQubit : ReferencePeakIs (under .scan .oneQubit) 10586 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.1 numerals_scan.2.1

/-- `scan` rule, `oneQubit` negation: the balanced reference circuit peaks at `xW + 8795 + 568`. -/
theorem balanced_scan_oneQubit : ReferenceBalancedPeakIs (under .scan .oneQubit) 568 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.1 numerals_scan.2.2.2.2.2.1

/-- `scan` rule, `oneQubit` negation: the every-site-split reference circuit peaks at `xW + 8795 + 568`. -/
theorem balancedU_scan_oneQubit : ReferenceBalancedUPeakIs (under .scan .oneQubit) 568 :=
  referenceBalancedUPeakIs_of _ balanced_scan_oneQubit

/-- `scan` rule, `scratch` negation: the plain reference circuit peaks at `xW + 8795 + 10586`. -/
theorem plain_scan_scratch : ReferencePeakIs (under .scan .scratch) 10586 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.2.2.1 numerals_scan.2.2.2.1

/-- `scan` rule, `scratch` negation: the balanced reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balanced_scan_scratch : ReferenceBalancedPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.2.2.1 numerals_scan.2.2.2.2.2.2.2

/-- `scan` rule, `scratch` negation: the every-site-split reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balancedU_scan_scratch : ReferenceBalancedUPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedUPeakIs_of _ balanced_scan_scratch

#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowea01254c45f8.plain_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowea01254c45f8.balanced_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowea01254c45f8.balancedU_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowea01254c45f8.plain_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowea01254c45f8.balanced_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowea01254c45f8.balancedU_scan_scratch

end Rowea01254c45f8
end PolicyNumeralsBoard
end QubitCount
end Shor
