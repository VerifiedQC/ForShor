import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Submission.Policies.BoardPP.Row6f7d25984ff8K8

/-!
# Qubit count: kernel-evaluated peaks of board row `6f7d25984ff8` (forshor_sub2), width rule `scan`

The 2048-bit reference circuit lowered by `PolicySubmission.Policies.BoardPP.Row6f7d25984ff8K8.policy` (a PhaseProduct policy of the public results board, deltas 1e-2, 3e-4; board ladder `2048:8 -> 279:4 -> 76:3 -> 29:leaf`)
under the width rule `scan` and each negation method (`oneQubit`, `scratch`): the peak qubit count is `xW + 8795 + N`, `xW` the exponent width (4095 or 4096), for

* the plain circuit (`ReferencePeakIs`, `N` = `Policy.orderFindingPeak`),
* the balanced circuit with the default rule (`ReferenceBalancedPeakIs`; no hypothesis on the allocator's capacities, `reference2048PeakBalanced_policyU`), and
* the circuit with every site split (`ReferenceBalancedUPeakIs`, the same circuit at the reference layout).

The eight budgets are closed by one `decide +kernel` (`numerals_scan`) and re-checked by the compiled interpreter (`#guard`).
-/

namespace Shor
namespace QubitCount
namespace PolicyNumeralsBoard
namespace Row6f7d25984ff8K8

/-- The policy under the width rule `r` and the negation method `m`. -/
abbrev under (r : WidthRule) (m : NegationMethod) : ShorLoweringPolicy :=
  (PolicySubmission.Policies.BoardPP.Row6f7d25984ff8K8.policy.policy.withRule r).withNegation m

theorem under_admissible (r : WidthRule) (m : NegationMethod) : (under r m).Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.BoardPP.Row6f7d25984ff8K8.admissible r) m

/-- The policy as submitted is `under .scan .oneQubit`. -/
theorem under_scan_oneQubit : under .scan .oneQubit = PolicySubmission.Policies.BoardPP.Row6f7d25984ff8K8.policy.policy :=
  rfl

theorem numerals_scan :
    Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 = 35484 ∧
    Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 = 35484 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 = 35484 ∧
    Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 = 35484 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 = 2772 ∧
    Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 = 2772 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 = 4400 ∧
    Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 = 4400 := by
  decide +kernel

-- the same eight numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4096 2048 2347 4398 == 35484
#guard Policy.orderFindingPeak (under .scan .oneQubit) 4095 2048 2347 4398 == 35484
#guard Policy.orderFindingPeak (under .scan .scratch) 4096 2048 2347 4398 == 35484
#guard Policy.orderFindingPeak (under .scan .scratch) 4095 2048 2347 4398 == 35484
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 == 2772
#guard Policy.orderFindingPeakU (under .scan .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 == 2772
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4096 2048 2347 4398 == 4400
#guard Policy.orderFindingPeakU (under .scan .scratch) Balanced.defaultRule 4095 2048 2347 4398 == 4400

/-- `scan` rule, `oneQubit` negation: the plain reference circuit peaks at `xW + 8795 + 35484`. -/
theorem plain_scan_oneQubit : ReferencePeakIs (under .scan .oneQubit) 35484 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.1 numerals_scan.2.1

/-- `scan` rule, `oneQubit` negation: the balanced reference circuit peaks at `xW + 8795 + 2772`. -/
theorem balanced_scan_oneQubit : ReferenceBalancedPeakIs (under .scan .oneQubit) 2772 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.1 numerals_scan.2.2.2.2.2.1

/-- `scan` rule, `oneQubit` negation: the every-site-split reference circuit peaks at `xW + 8795 + 2772`. -/
theorem balancedU_scan_oneQubit : ReferenceBalancedUPeakIs (under .scan .oneQubit) 2772 :=
  referenceBalancedUPeakIs_of _ balanced_scan_oneQubit

/-- `scan` rule, `scratch` negation: the plain reference circuit peaks at `xW + 8795 + 35484`. -/
theorem plain_scan_scratch : ReferencePeakIs (under .scan .scratch) 35484 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_scan.2.2.1 numerals_scan.2.2.2.1

/-- `scan` rule, `scratch` negation: the balanced reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balanced_scan_scratch : ReferenceBalancedPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_scan.2.2.2.2.2.2.1 numerals_scan.2.2.2.2.2.2.2

/-- `scan` rule, `scratch` negation: the every-site-split reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balancedU_scan_scratch : ReferenceBalancedUPeakIs (under .scan .scratch) 4400 :=
  referenceBalancedUPeakIs_of _ balanced_scan_scratch

#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Row6f7d25984ff8K8.plain_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Row6f7d25984ff8K8.balanced_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Row6f7d25984ff8K8.balancedU_scan_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Row6f7d25984ff8K8.plain_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Row6f7d25984ff8K8.balanced_scan_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Row6f7d25984ff8K8.balancedU_scan_scratch

end Row6f7d25984ff8K8
end PolicyNumeralsBoard
end QubitCount
end Shor
