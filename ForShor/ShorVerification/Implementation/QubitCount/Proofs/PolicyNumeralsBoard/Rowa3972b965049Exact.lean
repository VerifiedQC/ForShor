import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Submission.Policies.BoardPP.Rowa3972b965049
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsBoard.Row7df40770c0b6Exact

/-!
# Qubit count: kernel-evaluated peaks of board row `a3972b965049` (forshor_sub25), width rule `exact`

The 2048-bit reference circuit lowered by `PolicySubmission.Policies.BoardPP.Rowa3972b965049.policy` (a PhaseProduct policy of the public results board, deltas 1e-2, 3e-4, 1e-4, 1e-6; board ladder `2048:5 -> 421:5 -> 94:leaf`)
under the width rule `exact` (the board's own rule) and each negation method (`oneQubit`, `scratch`): the peak qubit count is `xW + 8795 + N`, `xW` the exponent width (4095 or 4096), for

* the plain circuit (`ReferencePeakIs`, `N` = `Policy.orderFindingPeak`),
* the balanced circuit with the default rule (`ReferenceBalancedPeakIs`; no hypothesis on the allocator's capacities, `reference2048PeakBalanced_policyU`), and
* the circuit with every site split (`ReferenceBalancedUPeakIs`, the same circuit at the reference layout).

The eight budgets are closed by one `decide +kernel` (`numerals_exact`) and re-checked by the compiled interpreter (`#guard`).

Comparison with the board (a report, not a theorem): the full order-finding row prints Q = 13404 = 12,890 + 514; the balanced `oneQubit` `N` below is 514, so the Lean count at 4095 exponent qubits (`4095 + 8795 + 514 = 13404`, base registers 12,890) is equal to the board's Q.
-/

namespace Shor
namespace QubitCount
namespace PolicyNumeralsBoard
namespace Rowa3972b965049Exact

/-- The policy under the width rule `r` and the negation method `m`. -/
abbrev under (r : WidthRule) (m : NegationMethod) : ShorLoweringPolicy :=
  (PolicySubmission.Policies.BoardPP.Rowa3972b965049.policy.policy.withRule r).withNegation m

theorem under_admissible (r : WidthRule) (m : NegationMethod) : (under r m).Admissible :=
  ShorLoweringPolicy.withNegation_admissible
    (ShorLoweringPolicy.withRule_admissible PolicySubmission.Policies.BoardPP.Rowa3972b965049.admissible r) m

theorem numerals_exact :
    Policy.orderFindingPeak (under .exact .oneQubit) 4096 2048 2347 4398 = 18788 ∧
    Policy.orderFindingPeak (under .exact .oneQubit) 4095 2048 2347 4398 = 18788 ∧
    Policy.orderFindingPeak (under .exact .scratch) 4096 2048 2347 4398 = 18788 ∧
    Policy.orderFindingPeak (under .exact .scratch) 4095 2048 2347 4398 = 18788 ∧
    Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 = 514 ∧
    Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 = 514 ∧
    Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4096 2048 2347 4398 = 4400 ∧
    Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4095 2048 2347 4398 = 4400 := by
  decide +kernel

-- the same eight numerals, by the compiled interpreter (independent of the kernel run above)
#guard Policy.orderFindingPeak (under .exact .oneQubit) 4096 2048 2347 4398 == 18788
#guard Policy.orderFindingPeak (under .exact .oneQubit) 4095 2048 2347 4398 == 18788
#guard Policy.orderFindingPeak (under .exact .scratch) 4096 2048 2347 4398 == 18788
#guard Policy.orderFindingPeak (under .exact .scratch) 4095 2048 2347 4398 == 18788
#guard Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4096 2048 2347 4398 == 514
#guard Policy.orderFindingPeakU (under .exact .oneQubit) Balanced.defaultRule 4095 2048 2347 4398 == 514
#guard Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4096 2048 2347 4398 == 4400
#guard Policy.orderFindingPeakU (under .exact .scratch) Balanced.defaultRule 4095 2048 2347 4398 == 4400

/-- `exact` rule, `oneQubit` negation: the plain reference circuit peaks at `xW + 8795 + 18788`. -/
theorem plain_exact_oneQubit : ReferencePeakIs (under .exact .oneQubit) 18788 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_exact.1 numerals_exact.2.1

/-- `exact` rule, `oneQubit` negation: the balanced reference circuit peaks at `xW + 8795 + 514`. -/
theorem balanced_exact_oneQubit : ReferenceBalancedPeakIs (under .exact .oneQubit) 514 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_exact.2.2.2.2.1 numerals_exact.2.2.2.2.2.1

/-- `exact` rule, `oneQubit` negation: the every-site-split reference circuit peaks at `xW + 8795 + 514`. -/
theorem balancedU_exact_oneQubit : ReferenceBalancedUPeakIs (under .exact .oneQubit) 514 :=
  referenceBalancedUPeakIs_of _ balanced_exact_oneQubit

/-- `exact` rule, `scratch` negation: the plain reference circuit peaks at `xW + 8795 + 18788`. -/
theorem plain_exact_scratch : ReferencePeakIs (under .exact .scratch) 18788 :=
  referencePeakIs_of _ (under_admissible _ _) numerals_exact.2.2.1 numerals_exact.2.2.2.1

/-- `exact` rule, `scratch` negation: the balanced reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balanced_exact_scratch : ReferenceBalancedPeakIs (under .exact .scratch) 4400 :=
  referenceBalancedPeakIs_of _ (under_admissible _ _) numerals_exact.2.2.2.2.2.2.1 numerals_exact.2.2.2.2.2.2.2

/-- `exact` rule, `scratch` negation: the every-site-split reference circuit peaks at `xW + 8795 + 4400`. -/
theorem balancedU_exact_scratch : ReferenceBalancedUPeakIs (under .exact .scratch) 4400 :=
  referenceBalancedUPeakIs_of _ balanced_exact_scratch

/-- Arithmetic only: `4095 + 8795 + 514` is the board's printed Q (13404) for this policy (the board's number is a Python formula, not a Lean claim; this records that the two agree). -/
theorem board_q_agrees : 4095 + 8795 + 514 = 13404 := by decide

#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowa3972b965049Exact.plain_exact_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowa3972b965049Exact.balanced_exact_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowa3972b965049Exact.balancedU_exact_oneQubit
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowa3972b965049Exact.plain_exact_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowa3972b965049Exact.balanced_exact_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowa3972b965049Exact.balancedU_exact_scratch
#assert_axioms _root_.Shor.QubitCount.PolicyNumeralsBoard.Rowa3972b965049Exact.board_q_agrees

end Rowa3972b965049Exact
end PolicyNumeralsBoard
end QubitCount
end Shor
