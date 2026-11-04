import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Balanced
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Arith

/-!
# Qubit count: the formulas

The claims of `Statement.lean` from the walk's formulas (`OrderFinding.lean`,
`Balanced.lean`) and the budget equalities of `Arith.lean`.
-/

namespace Shor
namespace QubitCount

theorem orderFindingPeakFormula (P : ShorLoweringPolicy) : Policy.OrderFindingPeakFormula P := by
  intro hP a N x y work scratch flag hmod hstep4 hws hlay
  rw [Policy.orderFindingQubits, orderFindingPeak_eq]
  exact orderFindingPeakFormulaRec P hP a N x y work scratch flag hmod hstep4 hws hlay

theorem referencePeakFormula (P : ShorLoweringPolicy) : Policy.ReferencePeakFormula P := by
  intro hP inst m
  have h := referencePeakFormulaRec P hP inst m
  dsimp only at h ⊢
  rw [Policy.orderFindingQubits, orderFindingPeak_eq]
  exact h

theorem orderFindingPeakFormulaBalanced (P : ShorLoweringPolicy) (R : Balanced.Rule) :
    Policy.OrderFindingPeakFormulaBalanced P R := by
  intro hP a N x y work scratch flag hmod hstep4 hws hlay
  rw [Policy.orderFindingQubitsBalanced, orderFindingPeakBalanced_eq]
  exact orderFindingPeakFormulaBalancedRec P R hP a N x y work scratch flag hmod hstep4 hws hlay

end QubitCount
end Shor
