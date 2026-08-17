import FastMultiplication.ShorVerification.Implementation.Shor.Assertions

/-!
# Naive Shor Correctness

This file isolates the ideal, non-lowered Shor order-finding theorem.  The
approximate and lowered correctness proofs import this result as the ideal
success-probability bound they transfer from.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [ContinuedFractionPost]
variable [Spec]

/-! =========================================================
    Ideal Order-Finding Correctness
========================================================= -/

/-- Ideal order-finding success probability for Shor's algorithm.

This is the top-level quantum lower bound: starting from a clean
computational-basis input, the ideal order-finding circuit recovers the order
with at least the standard inverse-polylogarithmic probability. -/
theorem Shor_correct
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs]
    (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance)
    (x y : ExtReg)
    (b0 : qs.Basis)
    (hm : regSize x.active = Nat.log2 (2 * inst.N^2))
    (hn : regSize y.active = Nat.log2 (2 * inst.N))
    (hinput : IdealOrderFindingInput qs x y b0) :
    ShorCorrect T hT inst x y b0 hm hn hinput := by
  sorry

end Shor
