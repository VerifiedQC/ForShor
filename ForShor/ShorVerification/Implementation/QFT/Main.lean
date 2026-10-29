import ForShor.ShorVerification.Implementation.QFT.Statement
import ForShor.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness

/-!
# QFT Main Theorem

This module proves the public assertion for the QFT implementation.
-/

namespace Shor
open Gate
open Operations

/-- QFT lowering theorem with a table -/
theorem lowerQFT_correct
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (r : ExtReg) :
    LowerQFTCorrect qs k hk ops r := by
  intro ψ pts hpts hworkspace hInterp hC hRun
  exact evalL_lowerQFT (qs := qs) (k := k) (hk := hk) (ops := ops) (r := r) (ψ := ψ)
    (pts := pts) (hpts := hpts) hworkspace hInterp hC hRun

/-- Main QFT lowering theorem under a policy. -/
theorem Policy.lowerQFT_correct
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (r : ExtReg) :
    Policy.LowerQFTCorrect qs P r := by
  intro ψ hworkspace hP
  exact Policy.evalL_lowerQFT qs P hP r ψ hworkspace

end Shor
