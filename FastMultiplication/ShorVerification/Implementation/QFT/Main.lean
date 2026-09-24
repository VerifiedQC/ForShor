import FastMultiplication.ShorVerification.Implementation.QFT.Spec.Assertions
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness

/-!
# QFT Main Theorem

This module proves the public assertion for the QFT implementation.  All
supporting lemmas are kept under `QFT` proof files (`Decomposition`,
`Lowering/*`).
-/

namespace Shor
open Gate
open Operations

/-- Main QFT lowering theorem, packaged as the public assertion. -/
theorem lowerQFT_correct
    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (r : ExtReg) :
    LowerQFTCorrect qs k hk ops r := by
  intro ψ pts hpts hworkspace hInterp hC hRun
  exact evalL_lowerQFT (qs := qs) (k := k) (hk := hk) (ops := ops) (r := r) (ψ := ψ)
    (pts := pts) (hpts := hpts) hworkspace hInterp hC hRun

end Shor
