import ForShor.ShorVerification.Implementation.QFT.Statement
import ForShor.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import ForShor.ShorVerification.Implementation.QFT.Proofs.GateCount
import ForShor.ShorVerification.Implementation.QFT.Proofs.PolicyGateCount

/-!
# QFT Main Theorems

This module proves the public assertions for the QFT implementation: the
lowering is correct, and its gate count grows at the phase-product rate.
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

/-- **The QFT gate count** for a table satisfying C1–C4: above some width, at
most a constant times `n^(log_k (2k - 1))`. (`QFTGateCountBoundOfProgramOK`.) -/
theorem qftGateCountBound_of_programOK
    {Basis : Type u}
    [RegEncoding Basis]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) :
    QFTGateCountBoundOfProgramOK (Basis := Basis) k hk ops pts hpts :=
  fun hops =>
    qftGateCountBound_of_phaseProduct (Basis := Basis) k hk ops pts hpts
      (unsignedPhaseProductBound_of_programOK (Basis := Basis) k hk ops pts hpts hops)

/-- **The QFT gate count under a policy.** (`Policy.QFTGateCountBound`.) -/
theorem Policy.qftGateCountBound (P : ShorLoweringPolicy) :
    Policy.QFTGateCountBound P :=
  fun hP => Policy.lowerQFT_gateCountFor_bound P.negation P hP

end Shor
