import ForShor.ShorVerification.Implementation.Shor.Proofs.Support
import ForShor.ShorVerification.Implementation.Shor.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Clean-Result Sequencing Infrastructure

`LoweredCleanResult P G hworkspace ψ` packages the two facts needed at every
step of the readiness induction: the recursively lowered gate `G` starts with
clean local workspace, and after executing it the resulting state satisfies
`P`. `LoweredCleanResult.seq` is the sequencing lemma combining two such
results across a `Gate.seq`.
-/

namespace Shor
open Gate
open Classical

/-! =========================================================
    Clean-result sequencing infrastructure
========================================================= -/

/-!
`LoweredCleanResult P G hworkspace ψ` says:

1. every recursively lowered gate in `G` starts with clean local workspace;
2. after executing the lowered `G`, the state satisfies `P`.
-/
def LoweredCleanResult
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (Pol : ShorLoweringPolicy)
    (P : qs.State → Prop)
    (G : Gate)
    (hworkspace :
      Policy.GateWorkspaceOK Pol G)
    (ψ : qs.State) :
    Prop :=
  Policy.GateWorkspaceCleanState
      qs
      Pol
      G
      hworkspace
      ψ
    ∧
  P
    (LowerGateClass.evalL
      (qs := qs)
      (Policy.lowerGate
        Pol
        G
        hworkspace)
      ψ)

theorem LoweredCleanResult.seq
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {Pol : ShorLoweringPolicy}
    {Pmid Pout : qs.State → Prop}
    {U V : Gate}
    (hworkspace :
      Policy.GateWorkspaceOK Pol (U ;; V))
    (ψ : qs.State)
    (hU :
      LoweredCleanResult
        qs Pol Pmid
        U hworkspace.1 ψ)
    (hV :
      LoweredCleanResult
        qs Pol Pout
        V
        hworkspace.2
        (LowerGateClass.evalL
          (qs := qs)
          (Policy.lowerGate
            Pol
            U
            hworkspace.1)
          ψ)) :
    LoweredCleanResult
      qs Pol Pout
      (U ;; V)
      hworkspace
      ψ := by
  constructor
  · exact ⟨hU.1, hV.1⟩
  · change
      Pout
        (LowerGateClass.evalL
          (qs := qs)
          (LowGate.seq
            (Policy.lowerGate
              Pol
              U
              hworkspace.1)
            (Policy.lowerGate
              Pol
              V
              hworkspace.2))
          ψ)

    rw [LowerGateClass.evalL_seq]
    exact hV.2

end Shor
