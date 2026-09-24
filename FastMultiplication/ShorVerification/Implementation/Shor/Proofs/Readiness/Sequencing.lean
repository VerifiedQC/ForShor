import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static

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
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (lowering : ShorLoweringSetup)
    (P : qs.State → Prop)
    (G : Gate)
    (hworkspace :
      GateWorkspaceOK lowering.ops G)
    (ψ : qs.State) :
    Prop :=
  GateWorkspaceCleanState
      qs
      lowering.k
      lowering.hk
      lowering.ops
      lowering.pts
      lowering.hpts
      G
      hworkspace
      ψ
    ∧
  P
    (LowerGateClass.evalL
      (qs := qs)
      (lowerGate
        lowering.k
        lowering.hk
        lowering.ops
        lowering.pts
        lowering.hpts
        G
        hworkspace)
      ψ)

theorem LoweredCleanResult.seq
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    {lowering : ShorLoweringSetup}
    {Pmid Pout : qs.State → Prop}
    {U V : Gate}
    (hworkspace :
      GateWorkspaceOK lowering.ops (U ;; V))
    (ψ : qs.State)
    (hU :
      LoweredCleanResult
        qs lowering Pmid
        U hworkspace.1 ψ)
    (hV :
      LoweredCleanResult
        qs lowering Pout
        V
        hworkspace.2
        (LowerGateClass.evalL
          (qs := qs)
          (lowerGate
            lowering.k
            lowering.hk
            lowering.ops
            lowering.pts
            lowering.hpts
            U
            hworkspace.1)
          ψ)) :
    LoweredCleanResult
      qs lowering Pout
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
            (lowerGate
              lowering.k
              lowering.hk
              lowering.ops
              lowering.pts
              lowering.hpts
              U
              hworkspace.1)
            (lowerGate
              lowering.k
              lowering.hk
              lowering.ops
              lowering.pts
              lowering.hpts
              V
              hworkspace.2))
          ψ)

    rw [LowerGateClass.evalL_seq]
    exact hV.2

end Shor
