import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Readiness
import FastMultiplication.ShorVerification.Implementation.QFT.Spec.Cleanliness

/-!
# QFT Plan Readiness

`QFTLoweringReady`: the semantic precondition required to execute a
`QFTLoweringPlan` on a state. A split node needs the phase-product macro
workspace to be clean, the right child's plan to be ready, and (after
evaluating the right child and the phase gate) the left child's plan to be
ready.
-/

namespace Shor

noncomputable def QFTLoweringReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    qs.State → Prop := by
  induction plan with
  | empty r hsize => exact fun _ => True
  | singleton r hsize => exact fun _ => True
  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan readyRight readyLeft =>
      exact fun ψ =>
        Gate.PhaseProdWorkspace.CleanState qs ws ψ
        ∧
        readyRight ψ
        ∧
        let ψRight := LowerGateClass.evalL (qs := qs) (lowerQFTPlan rightPlan) ψ
        PhaseLoweringReady qs phasePlan ψRight
        ∧
        let ψPhase :=
          LowerGateClass.evalL (qs := qs) (lowerGateRec phasePlan) ψRight
        readyLeft ψPhase

end Shor
