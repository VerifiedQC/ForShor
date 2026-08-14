import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Assertions
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.Main

/-!
# Phase-Product Main Theorems

This module proves the public assertions for the phase-product implementation.
All supporting lemmas are kept under `PhaseProduct.Proofs`.
-/

namespace Shor
open Gate
open Operations

/-- Main signed phase-product lowering theorem, packaged as the public assertion. -/
theorem lowerSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
  (ops : Prog k) :
    LowerSignedPhaseProductCorrect qs k hk phi x z ops := by
  intro ψ hworkspace hC hRun
  let plan : StandardPhaseLoweringPlan
        k hk ops
        (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) :=
    standardSignedPhaseLoweringPlan
      k hk phi x z ops
      hworkspace.static
  have hready :
      PhaseLoweringReady qs plan ψ := by
    simpa [plan] using standardSignedPhaseLoweringPlan_ready_of_workspace qs k hk phi x z ops ψ hworkspace hC hRun
  have hcorrect :=
    evalL_lowerSignedPhaseProd_of_plan
      (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (ops := ops) (plan := plan)
      (ψ := ψ) (hready := hready) (hC := hC) (hRun := hRun)
  simpa [lowerSignedPhaseProdWithWorkspace,plan] using hcorrect

/-- Main controlled signed phase-product lowering theorem, packaged as the public assertion. -/
theorem lowerCSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
  (ops : Prog k) :
    LowerCSignedPhaseProductCorrect qs k hk ctrl phi x z ops := by
  intro ψ hworkspace hC hRun
  let plan :
      StandardPhaseLoweringPlan k hk ops (phaseInputSize x z)
        (Gate.CSignedPhaseProd ctrl phi x z) :=
    standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hworkspace.static
  have hready : PhaseLoweringReady qs plan ψ := by
    simpa [plan] using
      standardCSignedPhaseLoweringPlan_ready_of_workspace
        qs k hk ctrl phi x z ops ψ hworkspace hC hRun
  have hInterp :
      GoodToomCookPoints k (genInterpolationPoints k) (generatedInterpolationPoints_length k) := by
    simpa using genInterpolationPoints_good k
  have hcorrect := evalL_lowerGateRec_correct (qs := qs) (hInterp := hInterp) (hC := hC) (hRun := hRun) plan ψ hready
  simpa [lowerCSignedPhaseProdWithWorkspace, lowerCSignedPhaseProd, plan] using hcorrect

end Shor
