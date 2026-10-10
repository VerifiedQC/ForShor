import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Assertions
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Correctness

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
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) :
    LowerSignedPhaseProductCorrect qs k hk phi x z ops := by
  intro ψ pts hpts hworkspace hInterp hC hRun
  let plan :
      StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) :=
    standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts hworkspace.static
  have hready : PhaseLoweringReady qs plan ψ := by
    simpa [plan] using
      standardSignedPhaseLoweringPlan_ready_of_workspace qs k hk phi x z ops ψ
        (pts := pts) (hpts := hpts) hworkspace hInterp hC hRun
  have hcorrect :=
    evalL_lowerSignedPhaseProd_of_plan
      (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (ops := ops)
      (pts := pts) (hpts := hpts) (plan := plan)
      (ψ := ψ) (hready := hready) (hInterp := hInterp) (hC := hC) (hRun := hRun)
  simpa [lowerSignedPhaseProdWithWorkspace, plan] using hcorrect

/-- Main controlled signed phase-product lowering theorem, packaged as the public assertion. -/
theorem lowerCSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) :
    LowerCSignedPhaseProductCorrect qs k hk ctrl phi x z ops := by
  intro ψ pts hpts hworkspace hInterp hC hRun
  let plan :
      StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z)
        (Gate.CSignedPhaseProd ctrl phi x z) :=
    standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts hworkspace.static
  have hready : PhaseLoweringReady qs plan ψ := by
    simpa [plan] using
      standardCSignedPhaseLoweringPlan_ready_of_workspace
        qs k hk ctrl phi x z ops ψ (pts := pts) (hpts := hpts) hworkspace hInterp hC hRun
  have hcorrect :=
    evalL_lowerGateRec_correct (qs := qs)
      (ShorLoweringPolicy.constPolicy_admissible (T := ⟨k, hk, pts, hpts, ops⟩)
        ⟨hInterp, hC, hRun⟩) plan ψ hready
  simpa [lowerCSignedPhaseProdWithWorkspace, lowerCSignedPhaseProd, plan] using hcorrect

/-! =========================================================
    The policy forms

    The claim a policy submission receives. The fixed-table theorems above are
    unchanged in statement and are now corollaries of these.
========================================================= -/

/-- Main signed phase-product lowering theorem under a policy. -/
theorem Policy.lowerSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg) :
    Policy.LowerSignedPhaseProductCorrect qs P phi x z := by
  intro ψ hworkspace hP
  have hready : PhaseLoweringReady qs (Policy.signedPlan P phi x z hworkspace.static) ψ :=
    Policy.signedPlan_ready qs P hP phi x z ψ hworkspace.static hworkspace.clean
  exact evalL_lowerGateRec_correct (qs := qs) hP (Policy.signedPlan P phi x z hworkspace.static)
    ψ hready

/-- Main controlled signed phase-product lowering theorem under a policy. -/
theorem Policy.lowerCSignedPhaseProduct_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg) :
    Policy.LowerCSignedPhaseProductCorrect qs P ctrl phi x z := by
  intro ψ hworkspace hP
  have hready :
      PhaseLoweringReady qs (Policy.cSignedPlan P ctrl phi x z hworkspace.static) ψ :=
    Policy.cSignedPlan_ready qs P hP ctrl phi x z ψ hworkspace.static hworkspace.clean
  exact evalL_lowerGateRec_correct (qs := qs) hP
    (Policy.cSignedPlan P ctrl phi x z hworkspace.static) ψ hready

end Shor
