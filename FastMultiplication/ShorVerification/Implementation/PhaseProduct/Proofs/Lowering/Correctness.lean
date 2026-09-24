import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Widths
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Readiness
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.RecursiveReadiness

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Lowering Correctness Bridge

This proof module supplies the plan-level semantic bridge used by the public
theorems in `PhaseProduct.Main`. Earlier files build the plan, workspace, and
readiness invariants; `Main` packages the final reader-facing statements.
-/

/-! =========================================================
    Plan-Level Correctness

    The bridge theorem states that a supplied standard signed phase-product plan
    lowers to a low-level circuit with the same semantics as the high-level
    signed phase-product gate.
========================================================= -/

/-- Correctness of lowering a supplied standard signed phase-product plan. -/
lemma evalL_lowerSignedPhaseProd_of_plan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    {pts : List Point}
    {hpts : pts.length = q k}
    (plan : StandardPhaseLoweringPlan k hk pts hpts ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z))
    (ψ : qs.State)
    (hready : PhaseLoweringReady qs plan ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state) :
    LowerGateClass.evalL (qs := qs) (lowerSignedPhaseProd k hk phi x z ops pts hpts plan) ψ
      = qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
  exact evalL_lowerGateRec_correct (qs := qs) (hInterp := hInterp) (hC := hC) (hRun := hRun) plan ψ hready

end Shor
