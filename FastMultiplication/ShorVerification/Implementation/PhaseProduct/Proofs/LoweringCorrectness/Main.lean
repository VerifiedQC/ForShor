import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.PlanReadiness
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs

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
    [LowerGatePrimitiveBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (plan :
      StandardPhaseLoweringPlan
        k
        hk
        ops
        (phaseInputSize x z)
        (Gate.SignedPhaseProd phi x z))
    (ψ : qs.State)
    (hready :
      PhaseLoweringReady qs plan ψ)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        (genInterpolationPoints k))
    (hRun :
      run? ops State.start_state =
        some State.start_state) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerSignedPhaseProd
          k hk phi x z ops plan)
        ψ
      =
    qs.eval
        (Gate.SignedPhaseProd phi x z)
        ψ := by
  have hInterp :
      GoodToomCookPoints
        k
        (genInterpolationPoints k)
        (generatedInterpolationPoints_length k) := by
    simpa using genInterpolationPoints_good k
  exact
    evalL_lowerGateRec_correct
      (qs := qs)
      (hInterp := hInterp)
      (hC := hC)
      (hRun := hRun)
      plan
      ψ
      hready

end Shor
