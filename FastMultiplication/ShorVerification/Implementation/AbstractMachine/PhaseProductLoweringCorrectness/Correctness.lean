import FastMultiplication.ShorVerification.Implementation.AbstractMachine.PhaseProductLoweringCorrectness.PlanReadiness

namespace Shor
open Gate
open Operations

/-!
# Public Phase-Product Lowering Correctness
This file exposes the final signed and controlled signed phase-product lowering
theorems. Earlier files build the plan, workspace, and readiness invariants;
this file packages those invariants into the user-facing semantic correctness
statements.
-/

/-! =========================================================
    Section 1: Public correctness theorems
    The final results expose the canonical lowered signed phase-product circuit
    and state that low-level evaluation agrees with the corresponding high-level
    signed or controlled signed phase-product gate.
========================================================= -/

/-- Correctness of lowering a supplied standard signed phase-product plan. -/
lemma evalL_lowerSignedPhaseProd_of_plan
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
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

/--
The canonical lowered circuit constructed from the root physical-workspace
assumption.
The caller supplies only the static reserve and disjointness facts. All
recursive layouts and capacity proofs are constructed internally.
-/
noncomputable def lowerSignedPhaseProdWithWorkspace
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (hstatic :
      SignedRecursiveWorkspaceOK ops x z) :
    LowGate :=
  lowerSignedPhaseProd k hk phi x z ops
    (standardSignedPhaseLoweringPlan
      k hk phi x z ops hstatic)

/--
Correctness of canonical recursive signed-phase-product lowering.
The public workspace assumption only says that:
* the complete owned regions of `x` and `z` are disjoint;
* their reserves are sufficiently large for the complete recursion;
* those reserves are initially clean.
All recursive layouts, capacity proofs, and intermediate readiness conditions
are derived internally.
-/
theorem evalL_lowerSignedPhaseProd
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  [LowerGateClass qs]
    [LowerGateGateBridge qs]
  (k : ℕ)
  (hk : 1 < k)
  (phi : ℝ)
  (x z : ExtReg)
  (ops : Prog k)
  (ψ : qs.State)
  (hworkspace : SignedRecursiveWorkspaceStateOK qs ops x z ψ)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (hRun : run? ops State.start_state = some State.start_state) :
  LowerGateClass.evalL (qs := qs) (lowerSignedPhaseProdWithWorkspace k hk phi x z ops hworkspace.static) ψ
    =
  qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
let plan :
    StandardPhaseLoweringPlan
      k
      hk
      ops
      (phaseInputSize x z)
      (Gate.SignedPhaseProd phi x z) :=
  standardSignedPhaseLoweringPlan
    k hk phi x z ops
    hworkspace.static
have hready :
    PhaseLoweringReady qs plan ψ := by
  simpa [plan] using
    standardSignedPhaseLoweringPlan_ready_of_workspace
      qs
      k
      hk
      phi
      x
      z
      ops
      ψ
      hworkspace hC hRun
have hcorrect :=
  evalL_lowerSignedPhaseProd_of_plan
    (qs := qs)
    (k := k)
    (hk := hk)
    (phi := phi)
    (x := x)
    (z := z)
    (ops := ops)
    (plan := plan)
    (ψ := ψ)
    (hready := hready)
    (hC := hC)
    (hRun := hRun)
simpa [
  lowerSignedPhaseProdWithWorkspace,
  plan
] using hcorrect


/--
The canonical lowered controlled circuit constructed from the root physical-workspace assumption.
The caller supplies only the static reserve, disjointness, and control-disjointness facts.
All recursive layouts and capacity proofs are constructed internally.
-/
noncomputable def lowerCSignedPhaseProdWithWorkspace
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    LowGate :=
  lowerCSignedPhaseProd k hk ctrl phi x z ops
    (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hstatic)

/--
Correctness of canonical recursive controlled signed-phase-product lowering.
This is the controlled analogue of `evalL_lowerSignedPhaseProd`: the public
workspace assumption contains the static recursive reserve facts, control
separation, and initial reserve cleanliness.
-/
theorem evalL_lowerCSignedPhaseProd
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
  (ops : Prog k)
  (ψ : qs.State)
  (hworkspace : CSignedRecursiveWorkspaceStateOK qs ops ctrl x z ψ)
  (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
  (hRun : run? ops State.start_state = some State.start_state) :
  LowerGateClass.evalL (qs := qs)
      (lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops hworkspace.static) ψ
    =
  qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
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
  have hcorrect :=
    evalL_lowerGateRec_correct
      (qs := qs)
      (hInterp := hInterp)
      (hC := hC)
      (hRun := hRun)
      plan
      ψ
      hready
  simpa [lowerCSignedPhaseProdWithWorkspace, lowerCSignedPhaseProd, plan] using hcorrect

end Shor
