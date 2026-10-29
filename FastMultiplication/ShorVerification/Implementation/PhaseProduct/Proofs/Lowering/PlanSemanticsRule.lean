import Mathlib.Data.Nat.Bitwise
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.Lowerable
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Compilation
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Readiness
import FastMultiplication.ShorVerification.Framework.Policy
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.CorrectnessRule

/-!
# Compiled phase-product gates under a width rule

`eval_compiledSignedPhaseGate_correct` and the controlled analogue for either
width rule `R`, for the policy lowering. `PlanSemantics.lean` keeps upstream's
scan statements.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-- For either width rule `R`: A compiled signed recursive phase-product gate evaluates to its source signed phase product. -/
lemma eval_compiledSignedPhaseGate_correct_by
    (R : WidthRule)
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (ψ : qs.State)
    (hclean : CleanWorkspaceState qs (initSignedLayoutState layout) (neededWidthsBy R x z ops) ψ) :
    qs.eval (compiledSignedPhaseGateBy R k hk pts hpts ops phi x z layout) ψ
      = qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
  unfold compiledSignedPhaseGateBy
  unfold loweringPhaseCoeff
  rw [cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth pts hpts hInterp]
  apply eval_compileOpsToSignedGate_correct_by (R := R)
    (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
    (pts := pts) (hpts := hpts) (hInterp := hInterp) (ψ := ψ) (ops := ops) (hC := hC)
    (run_ops_start_state := hRun)
  exact hclean

/-- For either width rule `R`: A compiled controlled signed recursive phase-product gate evaluates to its source controlled gate. -/
lemma eval_compiledCSignedPhaseGate_correct_by
    (R : WidthRule)
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hctrl : layout.ControlDisjoint ctrl)
    (ψ : qs.State)
    (hclean : CleanWorkspaceState qs (initSignedLayoutState layout) (neededWidthsBy R x z ops) ψ) :
    qs.eval (compiledCSignedPhaseGateBy R k hk pts hpts ops ctrl phi x z layout) ψ
      = qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
  unfold compiledCSignedPhaseGateBy
  unfold loweringPhaseCoeff
  rw [cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth pts hpts hInterp]
  apply eval_compileOpsToCSignedGate_correct_by (R := R)
    (qs := qs) (k := k) (hk := hk) (ctrl := ctrl) (phi := phi) (x := x) (z := z)
    (layout := layout) (hctrl := hctrl) (pts := pts) (hpts := hpts) (hInterp := hInterp)
    (ops := ops) (hC := hC) (hRun := hRun) (ψ := ψ)
  exact hclean

end Shor
