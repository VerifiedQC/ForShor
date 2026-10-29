import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Correctness
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.CompilationRule

/-!
# Gate-level correctness under a width rule

`eval_compileOpsToSignedGate_correct` and the controlled analogue for either
width rule `R`. `Correctness.lean` keeps upstream's statements (the scan).
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-- For either width rule `R`: State-level correctness of the signed compiled circuit on clean workspace states. -/
lemma eval_compileOpsToSignedGate_correct_by
    (R : WidthRule)
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (pts : List Point)
    (hpts : List.length pts = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ψ : qs.State)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hψ : CleanWorkspaceState qs (initSignedLayoutState layout) (neededWidthsBy R x z ops) ψ)
    (run_ops_start_state : run? ops State.start_state = some State.start_state) :
    let Wphase : ℕ := phaseLimbWidth x z k
    let coeff : Fin (q k) → ℚ := phaseCoeffFromPtsWidth k Wphase pts hpts
    qs.eval (compileOpsToSignedGateBy R k hk phi x z layout coeff ops) ψ
      = qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
  induction hψ with
  | ket b hworkspace =>
      exact eval_compileOpsToSignedGate_correct_ket_by (R := R)
        (qs := qs) (k := k) (hk := hk) (phi := phi) (x := x) (z := z) (layout := layout)
        (pts := pts) (hpts := hpts) (hInterp := hInterp) (b := b) (ops := ops) (hC := hC)
        (hworkspace := hworkspace) (run_ops_start_state := run_ops_start_state)
  | zero => simp [qs.eval_zero]
  | add hψ hφ ihψ ihφ => simpa [qs.eval_add] using congrArg₂ (· + ·) ihψ ihφ
  | smul a hψ ihψ => simpa [qs.eval_smul] using congrArg (a • ·) ihψ

/-- For either width rule `R`: State-level correctness of the controlled signed compiled circuit on clean workspace states. -/
lemma eval_compileOpsToCSignedGate_correct_by
    (R : WidthRule)
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hctrl : layout.ControlDisjoint ctrl)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (ψ : qs.State)
    (hψ : CleanWorkspaceState qs (initSignedLayoutState layout) (neededWidthsBy R x z ops) ψ) :
    qs.eval
        (compileOpsToCSignedGateBy R k hk ctrl phi x z layout
          (phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts) ops)
        ψ
      = qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
  induction hψ with
  | ket b hworkspace =>
      exact eval_compileOpsToCSignedGate_correct_ket_by (R := R)
        (qs := qs) (k := k) (hk := hk) (ctrl := ctrl) (phi := phi) (x := x) (z := z)
        (layout := layout) (hctrl := hctrl) (pts := pts) (hpts := hpts) (hInterp := hInterp)
        (ops := ops) (hC := hC) (hRun := hRun) (b := b) (hworkspace := hworkspace)
  | zero => simp [qs.eval_zero]
  | add hψ hφ ihψ ihφ => simpa [qs.eval_add] using congrArg₂ (· + ·) ihψ ihφ
  | smul a hψ ihψ => simpa [qs.eval_smul] using congrArg (a • ·) ihψ

end Shor
