import ForShor.ShorVerification.Implementation.Readout.Lowering
import ForShor.ShorVerification.Implementation.Compiler.Main

/-!
# Readout: the lowering of the measurement language is correct

`Policy.lowerM_correct`: under an admissible policy, the lowered program
(`Policy.lowerM`) of a measurement-language program with enough workspace acts on
a clean branching state exactly as the program (`Policy.MLowerGateCorrect`, the
form of the existing `Policy.LowerGateCorrect`). It lifts the existing lowering
correctness `Policy.lowerGate_correct` branch by branch; the only new step is the
reset of `measureReset`, whose low-level `LowGate.X q` is `Policy.lowerGate P (Gate.X q)`,
so it agrees with `qs.eval (Gate.X q)` by the same theorem.
-/

namespace Shor

section
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- The low-level reset branch is the high-level one (via the lowering of `Gate.X q`). -/
theorem measureResetBranchL_eq {P : ShorLoweringPolicy} (hP : P.Admissible) (q : ℕ) (b : Bool)
    (φ : qs.State) : measureResetBranchL q b φ = measureResetBranch q b φ := by
  cases b
  · rfl
  · simp only [measureResetBranchL, measureResetBranch, ite_true]
    exact Policy.lowerGate_correct qs P hP (Gate.X q) trivial _ trivial

end

/-- **The lowering of the measurement language is correct** (`lowerM_eval`), for every
policy, in the form of `Policy.LowerGateCorrect`. -/
theorem Policy.lowerM_correct (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    [LowerGateClass qs] [MeasureClass qs] (P : ShorLoweringPolicy) :
    Policy.MLowerGateCorrect qs P := by
  intro hP G
  induction G with
  | unitary u =>
      intro h ψ hc
      funext r
      exact Policy.lowerGate_correct qs P hP u h (ψ r) (hc r)
  | seq a b iha ihb =>
      intro h ψ hc
      show (Policy.lowerM P b h.2).eval ((Policy.lowerM P a h.1).eval ψ) = b.eval (a.eval ψ)
      rw [ihb h.2 _ hc.2, iha h.1 ψ hc.1]
  | measureReset q =>
      intro _ ψ _
      funext r
      show (if h : r = [] then 0 else measureResetBranchL q (r.getLast h) (ψ r.dropLast))
        = (if h : r = [] then 0 else measureResetBranch q (r.getLast h) (ψ r.dropLast))
      split
      · rfl
      · exact measureResetBranchL_eq hP _ _ _
  | ffPhase q j => intro _ _ _; rfl

/-- The lowering of the measurement language, applied: `lowerM_eval`. -/
theorem lowerM_eval {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    [LowerGateClass qs] [MeasureClass qs] {P : ShorLoweringPolicy} (hP : P.Admissible)
    (G : MGate) (hws : MGate.WorkspaceOK P G) (ψ : MState qs)
    (hclean : MGate.WorkspaceCleanState qs P G hws ψ) :
    (Policy.lowerM P G hws).eval ψ = G.eval ψ :=
  Policy.lowerM_correct qs P hP G hws ψ hclean

end Shor
