import ForShor.ShorVerification.Implementation.Shor.Statement
import ForShor.ShorVerification.Implementation.Shor.Proofs.Correctness
import ForShor.ShorVerification.Implementation.Shor.Proofs.Workspace

/-!
# Shor Main Theorems

The Shor theorems, each typed by its named proposition from `Statement.lean`
and proven here. All supporting lemmas live under `Shor.Proofs`.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]

/--
Correctness of the fully lowered approximate Shor order-finding circuit.
-/
theorem Shor_correct_approx_lowered_uniform
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLoweredUniform T hT := by
  refine ⟨1600, by norm_num, le_refl _, ?_⟩
  intro inst P hP x y work scratch flag b0 hm hn η hready _hws
  exact Shor_correct_approx_lowered_of_modExp_bound (qs := qs) 1600
    (modExpApprox_valid_dist_1600 (qs := qs)) T hT
    inst P hP x y work scratch flag b0 hm hn η hready

/--
Correctness of the fully lowered approximate Shor order-finding circuit at a
precision chosen from `N`.
-/
theorem Shor_correct_approx_lowered
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T) :
    ShorCorrectApproxLowered T hT :=
  Shor_correct_approx_lowered_at_shorPrecision T hT

end Shor
