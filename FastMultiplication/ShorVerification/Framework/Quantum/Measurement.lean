import FastMultiplication.ShorVerification.Framework.Quantum.QSemantics
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Framework/Quantum: measurement

`MeasureClass` packages the Born-rule projectors used to talk about measuring a
register — a quantum primitive, independent of any gate language.
-/

namespace Shor

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]

/-- Abstract interface for measuring a register.

Rather than committing to a concrete basis-level measurement construction, the
framework assumes the usual finite family of orthogonal self-adjoint projectors
and the Born rule for probabilities. -/
class MeasureClass (qs : QSemantics) [RegEncoding qs.Basis] where

  /-- Outcome projector for measuring register `r`. -/
  measProj : Reg → ℕ → qs.State →L[ℂ] qs.State

  /-- No outcomes beyond the register's computational-basis range. -/
  measProj_zero_outOfRange :
    ∀ r o ψ,
      2 ^ regSize r ≤ o →
      measProj r o ψ = 0

  /-- Each measurement effect is a self-adjoint projector. -/
  measProj_selfAdjoint :
    ∀ r o ψ φ,
      inner ℂ (measProj r o ψ) φ
        = inner ℂ ψ (measProj r o φ)

  /-- Different outcomes are orthogonal projectors. -/
  measProj_orthogonal :
    ∀ r o o' ψ,
      o ≠ o' →
      measProj r o (measProj r o' ψ) = 0

  /-- The projectors sum to identity over valid outcomes. -/
  measProj_complete :
    ∀ r ψ,
      (∑ o : Fin (2 ^ regSize r), measProj r o.1 ψ) = ψ


namespace MeasureClass
def probMeas
    [MeasureClass qs]
    (r : Reg) (o : ℕ) (ψ : qs.State) : ℝ :=
  ‖measProj r o ψ‖ ^ 2

/-- Born rule. -/
lemma probMeas_born [MeasureClass qs]:
    ∀ r o ψ,
      probMeas r o ψ = ‖MeasureClass.measProj r o ψ‖ ^ 2:=by simp[probMeas]


theorem measProj_idempotent
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [MeasureClass qs]
    (r : Reg) (o : ℕ) (ψ : qs.State) :
    MeasureClass.measProj r o
        (MeasureClass.measProj r o ψ) =
      MeasureClass.measProj r o ψ := by
  classical
  by_cases ho : o < 2 ^ regSize r
  · let i : Fin (2 ^ regSize r) := ⟨o, ho⟩

    have hsum :
        (∑ j : Fin (2 ^ regSize r),
          MeasureClass.measProj r j.1
            (MeasureClass.measProj r o ψ)) =
        MeasureClass.measProj r i.1
          (MeasureClass.measProj r o ψ) := by
      apply Fintype.sum_eq_single i
      intro j hji
      apply MeasureClass.measProj_orthogonal
      intro hjo
      apply hji
      apply Fin.ext
      simpa [i] using hjo

    have hcomplete :=
      MeasureClass.measProj_complete
        (qs := qs) r
        (MeasureClass.measProj r o ψ)

    simpa [i] using hsum.symm.trans hcomplete

  · have ho' : 2 ^ regSize r ≤ o :=
      Nat.le_of_not_gt ho

    calc
      MeasureClass.measProj r o
          (MeasureClass.measProj r o ψ)
          = 0 :=
        MeasureClass.measProj_zero_outOfRange
          (qs := qs) r o
          (MeasureClass.measProj r o ψ) ho'

      _ = MeasureClass.measProj r o ψ :=
        (MeasureClass.measProj_zero_outOfRange
          (qs := qs) r o ψ ho').symm

end MeasureClass

end Shor
