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
  /-- Probability of observing outcome `o` when measuring register `r`. -/
  probMeas : Reg → ℕ → qs.State → ℝ

  /-- Outcome projector for measuring register `r`. -/
  measProj : Reg → ℕ → qs.State →L[ℂ] qs.State

  /-- Born rule. -/
  probMeas_born :
    ∀ r o ψ,
      probMeas r o ψ = ‖measProj r o ψ‖ ^ 2

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

  /-- Projector idempotence for a single measurement outcome. -/
  measProj_idempotent :
    ∀ r o ψ,
      measProj r o (measProj r o ψ) = measProj r o ψ

  /-- Different outcomes are orthogonal projectors. -/
  measProj_orthogonal :
    ∀ r o o' ψ,
      o ≠ o' →
      measProj r o (measProj r o' ψ) = 0

  /-- The projectors sum to identity over valid outcomes. -/
  measProj_complete :
    ∀ r ψ,
      (∑ o : Fin (2 ^ regSize r), measProj r o.1 ψ) = ψ


end Shor
