import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition

namespace Shor

/-!
# Framework/Spec: order-finding interface

Submission-facing order-finding data, measurement semantics, and success
probabilities. This module deliberately imports only framework modules.
-/

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

/-- Run an arbitrary circuit-like object `C` using `evalC`, then measure `r`. -/
noncomputable def measProbAfter
    [MeasureClass qs]
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (r : Reg)
    (o : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  MeasureClass.probMeas (qs := qs) r o (evalC C ψ)

/-- Success probability after an arbitrary circuit-like object `C`.

`evalC` specifies how that circuit type acts on states. -/
noncomputable def probability_of_success
    [MeasureClass qs]
    [ContinuedFractionPost]
    {Circuit : Type}
    (evalC : Circuit → qs.State → qs.State)
    (T : ℕ → ℕ)
    (verify : OrderVerifier)
    (x : Reg)
    (r Q : ℕ)
    (C : Circuit)
    (ψ : qs.State) : ℝ :=
  ∑ o : Fin Q,
    (r_found (T := T) verify o.1 Q r) *
      measProbAfter
        (qs := qs) evalC x o.1 C ψ

/-- Arithmetic, width, and continued-fraction assumptions for one
order-finding instance. -/
structure ShorOrderFindingInstance where
  /-- The base whose order is being found. -/
  a : ℕ
  /-- The modulus to factor. -/
  N : ℕ
  /-- The exponent/control register. -/
  x : ExtReg
  /-- The modular-exponentiation data register. -/
  y : ExtReg
  /-- The sampled base is in the valid range. -/
  range : 0 < a ∧ a < N
  /-- The sampled base is coprime to the modulus. -/
  coprime : Nat.gcd a N = 1
  /-- The exponent register has the standard Shor width. -/
  x_width : regSize x.active = Nat.log2 (2 * N^2)
  /-- The data register has enough room for residues modulo `N`. -/
  y_width : regSize y.active = Nat.log2 (2 * N)

/-- Clean ideal input expected by order-finding: zero exponent/data registers
and disjoint ownership. -/
def IdealOrderFindingInput
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    (x y : ExtReg)
    (b0 : qs.Basis) : Prop :=
  RegEncoding.toNat x.active b0 = 0 ∧
  RegEncoding.toNat y.active b0 = 0 ∧
  ExtReg.OwnedDisjoint x y

end Shor
