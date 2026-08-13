import FastMultiplication.ShorVerification.Framework.Quantum.Registers
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — abstract quantum state space

The `QSemantics` class (Hilbert-space states, basis kets, measurement-free
quantum structure) and its basic ket lemmas.  The gate-evaluation semantics
built on top of it live in `Framework/Semantics`.
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

/-! =========================================================
    Section 6: Abstract quantum semantics
========================================================= -/

/--
Abstract Hilbert-space semantics. This class deliberately does not mention any
circuit language: high-level `Gate` and low-level `LowGate` evaluators are
separate semantic interfaces built on top of the same quantum state space.
-/
class QSemantics where
  Basis : Type u
  State : Type u

  [instNormed : NormedAddCommGroup State]
  [instIP     : InnerProductSpace ℂ State]

  ket   : Basis → State

  state_induction :
    ∀ (P : State → Prop),
      P 0 →
      (∀ ψ φ, P ψ → P φ → P (ψ + φ)) →
      (∀ (a : ℂ) ψ, P ψ → P (a • ψ)) →
      (∀ b : Basis, P (ket b)) →
      ∀ ψ, P ψ

  ket_ne_zero (b : Basis) :
    ket b ≠ 0

  ket_inj : Function.Injective ket

  ket_inner_eq_of_eq :
    ∀ {b₁ b₂ : Basis},
      b₁ = b₂ →
      inner ℂ (ket b₁) (ket b₂) = (1 : ℂ)

  ket_inner_eq_zero_of_ne :
    ∀ {b₁ b₂ : Basis},
      b₁ ≠ b₂ →
      inner ℂ (ket b₁) (ket b₂) = 0


open QSemantics


attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

lemma ket_inner_self
    (qs : QSemantics)
    (b : qs.Basis) :
    inner ℂ (qs.ket b) (qs.ket b) = (1 : ℂ) := by
  exact qs.ket_inner_eq_of_eq rfl

lemma ket_inner_ne
    (qs : QSemantics)
    {b₁ b₂ : qs.Basis}
    (h : b₁ ≠ b₂) :
    inner ℂ (qs.ket b₁) (qs.ket b₂) = 0 := by
  exact qs.ket_inner_eq_zero_of_ne h

lemma ket_norm_one
    (qs : QSemantics)
    (b : qs.Basis) :
    ‖qs.ket b‖ = 1 := by
  have hinner :
      inner ℂ (qs.ket b) (qs.ket b) = (1 : ℂ) :=
    ket_inner_self qs b

  have hsq :
      ‖qs.ket b‖ ^ 2 = (1 : ℝ) := by
    calc
      ‖qs.ket b‖ ^ 2
          = Complex.re (inner ℂ (qs.ket b) (qs.ket b)) := by
              simpa using
                (norm_sq_eq_re_inner (𝕜 := ℂ) (qs.ket b))
      _ = 1 := by
              simp at hinner; cases hinner<;> rename_i h<;> simp[h]

  have hnonneg : 0 ≤ ‖qs.ket b‖ := norm_nonneg _

  have hfactor :
      (‖qs.ket b‖ - 1) * (‖qs.ket b‖ + 1) = 0 := by
    nlinarith

  have hplus_ne :
      ‖qs.ket b‖ + 1 ≠ 0 := by
    nlinarith

  have hminus :
      ‖qs.ket b‖ - 1 = 0 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact h
    · exfalso
      exact hplus_ne h

  nlinarith

end Shor
