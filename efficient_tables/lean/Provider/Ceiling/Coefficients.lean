import Provider.Ceiling.DyadicPoints

/-! # Dyadic Coefficients
Defines the predicate `CoeffDyadic` on integer coefficients with respect to an exponent `E`. Proves `coeffDyadic_pow` for powers and `addConstFrom_coeff_fixed` for the coefficient produced by `addConstFrom` on a fixed source register.
-/

namespace Paper.F3ChargeCeiling

open TableGeneration

def CoeffDyadic (E : Nat) (c : Int) : Prop :=
  c = 0 ∨ ∃ e, e ≤ E ∧ c.natAbs = 2^e

theorem coeffDyadic_pow {E : Nat} (c : Int) (e j : Nat)
    (he : e * j ≤ E) (h : c.natAbs = 2^e) :
    CoeffDyadic E (c^j) := by
  right
  refine ⟨e*j, he, ?_⟩
  rw [Int.natAbs_pow, h, pow_mul]

theorem coeffDyadic_zero_pow (E j : Nat) :
    CoeffDyadic E ((0 : Int)^j) := by
  cases j with
  | zero =>
    right
    exact ⟨0, Nat.zero_le _, by norm_num⟩
  | succ j =>
    left
    simp

theorem addConstFrom_coeff_fixed {k : Nat} (dst src : Fin k) (E : Nat)
    (hsep : src ≠ dst) (c : Int) (h : CoeffDyadic E c) :
    SourceFixed dst E (addConstFrom dst src c) ∧
      (addConstFrom dst src c).length ≤ 1 := by
  rcases h with rfl | ⟨e, he, habs⟩
  · simp [SourceFixed, addConstFrom]
  · rw [addConstFrom_dyadic dst src c e habs]
    constructor
    · intro op hop
      simp only [List.mem_singleton] at hop
      subst op
      exact Or.inr ⟨src, decide (c < 0), e, hsep, he, rfl⟩
    · simp

end Paper.F3ChargeCeiling
