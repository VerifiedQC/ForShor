import Foundations.SeparationLemmas.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib

namespace SeparationLemmas

theorem peeling {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ℕ) (ε lam : ι → ℤ) (c : ι → ℕ)
    (hgap : SeparationLemmas.GapSep H ε lam c) (L : Finset ι) (A B : ℤ)
    (hAB : A + (H : ℤ) ≤ B)
    (hL : ∀ i ∈ L, lam i ≤ A) (hU : ∀ j ∈ Lᶜ, B ≤ lam j)
    (hm : ∃ m : ℤ, (∑ i ∈ L, (ε i : ℚ) * (2 : ℚ) ^ (lam i))
        + (∑ j ∈ Lᶜ, (ε j : ℚ) * (2 : ℚ) ^ (lam j)) = (2 : ℚ) ^ B * (m : ℚ)) :
    (∑ i ∈ L, (ε i : ℚ) * (2 : ℚ) ^ (lam i)) = 0 := by
  obtain ⟨hcard, heps, -⟩ := hgap
  obtain ⟨m, hm⟩ := hm
  set X := ∑ i ∈ L, (ε i : ℚ) * (2 : ℚ) ^ (lam i) with hX
  have hB2 : (0 : ℚ) < 2 ^ B := zpow_pos (by norm_num) _
  set m' : ℤ := ∑ j ∈ Lᶜ, ε j * 2 ^ ((lam j - B).toNat) with hm'
  have hY : ∑ j ∈ Lᶜ, (ε j : ℚ) * (2 : ℚ) ^ (lam j) = (2 : ℚ) ^ B * (m' : ℚ) := by
    rw [hm']; push_cast; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have e : (2 : ℚ) ^ (lam j) = 2 ^ B * 2 ^ ((lam j - B).toNat) := by
      have := hU j hj
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      omega
    rw [e]; ring
  have hXe : X = (2 : ℚ) ^ B * ((m - m' : ℤ) : ℚ) := by
    push_cast; rw [hY] at hm; linarith
  have hbound : |X| < 2 ^ B := by
    have h1 : |X| ≤ (L.card : ℚ) * 2 ^ A := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℚ) < 2) _)]
      have h1 : |(ε i : ℚ)| ≤ 1 := by
        have hi := heps i
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with h | h | h <;> rw [h] <;> norm_num
      have h2 : (2 : ℚ) ^ (lam i) ≤ 2 ^ A :=
        zpow_le_zpow_right₀ (by norm_num) (hL i hi)
      have h3 : (0 : ℚ) < 2 ^ (lam i) := zpow_pos (by norm_num) _
      nlinarith
    have hcL : (L.card : ℚ) < 2 ^ H := by
      have : L.card < 2 ^ H := lt_of_le_of_lt (Finset.card_le_univ _) hcard
      exact_mod_cast this
    have hA : (0 : ℚ) < 2 ^ A := zpow_pos (by norm_num) _
    have hAB' : (2 : ℚ) ^ (A + (H : ℤ)) ≤ 2 ^ B :=
      zpow_le_zpow_right₀ (by norm_num) hAB
    have hB : (2 : ℚ) ^ (A + (H : ℤ)) = 2 ^ H * 2 ^ A := by
      rw [zpow_add₀ (by norm_num), zpow_natCast]; ring
    nlinarith
  have hk : |((m - m' : ℤ) : ℚ)| < 1 := by
    by_contra hc
    push_neg at hc
    rw [hXe, abs_mul, abs_of_pos hB2] at hbound
    nlinarith
  have hk0 : m - m' = 0 := by
    have : |m - m'| < 1 := by exact_mod_cast hk
    rw [abs_lt] at this; omega
  rw [hXe, hk0]; simp

end SeparationLemmas
