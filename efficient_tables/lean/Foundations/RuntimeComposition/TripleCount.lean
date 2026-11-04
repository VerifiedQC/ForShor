import Foundations.RuntimeComposition.Defs
import Mathlib.Tactic

namespace RuntimeComposition

theorem triple_count_le (K : ℕ) (hK : 2 ≤ K) :
    (RuntimeComposition.tripleSet K).card ≤ 28 * K ^ 5 ∧
      (RuntimeComposition.tripleSet K).card ≤ 2 ^ (5 + 5 * RuntimeComposition.bl K) := by
  have h1 : (RuntimeComposition.tripleSet K).card ≤ 28 * K ^ 5 := by
    unfold RuntimeComposition.tripleSet
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_sigma]
    have : ∀ k ∈ Finset.Icc 2 K,
        (Finset.range k ×ˢ Finset.range (27 * k ^ 3 + 1)).card ≤ 28 * K ^ 4 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.card_product, Finset.card_range, Finset.card_range]
      have h3 : k ^ 3 ≤ K ^ 3 := Nat.pow_le_pow_left hk.2 3
      have h1 : k ≤ K := hk.2
      have : k * (27 * k ^ 3 + 1) ≤ 28 * K ^ 4 := by
        have hk1 : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ (by omega)
        calc k * (27 * k ^ 3 + 1) ≤ K * (28 * K ^ 3) := by
              apply Nat.mul_le_mul h1; omega
          _ = 28 * K ^ 4 := by ring
      exact this
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
    rw [Nat.card_Icc, smul_eq_mul]
    have : K + 1 - 2 ≤ K := by omega
    calc (K + 1 - 2) * (28 * K ^ 4) ≤ K * (28 * K ^ 4) := Nat.mul_le_mul_right _ this
      _ = 28 * K ^ 5 := by ring
  refine ⟨h1, h1.trans ?_⟩
  have hkb : K < 2 ^ RuntimeComposition.bl K := Nat.lt_pow_succ_log_self (by norm_num) K
  calc 28 * K ^ 5 ≤ 2 ^ 5 * (2 ^ RuntimeComposition.bl K) ^ 5 := by
        apply Nat.mul_le_mul (by norm_num)
        exact Nat.pow_le_pow_left hkb.le 5
    _ = 2 ^ (5 + 5 * RuntimeComposition.bl K) := by rw [← pow_mul, ← pow_add, mul_comm (RuntimeComposition.bl K)]

end RuntimeComposition
