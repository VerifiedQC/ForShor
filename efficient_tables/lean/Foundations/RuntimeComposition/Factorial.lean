import Foundations.RuntimeComposition.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace RuntimeComposition

theorem C_Lem2_aux (t : ℕ) : t ^ t ≤ (Nat.factorial t) ^ 2 := by
  have h1 : Nat.factorial t = ∏ i ∈ Finset.range t, (i + 1) := by
    rw [Finset.prod_range_add_one_eq_factorial]
  have h2 : ∏ i ∈ Finset.range t, (i + 1) = ∏ i ∈ Finset.range t, (t - 1 - i + 1) :=
    (Finset.prod_range_reflect (fun i => i + 1) t).symm
  have h3 : (Nat.factorial t) ^ 2 = ∏ i ∈ Finset.range t, ((i + 1) * (t - 1 - i + 1)) := by
    rw [Finset.prod_mul_distrib, ← h2, ← h1, sq]
  rw [h3]
  calc t ^ t = ∏ _i ∈ Finset.range t, t := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro i hi
      have := Finset.mem_range.mp hi
      rcases Nat.exists_eq_add_of_lt this with ⟨k, hk⟩
      have e : t - 1 - i + 1 = t - i := by omega
      rw [e]
      obtain ⟨m, hm⟩ : ∃ m, t = i + m + 1 := ⟨k, hk⟩
      have e2 : t - i = m + 1 := by omega
      rw [e2, hm]
      nlinarith [Nat.zero_le i, Nat.zero_le m, Nat.zero_le (i * m)]

theorem tt_le_factorial_sq (t : ℕ) (ht : 1 ≤ t) :
    t ^ t ≤ (Nat.factorial t) ^ 2 ∧
      ∀ c U : ℕ, 1 ≤ c → Nat.factorial t ≤ U → t ^ (c * t) ≤ U ^ (2 * c) := by
  refine ⟨C_Lem2_aux t, ?_⟩
  intro c U _ hU
  calc t ^ (c * t) = (t ^ t) ^ c := by rw [mul_comm, pow_mul]
    _ ≤ ((Nat.factorial t) ^ 2) ^ c := Nat.pow_le_pow_left (C_Lem2_aux t) c
    _ ≤ (U ^ 2) ^ c := Nat.pow_le_pow_left (Nat.pow_le_pow_left hU 2) c
    _ = U ^ (2 * c) := by rw [← pow_mul]

end RuntimeComposition
