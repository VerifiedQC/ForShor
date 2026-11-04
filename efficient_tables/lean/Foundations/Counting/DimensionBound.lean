import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Factorial power dimension bound

Pure natural-number arithmetic about factorials and powers. Proves `t ^ t ≤ t.factorial ^ 2` (`pow_self_le_factorial_sq`) from the pairwise estimate `pair_factor_lower_bound`, and uses it to derive the budget-style bound `factorial_power_dimension_bound`.
-/

namespace Paper.DimensionStage

lemma pair_factor_lower_bound {t i : Nat} (hi : i < t) :
    t ≤ (i + 1) * (t - i) := by
  have hfac : 1 ≤ t - i := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hi)
  have hmul : i ≤ i * (t - i) := by
    calc
      i = i * 1 := by simp
      _ ≤ i * (t - i) := Nat.mul_le_mul_left i hfac
  calc
    t = i + (t - i) := by omega
    _ ≤ i * (t - i) + (t - i) := Nat.add_le_add_right hmul _
    _ = (i + 1) * (t - i) := by ring

theorem pow_self_le_factorial_sq (t : Nat) : t ^ t ≤ t.factorial ^ 2 := by
  calc
    t ^ t = ∏ i ∈ Finset.range t, t := by simp
    _ ≤ ∏ i ∈ Finset.range t, ((i + 1) * (t - i)) := by
      apply Finset.prod_le_prod'
      intro i hi
      exact pair_factor_lower_bound (Finset.mem_range.mp hi)
    _ = (∏ i ∈ Finset.range t, (i + 1)) *
        (∏ i ∈ Finset.range t, (t - i)) := by
      rw [Finset.prod_mul_distrib]
    _ = t.factorial ^ 2 := by
      rw [Finset.prod_range_add_one_eq_factorial]
      rw [← Nat.descFactorial_eq_prod_range]
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_self]
      simp [pow_two]

theorem factorial_power_dimension_bound {t c U : Nat}
    (hfac : t.factorial ≤ U) : t ^ (c * t) ≤ U ^ (2 * c) := by
  have hbase : t ^ t ≤ U ^ 2 := by
    calc
      t ^ t ≤ t.factorial ^ 2 := pow_self_le_factorial_sq t
      _ ≤ U ^ 2 := Nat.pow_le_pow_left hfac 2
  calc
    t ^ (c * t) = t ^ (t * c) := by rw [Nat.mul_comm c t]
    _ = (t ^ t) ^ c := by rw [Nat.pow_mul]
    _ ≤ (U ^ 2) ^ c := Nat.pow_le_pow_left hbase c
    _ = U ^ (2 * c) := by rw [Nat.pow_mul]

end Paper.DimensionStage