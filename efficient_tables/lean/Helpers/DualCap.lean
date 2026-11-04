import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

namespace Paper

theorem max_weight_budget (A B : ℚ) :
    A + B ≤ 2 * max A B := by
  have hA := le_max_left A B
  have hB := le_max_right A B
  linarith

theorem weighted_dual_add_progress (x y A B l : ℚ)
    (hB : 0 ≤ B) (hl : 0 ≤ l) :
    |x| * A + |y| * B + |x| * |A - l * B| ≤
      |x| * (2 * max A (l * B)) + |y - l * x| * B := by
  have ht := abs_add_le (y - l * x) (l * x)
  rw [sub_add_cancel, abs_mul, abs_of_nonneg hl] at ht
  have hw := mul_le_mul_of_nonneg_right ht hB
  rcases le_total A (l * B) with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith

theorem weighted_dual_add_monotone (x y A B l : ℚ)
    (hB : 0 ≤ B) (hl : 0 ≤ l) :
    |x| * A + |y| * B ≤
      |x| * (2 * max A (l * B)) + |y - l * x| * B := by
  have h := weighted_dual_add_progress x y A B l hB hl
  have hn : 0 ≤ |x| * |A - l * B| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  linarith

end Paper
