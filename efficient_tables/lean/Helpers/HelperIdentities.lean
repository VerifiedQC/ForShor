import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace Paper

theorem helper_divided_difference_recurrence
    (u v : Int) (h : Nat → Int) (hzero : h 0 = 0)
    (hstep : ∀ n, h (n + 1) = v * h n + u ^ n) :
    ∀ n, (v - u) * h n = v ^ n - u ^ n := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      calc
        (v - u) * h (n + 1) =
            v * ((v - u) * h n) + (v - u) * u ^ n := by
              rw [hstep]
              ring
        _ = v * (v ^ n - u ^ n) + (v - u) * u ^ n := by rw [ih]
        _ = v ^ (n + 1) - u ^ (n + 1) := by
              simp only [pow_succ]
              ring

theorem helper_cleanup_width (x y b w : Nat)
    (hw : w = 1 + max x (y + b)) :
    1 + max w (y + b) = w + 1 := by
  omega

theorem helper_ascending_collect_exchange (x a b : Nat) (hab : a ≤ b) :
    1 + max (1 + max x a) b ≤ 1 + max (1 + max x b) a := by
  omega

theorem helper_collection_preserves_dominance (x y a b : Nat)
    (hxy : x ≤ y) (hab : a ≤ b) :
    1 + max x a ≤ 1 + max y b := by
  omega

end Paper
