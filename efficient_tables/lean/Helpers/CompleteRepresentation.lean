import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace Paper

-- Scalar arithmetic supporting the all-target evaluation blind spot.
-- The F2 indexing, coefficient-vector embedding and legality proof remain external.
theorem consecutive_integer_evaluations_even (z : Int) :
    (z * z - z) % 2 = 0 := by
  have hz : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rcases hz with h | h <;> simp [Int.sub_emod, Int.mul_emod, h]

theorem homogeneous_integer_evaluations_even (z : Int) (m : Nat) :
    (z ^ (m + 1) * (1 - z)) % 2 = 0 := by
  have h : (z * (1 - z)) % 2 = 0 := by
    have hz : z % 2 = 0 ∨ z % 2 = 1 := by omega
    rcases hz with h | h <;> simp [Int.sub_emod, Int.mul_emod, h]
  have heq : z ^ (m + 1) * (1 - z) = z ^ m * (z * (1 - z)) := by
    rw [pow_succ]
    ring
  rw [heq, Int.mul_emod, h]
  simp

theorem odd_coefficient_obstruction :
    ((-1 : Int) % 2 = 1) ∧ ((1 : Int) % 2 = 1) := by decide

-- Constants only; the catalogue-family and witness premises are separately reviewed.
theorem all_order_catalogue_gap : (327272 : Int) < 345083 := by decide

end Paper

