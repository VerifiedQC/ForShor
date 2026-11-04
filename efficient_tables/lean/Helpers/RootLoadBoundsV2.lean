import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/- Algebraic consequence of the explicit Newton-family counts.
   The legal-schedule construction and its count formulas are proved on paper,
   not encoded in this module. This does NOT formalize table optimization in P. -/

namespace Paper

theorem newton_load_cubic_lower (k : ℝ) (hk : 3 ≤ k) :
    k ^ 3 / 6 ≤ (2 * k ^ 3 - 3 * k ^ 2 + 7 * k - 12) / 6 := by
  have hmul : 0 ≤ (k - 3) * k ^ 2 := mul_nonneg (by linarith) (sq_nonneg k)
  nlinarith

theorem newton_cost_quadratic_upper (k : ℝ) (hk : 3 ≤ k) :
    6 * k ^ 2 - 18 * k + 14 ≤ 6 * k ^ 2 := by
  linarith

theorem cubic_exceeds_claimed_amortization
    (k C D cost load : ℝ)
    (hk : 3 ≤ k) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlarge : 36 * C + 6 * D + 1 < k)
    (hcost : cost ≤ 6 * k ^ 2)
    (hload : k ^ 3 / 6 ≤ load) :
    C * cost + D * k < load := by
  have hkpos : 0 < k := by linarith
  have hsqpos : 0 < k ^ 2 := sq_pos_of_pos hkpos
  have hmul : 0 < (k - (36 * C + 6 * D + 1)) * k ^ 2 :=
    mul_pos (by linarith) hsqpos
  have hDmul : 0 ≤ D * (k ^ 2 - k) :=
    mul_nonneg hD (by nlinarith)
  have hCmul : C * cost ≤ C * (6 * k ^ 2) := mul_le_mul_of_nonneg_left hcost hC
  nlinarith

theorem natural_counterexample_parameters (C D : ℕ) :
    3 ≤ 36 * C + 6 * D + 10 ∧
    36 * C + 6 * D + 1 < 36 * C + 6 * D + 10 := by
  omega

end Paper
