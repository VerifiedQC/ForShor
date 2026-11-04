import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

namespace Paper

theorem rounded_leaf_budget (N R tN tR c : ℚ)
    (hR : 0 ≤ R) (hNR : R ≤ N) (htR : 0 ≤ tR) (ht : tR ≤ tN)
    (hc : c < 4 * (N - R)) :
    c + R * (4 + tR) < N * (4 + tN) := by
  have hN : 0 ≤ N := le_trans hR hNR
  have h1 : 0 ≤ N * (tN - tR) := mul_nonneg hN (sub_nonneg.mpr ht)
  have h2 : 0 ≤ (N - R) * tR := mul_nonneg (sub_nonneg.mpr hNR) htR
  nlinarith

theorem explicit_budget_margin (k : ℚ) (hk : 3 ≤ k) :
    4088 < 4 * k * (4096 * k - 10658) := by
  nlinarith [sq_nonneg (k - 3)]

end Paper
