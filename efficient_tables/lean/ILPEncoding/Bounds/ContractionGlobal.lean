import ILPEncoding.Bounds.Terminal

/-! # Global Contraction Expression Bound
Proves `contractionExpr_global`, a global bound on the contraction expression of an affine word, stated over any key set.
-/

namespace Paper.F7Contraction

open Paper.F6ILP Paper.F6ILPRows Paper.F7Size Paper.AffineNat

theorem contractionExpr_global {keys : Finset Nat}
    (e next : AffineExpr keys) (P U K B C : ℤ) (label : Label)
    (hP : 0 ≤ P) (hprod : P * label.k ≤ U)
    (hK : (label.k : ℤ) ≤ K) (hB : 0 ≤ B)
    (he : -B ≤ e.intercept ∧ e.intercept ≤ B)
    (hn : -B ≤ next.intercept ∧ next.intercept ≤ B)
    (hc : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C)
    (hnc : ∀ key, 0 ≤ next.coeff key ∧ next.coeff key ≤ C) :
    -((K + 1) * B + U) ≤ (contractionExpr e next P label).intercept ∧
      (contractionExpr e next P label).intercept ≤ (K + 1) * B + U ∧
      (∀ key, -((K + 1) * C) ≤ (contractionExpr e next P label).coeff key ∧
        (contractionExpr e next P label).coeff key ≤ (K + 1) * C) := by
  have hU : 0 ≤ U := le_trans (mul_nonneg hP (Int.natCast_nonneg _)) hprod
  have hK0 : 0 ≤ K := le_trans (Int.natCast_nonneg _) hK
  have hke : -(K * B) ≤ label.k * e.intercept ∧
      label.k * e.intercept ≤ K * B := by
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hK)
        (sub_nonneg.mpr he.1), mul_nonneg (Int.natCast_nonneg label.k)
        (sub_nonneg.mpr he.1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hK)
        (sub_nonneg.mpr he.2), mul_nonneg (Int.natCast_nonneg label.k)
        (sub_nonneg.mpr he.2)]
  have hcoeff : ∀ key, 0 ≤ label.k * e.coeff key ∧
      label.k * e.coeff key ≤ K * C := by
    intro key
    constructor
    · exact mul_nonneg (Int.natCast_nonneg _) (hc key).1
    · have hC0 : 0 ≤ C := le_trans (hc key).1 (hc key).2
      nlinarith [mul_nonneg (Int.natCast_nonneg label.k)
        (sub_nonneg.mpr (hc key).2),
        mul_nonneg (sub_nonneg.mpr hK) hC0]
  dsimp [contractionExpr, subExpr, scaleExpr, startExpr]
  constructor
  · nlinarith [hke.1, hn.2, hprod]
  constructor
  · nlinarith [hke.2, hn.1, hprod]
  · intro key
    have hec := hcoeff key
    have hnc' := hnc key
    constructor <;> nlinarith

end Paper.F7Contraction

