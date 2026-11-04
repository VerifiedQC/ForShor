import ILPEncoding.Bounds.ContractionRows

/-! # Contraction Root Bounds
Proves `contractionRoot_bounds`, bounds on the contraction rows for a label list at the root, from the per-row bounds in `ContractionRows`.
-/

namespace Paper.F7Contraction

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPSystem Paper.F6ILPCost
open Paper.F7Size Paper.F7QControl Paper.AffineNat

theorem contractionRoot_bounds (labels : List Label) (x n : ℤ)
    (U K : Nat) (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hn : 0 ≤ n) (hx : -n ≤ x ∧ x ≤ n) :
    (contractionRoot labels x).Forall
      (fun row =>
        -(((K : ℤ) + 1) *
            (n + 2 * (U : ℤ) * K * labels.length) + U) ≤
          row.intercept ∧
        row.intercept ≤
          ((K : ℤ) + 1) *
            (n + 2 * (U : ℤ) * K * labels.length) + U ∧
        (∀ key,
          -(((K : ℤ) + 1) * (U : ℤ) * labels.length) ≤
            row.coeff key ∧
          row.coeff key ≤
            ((K : ℤ) + 1) * (U : ℤ) * labels.length)) := by
  have hcontrol : Controlled U K 1 labels :=
    controlled_of_qWord U K 1 labels (by simpa using hbudget) hK
  have hroot : -n ≤ (rootExpr labels x).intercept ∧
      (rootExpr labels x).intercept ≤ n := by
    simpa only [rootExpr, startExpr] using hx
  have hc : ∀ key, 0 ≤ (rootExpr labels x).coeff key ∧
      (rootExpr labels x).coeff key ≤ (0 : ℤ) := by
    intro key
    simp [rootExpr, startExpr]
  have haux := contractionRows_bounds_aux labels (keyProof labels)
    (rootExpr labels x) 1 U K n 0
    (Int.natCast_nonneg U) (Int.natCast_nonneg K) hn (by decide)
    hcontrol hroot hc
  simpa only [contractionRoot, zero_add, mul_assoc] using haux

end Paper.F7Contraction
