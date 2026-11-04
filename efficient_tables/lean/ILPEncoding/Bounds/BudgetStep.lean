import ILPEncoding.Bounds.BudgetSum

/-! # Budget Step Bound
Proves `clearedTerm_bound`, a bound on one cleared term of the budget sum, to be fed into the sum bounds of `BudgetSum`.
-/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.AffineNat

theorem clearedTerm_bound {keys : Finset Nat}
    (next : AffineExpr keys) (D Q : ℤ)
    (N c U H B C : Nat)
    (hD : 0 ≤ D ∧ D ≤ U)
    (hQ : 0 ≤ Q ∧ Q ≤ U)
    (hN : N ≤ U) (hc : c ≤ H)
    (hB :
      -((B : Nat) : ℤ) ≤ next.intercept ∧ next.intercept ≤ B)
    (hC : ∀ key, 0 ≤ next.coeff key ∧ next.coeff key ≤ C) :
    AbsBound
      (scaleExpr (8 * (N : ℤ) * c)
        (subExpr (scaleExpr Q next) (startExpr keys D)))
      (8 * (U : ℤ) * H * U * (B + 1))
      (8 * (U : ℤ) * H * U * C) := by
  have hU : 0 ≤ (U : ℤ) := Int.natCast_nonneg _
  have hH : 0 ≤ (H : ℤ) := Int.natCast_nonneg _
  have hBn : 0 ≤ (B : ℤ) := Int.natCast_nonneg _
  have hCn : 0 ≤ (C : ℤ) := Int.natCast_nonneg _
  have hN0 : 0 ≤ (N : ℤ) := Int.natCast_nonneg _
  have hc0 : 0 ≤ (c : ℤ) := Int.natCast_nonneg _
  have hNle : (N : ℤ) ≤ U := by exact_mod_cast hN
  have hcle : (c : ℤ) ≤ H := by exact_mod_cast hc
  let S : ℤ := 8 * N * c
  let Smax : ℤ := 8 * U * H
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hSle : S ≤ Smax := by
    have h1 : (N : ℤ) * c ≤ U * c :=
      mul_le_mul_of_nonneg_right hNle hc0
    have h2 : (U : ℤ) * c ≤ U * H :=
      mul_le_mul_of_nonneg_left hcle hU
    dsimp [S, Smax]
    nlinarith
  have hinner : -(U * (B + 1) : ℤ) ≤ Q * next.intercept - D ∧
      Q * next.intercept - D ≤ U * (B + 1) := by
    have hqplus := mul_nonneg hQ.1 (sub_nonneg.mpr hB.2)
    have hqminus := mul_nonneg hQ.1 (sub_nonneg.mpr hB.1)
    have hqU := mul_nonneg (sub_nonneg.mpr hQ.2) hBn
    constructor <;> nlinarith
  have hinnerCoeff : ∀ key, 0 ≤ Q * next.coeff key ∧
      Q * next.coeff key ≤ (U : ℤ) * C := by
    intro key
    constructor
    · exact mul_nonneg hQ.1 (hC key).1
    · nlinarith [mul_nonneg hQ.1 (sub_nonneg.mpr (hC key).2),
        mul_nonneg (sub_nonneg.mpr hQ.2) hCn]
  unfold AbsBound
  dsimp [scaleExpr, subExpr, startExpr]
  constructor
  · nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hinner.1),
      mul_nonneg (sub_nonneg.mpr hSle) (by positivity : 0 ≤ (U : ℤ) * (B + 1))]
  constructor
  · nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hinner.2),
      mul_nonneg (sub_nonneg.mpr hSle) (by positivity : 0 ≤ (U : ℤ) * (B + 1))]
  · intro key
    have hk := hinnerCoeff key
    constructor
    · nlinarith [mul_nonneg hS0 hk.1]
    · nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hk.2),
        mul_nonneg (sub_nonneg.mpr hSle) (by positivity : 0 ≤ (U : ℤ) * C)]

end Paper.F7Budget
