import ILPEncoding.Bounds.Terminal

/-! # Budget Row Bounds from Cleared Bounds
Proves `budgetRow_bounds_from_cleared`: bounds on the budget row follow from bounds on the cleared root expression together with the terminal row bounds.
-/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.AffineNat Paper.AffineILP Paper.PPEndToEnd

theorem budgetRow_bounds_from_cleared
    (labels : List Label) (x z : ℤ) (c : Nat → Nat)
    (price : Nat → Nat) (N T U L S R : Nat)
    (hD : terminalProduct 1
      (labels.map (instantiate (fun _ => 0))) ≤ U)
    (hT : T ≤ U)
    (hLeaf : leafPP price (finalN N labels) z.toNat ≤ L)
    (hCleared :
      -(S : ℤ) ≤
        (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c N 1 (rootExpr labels x) labels (keyProof labels)).intercept ∧
      (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
        c N 1 (rootExpr labels x) labels (keyProof labels)).intercept ≤ S ∧
      (∀ key, -(R : ℤ) ≤
        (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c N 1 (rootExpr labels x) labels (keyProof labels)).coeff key ∧
        (clearedExpr (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c N 1 (rootExpr labels x) labels (keyProof labels)).coeff key ≤ R)) :
    -((U : ℤ) * (U + L) + S) ≤
        (budgetRow labels x z c price N T).intercept ∧
      (budgetRow labels x z c price N T).intercept ≤
        (U : ℤ) * (U + L) + S ∧
      (∀ key, -(R : ℤ) ≤ (budgetRow labels x z c price N T).coeff key ∧
        (budgetRow labels x z c price N T).coeff key ≤ R) := by
  let D := terminalProduct 1 (labels.map (instantiate (fun _ => 0)))
  let leaf := leafPP price (finalN N labels) z.toNat
  let e := clearedExpr D c N 1 (rootExpr labels x)
    labels (keyProof labels)
  have hD0 : 0 ≤ D := le_of_lt (Paper.F6Cleared.terminalProduct_pos
    1 _ (by decide))
  have hDle : D ≤ (U : ℤ) := hD
  have hT0 : 0 ≤ (T : ℤ) := Int.natCast_nonneg _
  have hTle : (T : ℤ) ≤ U := by exact_mod_cast hT
  have hL0 : 0 ≤ (leaf : ℤ) := Int.natCast_nonneg _
  have hLle : (leaf : ℤ) ≤ L := by exact_mod_cast hLeaf
  have hroot : -((U : ℤ) * (U + L)) ≤ D * ((T : ℤ) - leaf) ∧
      D * ((T : ℤ) - leaf) ≤ (U : ℤ) * (U + L) := by
    constructor
    · nlinarith [mul_nonneg hD0 hT0,
        mul_nonneg (sub_nonneg.mpr hDle) hL0,
        mul_nonneg (Int.natCast_nonneg U) (sub_nonneg.mpr hLle)]
    · nlinarith [mul_nonneg hD0 hL0,
        mul_nonneg (sub_nonneg.mpr hDle) hT0,
        mul_nonneg (Int.natCast_nonneg U) (sub_nonneg.mpr hTle)]
  have he : -(S : ℤ) ≤ e.intercept ∧ e.intercept ≤ S ∧
      (∀ key, -(R : ℤ) ≤ e.coeff key ∧ e.coeff key ≤ R) := hCleared
  have hBudgetInt : (budgetRow labels x z c price N T).intercept =
      D * ((T : ℤ) - leaf) - e.intercept := by
    simp only [budgetRow, subExpr, startExpr]
    rfl
  have hBudgetCoeff : ∀ key,
      (budgetRow labels x z c price N T).coeff key = -e.coeff key := by
    intro key
    simp only [budgetRow, subExpr, startExpr, zero_sub]
    rfl
  constructor
  · rw [hBudgetInt]
    omega
  constructor
  · rw [hBudgetInt]
    omega
  · intro key
    have h := he.2.2 key
    rw [hBudgetCoeff]
    constructor <;> omega

end Paper.F7Budget

