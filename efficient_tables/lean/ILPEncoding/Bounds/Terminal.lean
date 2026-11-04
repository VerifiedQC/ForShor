import ILPEncoding.Bounds.Products

/-! # Terminal Row Bounds
Proves `terminalRow_bounds`, bounds on the coefficients and constant of the terminal row of the encoding for a label list.
-/

namespace Paper.F7Terminal

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F7Size Paper.F7QControl Paper.F7Products Paper.AffineNat
open Paper.AffineILP

theorem terminalRow_bounds (labels : List Label) (x z : ℤ)
    (a : Nat → Nat) (U K : Nat) (n : ℤ)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hx : -n ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U) :
    -(n + 2 * (U : ℤ) * K * labels.length + (U : ℤ) * U) ≤ (terminalRow labels x z).intercept ∧
      (terminalRow labels x z).intercept ≤ n + 2 * (U : ℤ) * K * labels.length + (U : ℤ) * U ∧
      (∀ key, 0 ≤ (terminalRow labels x z).coeff key ∧
        (terminalRow labels x z).coeff key ≤ (U : ℤ) * labels.length) := by
  let E := terminalExpr 1 (rootExpr labels x) labels (keyProof labels)
  let D := terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a))
  have hcontrol : Controlled U K 1 labels :=
    controlled_root_of_typed_budget U K labels
      (by simpa only [← qWord_eq_typed] using hbudget) hK
  have hroot : -(n : ℤ) ≤ (rootExpr labels x).intercept ∧
      (rootExpr labels x).intercept ≤ n := by
    simpa only [rootExpr, startExpr] using hx
  have hzero : ∀ key, 0 ≤ (rootExpr labels x).coeff key ∧
      (rootExpr labels x).coeff key ≤ (0 : ℤ) := by
    intro key
    simp [rootExpr, startExpr]
  have hE := terminalExpr_bounds (rootExpr labels x) 1 U K n 0
    labels (keyProof labels) hcontrol hroot hzero
  have hE' :
      -(n + 2 * (U : ℤ) * K * labels.length) ≤ E.intercept ∧
      E.intercept ≤ n + 2 * (U : ℤ) * K * labels.length ∧
      (∀ key, 0 ≤ E.coeff key ∧
        E.coeff key ≤ (U : ℤ) * labels.length) := by
    simpa only [E, interceptGrowth_eq_length,
      coeffGrowth_eq_length, zero_add] using hE
  have hD0 : 0 ≤ D := le_of_lt (Paper.F6Cleared.terminalProduct_pos
    1 _ (by decide))
  have hDU : D ≤ U := terminalProduct_le_typed_budget U a labels hbudget
  have hDfix : D = terminalProduct 1
      (labels.map (Paper.AffineNat.instantiate (fun _ => 0))) := by
    exact Paper.F6ILPCost.terminalProduct_independent 1 labels a (fun _ => 0)
  have hDz : 0 ≤ D * z ∧ D * z ≤ (U : ℤ) * U := by
    constructor
    · exact mul_nonneg hD0 hz.1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hDU) hz.1,
        mul_nonneg (Int.natCast_nonneg U) (sub_nonneg.mpr hz.2)]
  have hrow : (terminalRow labels x z).intercept = E.intercept - D * z := by
    simp [terminalRow, E, subExpr, startExpr, ← hDfix]
  have hcoeff : ∀ key, (terminalRow labels x z).coeff key = E.coeff key := by
    intro key
    simp [terminalRow, E, subExpr, startExpr]
  constructor
  · rw [hrow]
    nlinarith [hE'.1, hDz.2]
  constructor
  · rw [hrow]
    nlinarith [hE'.2.1, hDz.1]
  · intro key
    rw [hcoeff]
    exact hE'.2.2 key

end Paper.F7Terminal

