import ILPEncoding.Bounds.BudgetActual
import ILPEncoding.Bounds.BudgetLeaf

/-! # Budget Root Magnitude
Proves `budgetRoot_bound`, a magnitude bound on the budget root expression, combining the actual-word budget bounds with the leaf budget-row bounds.
-/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.AffineNat Paper.AffineILP Paper.F7QControl Paper.F7Products Paper.PPEndToEnd

theorem budgetRoot_bound (labels : List Label) (x z : ℤ)
    (c : Nat → Nat) (price : Nat → Nat)
    (T U K H n L : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hcap : ∀ label ∈ labels, c label.k ≤ H)
    (hx : -(n : ℤ) ≤ x ∧ x ≤ n)
    (hT : T ≤ U)
    (hLeaf : leafPP price (finalN 1 labels) z.toNat ≤ L) :
    let S : Nat := labels.length *
      (8 * U * H * U *
        (n + 2 * U * K * labels.length + 1));
    let R : Nat := labels.length *
      (8 * U * H * U * (U * labels.length));
    -((U : ℤ) * (U + L) + S) ≤
        (budgetRow labels x z c price 1 T).intercept ∧
      (budgetRow labels x z c price 1 T).intercept ≤
        (U : ℤ) * (U + L) + S ∧
      (∀ key, -(R : ℤ) ≤ (budgetRow labels x z c price 1 T).coeff key ∧
        (budgetRow labels x z c price 1 T).coeff key ≤ R) := by
  have hD := terminalProduct_le_typed_budget U (fun _ => 0)
    labels hbudget
  have hCleared := clearedRoot_bound labels x c U K H n
    hbudget hK hcap hx
  have hCleared' :
      -((labels.length *
        (8 * U * H * U * (n + 2 * U * K * labels.length + 1)) : Nat) : ℤ) ≤
          (clearedExpr
            (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
            c 1 1 (rootExpr labels x) labels (keyProof labels)).intercept ∧
      (clearedExpr
        (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
        c 1 1 (rootExpr labels x) labels (keyProof labels)).intercept ≤
          (labels.length *
            (8 * U * H * U * (n + 2 * U * K * labels.length + 1)) : Nat) ∧
      (∀ key,
        -((labels.length * (8 * U * H * U * (U * labels.length)) : Nat) : ℤ) ≤
          (clearedExpr
            (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
            c 1 1 (rootExpr labels x) labels (keyProof labels)).coeff key ∧
        (clearedExpr
          (terminalProduct 1 (labels.map (instantiate (fun _ => 0))))
          c 1 1 (rootExpr labels x) labels (keyProof labels)).coeff key ≤
            (labels.length * (8 * U * H * U * (U * labels.length)) : Nat)) := by
    simpa only [AbsBound, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using hCleared
  exact budgetRow_bounds_from_cleared labels x z c price 1 T U L
    (labels.length *
      (8 * U * H * U * (n + 2 * U * K * labels.length + 1)))
    (labels.length * (8 * U * H * U * (U * labels.length)))
    hD hT hLeaf hCleared'

end Paper.F7Budget
