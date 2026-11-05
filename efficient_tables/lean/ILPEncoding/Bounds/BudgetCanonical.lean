import ILPEncoding.Bounds.BudgetMagnitude
import ILPEncoding.Bounds.LeafCanon

/-! # Canonical Budget Root Bound
Proves `budgetRoot_canonical_bound`, a bound on the budget-row root expression for the canonical leaf price, obtained by combining the budget-magnitude and canonical-leaf bounds.
-/

set_option autoImplicit false

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.F6Objective Paper.AffineNat Paper.F7QControl
open Paper.PPEndToEnd Paper.CountStage.StopBudget Paper.F7LeafCanon

theorem budgetRoot_canonical_bound (labels : List Label) (x z : ℤ)
    (c : Nat → Nat) (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hlabelCap : ∀ label ∈ labels, label.c ≤ 27 * label.k ^ 3)
    (hshared : ∀ label ∈ labels, label.c = c label.k)
    (hx : -(n : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hT : T ≤ U) :
    let H : Nat := 27 * K ^ 3;
    let L : Nat := 2004 * (U + 1) ^ 6;
    let S : Nat := labels.length *
      (8 * U * H * U * (n + 2 * U * K * labels.length + 1));
    let R : Nat := labels.length * (8 * U * H * U * (U * labels.length));
    -((U : ℤ) * (U + L) + S) ≤
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ∧
      (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ≤
        (U : ℤ) * (U + L) + S ∧
      (∀ key, -(R : ℤ) ≤ (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ∧
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ≤ R) := by
  have hzNat : z.toNat ≤ U := by omega
  have hleaf := canonical_leaf_bound labels U z.toNat hbudget hzNat
  have hcap := shared_charge_cap labels c K hK hlabelCap hshared
  exact budgetRoot_bound labels x z c Paper.PPEndToEnd.tauExact T U K
    (27 * K ^ 3) n (2004 * (U + 1) ^ 6)
    hbudget hK hcap hx hT hleaf

end Paper.F7Budget
