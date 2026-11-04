import ILPEncoding.Bounds.BudgetCanonical
import ILPEncoding.Bounds.SystemNumeric

/-! # Canonical Matrix Bit Bound
Proves `canonical_matrix_bits_uniform`, an explicit finite binary encoding bound for the canonical leaf price. The budget-row envelope is derived from the actual q-word budget and the minimum-charge label cap; no coefficient oracle remains.
-/

set_option autoImplicit false

namespace Paper.F7MatrixFinal

open Paper.AffineNat Paper.F6ILP Paper.F6ILPSystem
open Paper.F7QControl Paper.F7Computable Paper.F7Encoding
open Paper.F7Budget Paper.F7System
open Paper.PPEndToEnd
open Paper.CountStage.StopBudget

/-- Explicit finite binary encoding bound for the canonical leaf price.
The budget-row envelope is derived from the actual q-word budget and
the minimum-charge label cap; no coefficient oracle remains. -/
theorem canonical_matrix_bits_uniform
    (labels : List Label) (x z : ℤ)
    (c lo hi : Nat → Nat) (T U K n : Nat)
    (hbudget : qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K)
    (hlabelCap : ∀ label ∈ labels, label.c ≤ 27 * label.k ^ 3)
    (hshared : ∀ label ∈ labels, label.c = c label.k)
    (hx : -(n : ℤ) ≤ x ∧ x ≤ n)
    (hz : 0 ≤ z ∧ z ≤ U)
    (hT : T ≤ U)
    (hlohi : ∀ key ∈ usedKeys labels,
      lo key.val ≤ n ∧ hi key.val ≤ n) :
    matrixBits (systemRowsC labels x z c lo hi Paper.PPEndToEnd.tauExact 1 T) ≤
      (3 * U + 3) * (U + 1) *
        (numericMagnitudeUniform U K n + 2) := by
  have hb := budgetRoot_canonical_bound labels x z c T U K n
    hbudget hK hlabelCap hshared hx hz hT
  have hbI :
      -((budgetA U K n labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ∧
      (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).intercept ≤
        budgetA U K n labels.length := by
    simpa only [budgetA, budgetS, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat] using And.intro hb.1 hb.2.1
  have hbC : ∀ key,
      -((budgetR U K labels.length : Nat) : ℤ) ≤
        (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ∧
      (budgetRow labels x z c Paper.PPEndToEnd.tauExact 1 T).coeff key ≤
        budgetR U K labels.length := by
    intro key
    simpa only [budgetR, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add, Nat.cast_ofNat] using hb.2.2 key
  have hbits := systemRowsC_numericBits_le labels x z c lo hi
    Paper.PPEndToEnd.tauExact T U K n hbudget hK hx hz hlohi hbI hbC
  exact systemRowsC_numericBits_uniform labels x z c lo hi
    Paper.PPEndToEnd.tauExact T U K n hbudget hbits

end Paper.F7MatrixFinal
