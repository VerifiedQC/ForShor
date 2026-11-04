import ILPEncoding.Bounds.QControl
import ILPEncoding.Bounds.ComputableRows

/-! # Word Size versus Q-Word
Proves `qWord_eq_typedProduct`, that the typed count budget equals the affine-word prefix budget, and `length_le_qWord`, since every label contributes a qWord factor at least three. Also proves `variable_card_le_length` and the combined `length_and_variable_card_le_of_qWord_bound`.
-/

namespace Paper.F7WordSize

open Paper.AffineNat Paper.F6ILP Paper.F7QControl
open Paper.CountStage.TypedDecorationWords Paper.F6TypedBridge

/-- The typed count budget is exactly the same product as the affine-word
prefix budget, after applying the existing label encoding. -/
theorem qWord_eq_typedProduct (labels : List Label) :
    qWord labels = qProduct labelQ (labels.map toTyped) :=
  Paper.F7QControl.qWord_eq_typed labels

/-- Every label contributes a qWord factor at least three, so the product
strictly dominates the number of labels. -/
theorem length_add_one_le_qWord (labels : List Label) :
    labels.length + 1 ≤ qWord labels := by
  induction labels with
  | nil => simp [qWord]
  | cons label rest ih =>
      have hk := label.hk
      have hfactor : 3 ≤ 2 * label.k - 1 := by omega
      have hsmall : rest.length + 2 ≤ 3 * (rest.length + 1) := by
        nlinarith
      have hlarge : 3 * (rest.length + 1) ≤
          (2 * label.k - 1) * qWord rest :=
        Nat.mul_le_mul hfactor ih
      simpa only [List.length_cons, qWord] using le_trans hsmall hlarge

theorem length_le_qWord (labels : List Label) :
    labels.length ≤ qWord labels := by
  have h := length_add_one_le_qWord labels
  omega

/-- `Variable` indexes the distinct arities in the label list, so its
cardinality cannot exceed the list length. -/
theorem variable_card_le_length (labels : List Label) :
    Fintype.card (Variable labels) ≤ labels.length := by
  rw [Paper.F6ILP.variable_count, usedArities]
  have h := List.toFinset_card_le (labels.map Label.k)
  simpa only [List.length_map] using h

theorem length_and_variable_card_le_of_qWord_bound
    (labels : List Label) (U : Nat)
    (hbudget : qWord labels ≤ U) :
    labels.length ≤ U ∧ Fintype.card (Variable labels) ≤ U := by
  have hlength : labels.length ≤ U :=
    (length_le_qWord labels).trans hbudget
  exact ⟨hlength, (variable_card_le_length labels).trans hlength⟩

end Paper.F7WordSize
