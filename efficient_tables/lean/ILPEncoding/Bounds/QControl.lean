import ILPEncoding.Bounds.Global
import ILPEncoding.Labels.Typed

/-! # Q-Word Control
Defines `qWord`, the product of `2 * label.k - 1` over a label list. Proves `qWord_pos`, `qWord_eq_typed` relating it to the typed count budget, and the control statements `controlled_of_qWord` and `controlled_root_of_typed_budget`.
-/

namespace Paper.F7QControl

open Paper.AffineNat Paper.F7Size
open Paper.CountStage.TypedDecorationWords Paper.F6TypedBridge

def qWord : List Label → Nat
  | [] => 1
  | label :: rest => (2 * label.k - 1) * qWord rest

theorem qWord_pos (labels : List Label) : 1 ≤ qWord labels := by
  induction labels with
  | nil => simp [qWord]
  | cons label rest ih =>
      have hq : 1 ≤ 2 * label.k - 1 := by
        have hk := label.hk
        omega
      simpa only [qWord] using Nat.mul_le_mul hq ih

theorem qWord_eq_typed (labels : List Label) :
    qWord labels = qProduct labelQ (labels.map toTyped) := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
      simp only [qWord, List.map_cons, qProduct, List.prod_cons]
      simp only [labelQ, toTyped]
      exact congrArg (fun n => (2 * label.k - 1) * n) ih

theorem controlled_of_qWord (U K P : Nat) (labels : List Label)
    (hbudget : P * qWord labels ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K) :
    Controlled U K P labels := by
  induction labels generalizing P with
  | nil => simp [Controlled]
  | cons label rest ih =>
      have hq : label.k ≤ 2 * label.k - 1 := by
        have hk := label.hk
        omega
      have hfull : P * (2 * label.k - 1) * qWord rest ≤ U := by
        simpa only [qWord, mul_assoc] using hbudget
      have hfactor : (P * label.k) * qWord rest ≤
          P * (2 * label.k - 1) * qWord rest := by
        have h := Nat.mul_le_mul_left P
          (Nat.mul_le_mul_right (qWord rest) hq)
        simpa only [mul_assoc] using h
      have htailbudget : (P * label.k) * qWord rest ≤ U :=
        le_trans hfactor hfull
      have hprod : P * label.k ≤ U := by
        have h := Nat.mul_le_mul_left (P * label.k) (qWord_pos rest)
        have hh : P * label.k ≤ (P * label.k) * qWord rest := by
          simpa only [mul_one] using h
        exact le_trans hh htailbudget
      have htailK : ∀ q ∈ rest, q.k ≤ K := by
        intro q hqmem
        exact hK q (by simp [hqmem])
      refine ⟨by exact_mod_cast (Nat.zero_le P), ?_, ?_, ?_⟩
      · exact_mod_cast hprod
      · exact_mod_cast hK label (by simp)
      · exact ih (P * label.k) htailbudget htailK

theorem controlled_root_of_typed_budget (U K : Nat)
    (labels : List Label)
    (hbudget : qProduct labelQ (labels.map toTyped) ≤ U)
    (hK : ∀ label ∈ labels, label.k ≤ K) :
    Controlled U K 1 labels := by
  apply controlled_of_qWord U K 1 labels
  · simpa only [one_mul, qWord_eq_typed] using hbudget
  · exact hK

end Paper.F7QControl
