import ILPEncoding.Bounds.QControl

/-! # Word Products
Defines `kWord` and proves `kWord_le_qWord`. Relates the terminal product to it (`terminalProduct_eq_kWord`, `terminalProduct_le_typed_budget`) and bounds the final multiplicity (`finalN_eq_qWord`, `finalN_le_budget`).
-/

namespace Paper.F7Products

open Paper.AffineNat Paper.AffineILP Paper.F6Objective
open Paper.F7QControl

def kWord : List Label → Nat
  | [] => 1
  | label :: rest => label.k * kWord rest

theorem kWord_le_qWord (labels : List Label) :
    kWord labels ≤ qWord labels := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
      have hk := label.hk
      have hfactor : label.k ≤ 2 * label.k - 1 := by omega
      calc
        kWord (label :: rest) = label.k * kWord rest := rfl
        _ ≤ label.k * qWord rest := Nat.mul_le_mul_left _ ih
        _ ≤ (2 * label.k - 1) * qWord rest :=
          Nat.mul_le_mul_right _ hfactor
        _ = qWord (label :: rest) := rfl

theorem terminalProduct_eq_kWord (P : ℤ) (a : Nat → Nat)
    (labels : List Label) :
    terminalProduct P (labels.map (Paper.AffineNat.instantiate a)) =
      P * (kWord labels : ℤ) := by
  induction labels generalizing P with
  | nil => simp [terminalProduct, kWord]
  | cons label rest ih =>
      change terminalProduct (P * label.k)
          (rest.map (Paper.AffineNat.instantiate a)) =
        P * (kWord (label :: rest) : ℤ)
      rw [ih (P * label.k)]
      simp only [kWord, Nat.cast_mul]
      ring

theorem terminalProduct_le_typed_budget (U : Nat) (a : Nat → Nat)
    (labels : List Label)
    (hbudget : qWord labels ≤ U) :
    terminalProduct 1 (labels.map (Paper.AffineNat.instantiate a)) ≤ U := by
  rw [terminalProduct_eq_kWord]
  norm_num
  exact_mod_cast (le_trans (kWord_le_qWord labels) hbudget)

theorem finalN_eq_qWord (N : Nat) (labels : List Label) :
    finalN N labels = N * qWord labels := by
  induction labels generalizing N with
  | nil => simp [finalN, qWord]
  | cons label rest ih =>
      change finalN (N * (2 * (label.k - 1) + 1)) rest =
        N * qWord (label :: rest)
      rw [ih]
      have hk := label.hk
      have hq : 2 * (label.k - 1) + 1 = 2 * label.k - 1 := by omega
      rw [hq]
      simp [qWord, mul_assoc]

theorem finalN_le_budget (labels : List Label) (U : Nat)
    (hbudget : qWord labels ≤ U) :
    finalN 1 labels ≤ U := by
  simpa only [finalN_eq_qWord, one_mul] using hbudget

end Paper.F7Products
