import ILPEncoding.Labels.ILPChecked

/-! # Row Size Bounds
Proves bounds on offsets and step expressions (`offset_nonneg`, `offset_le_arity`, `step_coeff_nonneg_le`, `step_constant_bounds`) and the row counts `contractionRows_length` and `contractionRoot_length`.
-/

namespace Paper.F7Size

open Paper.F6ILP Paper.F6ILPRows Paper.AffineNat

theorem offset_nonneg (label : Label) :
    0 ≤ offsetConstant label := by
  unfold offsetConstant
  positivity

theorem offset_le_arity (label : Label) :
    offsetConstant label ≤ label.k := by
  unfold offsetConstant
  have hr : (label.r : ℤ) < label.k := by exact_mod_cast label.hr
  have hd : 0 ≤ (label.d : ℤ) := Int.natCast_nonneg _
  omega

theorem step_coeff_nonneg_le {keys : Finset Nat}
    (e : AffineExpr keys) (P U B : ℤ) (label : Label)
    (hk : label.k ∈ keys)
    (hP : 0 ≤ P) (hprod : P * label.k ≤ U)
    (he : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ B)
    (key : { k : Nat // k ∈ keys }) :
    0 ≤ (stepExpr e P label hk).coeff key ∧
      (stepExpr e P label hk).coeff key ≤ B + U := by
  simp only [stepExpr]
  split_ifs <;> have hpk : 0 ≤ P * (label.k : ℤ) :=
    mul_nonneg hP (Int.natCast_nonneg _)
  · constructor <;> nlinarith [he key]
  · constructor <;> nlinarith [he key]

theorem step_constant_bounds {keys : Finset Nat}
    (e : AffineExpr keys) (P U K B : ℤ) (label : Label)
    (hk : label.k ∈ keys)
    (hP : 0 ≤ P) (hprod : P * label.k ≤ U)
    (hK : (label.k : ℤ) ≤ K)
    (he : -B ≤ e.intercept ∧ e.intercept ≤ B) :
    -(B + 2 * U * K) ≤ (stepExpr e P label hk).intercept ∧
      (stepExpr e P label hk).intercept ≤ B + 2 * U * K := by
  have hU : 0 ≤ U := le_trans (mul_nonneg hP (Int.natCast_nonneg _)) hprod
  have hK0 : 0 ≤ K := le_trans (Int.natCast_nonneg _) hK
  have hoff0 := offset_nonneg label
  have hoff : offsetConstant label ≤ K :=
    le_trans (offset_le_arity label) hK
  have hr0 : 0 ≤ (label.r : ℤ) := Int.natCast_nonneg _
  have hrK : (label.r : ℤ) ≤ K := by
    have hr : (label.r : ℤ) < label.k := by exact_mod_cast label.hr
    omega
  have hPk0 : 0 ≤ P * (label.k : ℤ) := mul_nonneg hP (Int.natCast_nonneg _)
  have hpU : P ≤ U := by
    have hk1 : (1 : ℤ) ≤ label.k := by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) label.hk)
    nlinarith [mul_nonneg hP (sub_nonneg.mpr hk1)]
  have hPr : P * (label.r : ℤ) ≤ U * K := by
    calc
      P * (label.r : ℤ) ≤ U * (label.r : ℤ) :=
        mul_le_mul_of_nonneg_right hpU hr0
      _ ≤ U * K := mul_le_mul_of_nonneg_left hrK hU
  have hterm : P * (label.k : ℤ) * offsetConstant label ≤ U * K := by
    calc
      P * (label.k : ℤ) * offsetConstant label ≤
          U * offsetConstant label := mul_le_mul_of_nonneg_right hprod hoff0
      _ ≤ U * K := mul_le_mul_of_nonneg_left hoff hU
  dsimp [stepExpr]
  constructor <;> nlinarith [mul_nonneg hP hr0, mul_nonneg hPk0 hoff0]

theorem contractionRows_length {keys : Finset Nat}
    (P : ℤ) (e : AffineExpr keys) (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys) :
    (contractionRows P e labels hkeys).length = labels.length := by
  induction labels generalizing P e with
  | nil => rfl
  | cons label rest ih =>
      simp only [contractionRows, List.length_cons]
      exact congrArg Nat.succ (ih (P * label.k)
        (stepExpr e P label (hkeys label (by simp)))
        (by intro q hq; exact hkeys q (by simp [hq])))

theorem contractionRoot_length (labels : List Label) (x : ℤ) :
    (Paper.F6ILPSystem.contractionRoot labels x).length = labels.length := by
  exact contractionRows_length 1 (Paper.F6ILPCost.rootExpr labels x)
    labels (Paper.F6ILPSystem.keyProof labels)

end Paper.F7Size
