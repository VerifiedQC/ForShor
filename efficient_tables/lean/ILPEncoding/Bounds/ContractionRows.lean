import ILPEncoding.Bounds.ContractionGlobal

/-! # Contraction Row Bounds
Proves `contractionRows_bounds_aux`, bounds on every contraction row, building on the global contraction-expression bound.
-/

namespace Paper.F7Contraction

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPSystem Paper.F6ILPCost
open Paper.F7Size Paper.F7QControl Paper.AffineNat

theorem contractionRows_bounds_aux {keys : Finset Nat}
    (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (e : AffineExpr keys) (P U K B0 C0 : ℤ)
    (hU : 0 ≤ U) (hK0 : 0 ≤ K) (hB0 : 0 ≤ B0) (hC0 : 0 ≤ C0)
    (hcontrol : Controlled U K P labels)
    (he : -B0 ≤ e.intercept ∧ e.intercept ≤ B0)
    (hc : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C0) :
    (contractionRows P e labels hkeys).Forall
      (fun row =>
        -((K + 1) * (B0 + 2 * U * K * labels.length) + U) ≤ row.intercept ∧
        row.intercept ≤ (K + 1) * (B0 + 2 * U * K * labels.length) + U ∧
        (∀ key,
          -((K + 1) * (C0 + U * labels.length)) ≤ row.coeff key ∧
          row.coeff key ≤ (K + 1) * (C0 + U * labels.length))) := by
  induction labels generalizing e P B0 C0 with
  | nil => simp [contractionRows]
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      have hnext := step_constant_bounds e P U K B0 label hk
        hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 he
      have hnextCoeff := step_coeff_nonneg_le e P U C0
        label hk hcontrol.1 hcontrol.2.1 hc
      have hBK : 0 ≤ 2 * U * K := by positivity
      have hBgrow : B0 + 2 * U * K ≤
          B0 + 2 * U * K * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg hBK (Int.natCast_nonneg rest.length)]
      have hCgrow : C0 + U ≤ C0 + U * (label :: rest).length := by
        simp only [List.length_cons, Nat.cast_succ]
        nlinarith [mul_nonneg hU (Int.natCast_nonneg rest.length)]
      have hBtotal0 : 0 ≤ B0 + 2 * U * K * (label :: rest).length := by
        positivity
      have hCurrent :
          -(B0 + 2 * U * K * (label :: rest).length) ≤ e.intercept ∧
          e.intercept ≤ B0 + 2 * U * K * (label :: rest).length := by
        constructor <;> nlinarith [he.1, he.2, hBgrow]
      have hNext :
          -(B0 + 2 * U * K * (label :: rest).length) ≤ next.intercept ∧
          next.intercept ≤ B0 + 2 * U * K * (label :: rest).length := by
        constructor <;> nlinarith [hnext.1, hnext.2, hBgrow]
      have hcCurrent : ∀ key, 0 ≤ e.coeff key ∧
          e.coeff key ≤ C0 + U * (label :: rest).length := by
        intro key
        have h := hc key
        constructor <;> nlinarith [hCgrow]
      have hcNext : ∀ key, 0 ≤ next.coeff key ∧
          next.coeff key ≤ C0 + U * (label :: rest).length := by
        intro key
        have h := hnextCoeff key
        constructor <;> nlinarith [hCgrow]
      have hhead := contractionExpr_global e next P U K
        (B0 + 2 * U * K * (label :: rest).length)
        (C0 + U * (label :: rest).length) label
        hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 hBtotal0
        hCurrent hNext hcCurrent hcNext
      have htail := ih hrest next (P * label.k)
        (B0 + 2 * U * K) (C0 + U)
        (by positivity) (by positivity)
        hcontrol.2.2.2
        (by simpa only [add_assoc] using hnext)
        (by intro key; exact hnextCoeff key)
      have htail' : (contractionRows (P * label.k) next rest hrest).Forall
          (fun row =>
            -((K + 1) * (B0 + 2 * U * K * (label :: rest).length) + U) ≤
              row.intercept ∧
            row.intercept ≤
              (K + 1) * (B0 + 2 * U * K * (label :: rest).length) + U ∧
            (∀ key,
              -((K + 1) * (C0 + U * (label :: rest).length)) ≤
                row.coeff key ∧
              row.coeff key ≤ (K + 1) *
                (C0 + U * (label :: rest).length))) := by
        convert htail using 1 <;>
          simp only [List.length_cons, Nat.cast_succ] <;> ring
      simpa only [contractionRows, List.forall_cons] using
        And.intro hhead htail'

end Paper.F7Contraction

