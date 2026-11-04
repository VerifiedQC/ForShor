import ILPEncoding.Bounds.Size

/-! # Global Growth Bounds
Defines `Controlled`, `interceptGrowth` and `coeffGrowth` for label lists. Proves `terminalExpr_bounds`, bounds on the terminal expression, together with `interceptGrowth_eq_length` and `coeffGrowth_eq_length`.
-/

namespace Paper.F7Size

open Paper.F6ILP Paper.F6ILPRows Paper.AffineNat

def Controlled (U K P : ℤ) : List Label → Prop
  | [] => 0 ≤ P
  | label :: rest =>
      0 ≤ P ∧ P * label.k ≤ U ∧ (label.k : ℤ) ≤ K ∧
        Controlled U K (P * label.k) rest

def interceptGrowth (U K : ℤ) : List Label → ℤ
  | [] => 0
  | _ :: rest => 2 * U * K + interceptGrowth U K rest

def coeffGrowth (U : ℤ) : List Label → ℤ
  | [] => 0
  | _ :: rest => U + coeffGrowth U rest

theorem terminalExpr_bounds {keys : Finset Nat}
    (e : AffineExpr keys) (P U K B C : ℤ)
    (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (hcontrol : Controlled U K P labels)
    (hintercept : -B ≤ e.intercept ∧ e.intercept ≤ B)
    (hcoeff : ∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C) :
    let result := terminalExpr P e labels hkeys;
    -(B + interceptGrowth U K labels) ≤ result.intercept ∧
      result.intercept ≤ B + interceptGrowth U K labels ∧
      (∀ key, 0 ≤ result.coeff key ∧
        result.coeff key ≤ C + coeffGrowth U labels) := by
  induction labels generalizing P e B C with
  | nil =>
      have h : -B ≤ e.intercept ∧ e.intercept ≤ B ∧
          (∀ key, 0 ≤ e.coeff key ∧ e.coeff key ≤ C) :=
        ⟨hintercept.1, hintercept.2, hcoeff⟩
      simpa [terminalExpr, interceptGrowth, coeffGrowth] using h
  | cons label rest ih =>
      have hk : label.k ∈ keys := hkeys label (by simp)
      have htail : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      have hsintercept := step_constant_bounds e P U K B label hk
        hcontrol.1 hcontrol.2.1 hcontrol.2.2.1 hintercept
      have hscoeff := step_coeff_nonneg_le e P U C label hk
        hcontrol.1 hcontrol.2.1 hcoeff
      have hresult := ih (stepExpr e P label hk) (P * label.k)
        (B + 2 * U * K) (C + U) htail hcontrol.2.2.2
        hsintercept hscoeff
      simpa only [terminalExpr, interceptGrowth, coeffGrowth,
        add_assoc] using hresult

theorem interceptGrowth_eq_length (U K : ℤ) (labels : List Label) :
    interceptGrowth U K labels =
      2 * U * K * labels.length := by
  induction labels with
  | nil => simp [interceptGrowth]
  | cons label rest ih =>
      simp only [interceptGrowth, List.length_cons, Nat.cast_succ, ih]
      ring

theorem coeffGrowth_eq_length (U : ℤ) (labels : List Label) :
    coeffGrowth U labels = U * labels.length := by
  induction labels with
  | nil => simp [coeffGrowth]
  | cons label rest ih =>
      simp only [coeffGrowth, List.length_cons, Nat.cast_succ, ih]
      ring

end Paper.F7Size
