import ILPEncoding.Bounds.Terminal

/-! # Budget Sum Bounds
Defines `AbsBound` (absolute-value bounds on an affine expression) and `TermBounded`. Proves `absBound_add` and `clearedExpr_sum_bound`, a bound on the cleared-expression sum.
-/

namespace Paper.F7Budget

open Paper.F6ILP Paper.F6ILPRows Paper.F6ILPCost Paper.F6ILPSystem
open Paper.AffineNat

def AbsBound {keys : Finset Nat} (e : AffineExpr keys) (A C : ℤ) : Prop :=
  -A ≤ e.intercept ∧ e.intercept ≤ A ∧
    ∀ key, -C ≤ e.coeff key ∧ e.coeff key ≤ C

theorem absBound_add {keys : Finset Nat} (e f : AffineExpr keys)
    (A B C D : ℤ) (he : AbsBound e A C)
    (hf : AbsBound f B D) :
    AbsBound (addExpr e f) (A + B) (C + D) := by
  unfold AbsBound at *
  simp only [addExpr]
  constructor
  · omega
  constructor
  · omega
  · intro key
    have hec := he.2.2 key
    have hfc := hf.2.2 key
    constructor <;> omega

def TermBounded {keys : Finset Nat}
    (D : ℤ) (c : Nat → Nat) (A C : ℤ)
    (N : Nat) (P : ℤ) (e : AffineExpr keys) :
    (labels : List Label) →
    (∀ label ∈ labels, label.k ∈ keys) → Prop
  | [], _ => True
  | label :: rest, hkeys =>
      let next := stepExpr e P label (hkeys label (by simp))
      let term := scaleExpr (8 * (N : ℤ) * (c label.k : ℤ))
        (subExpr (scaleExpr (D / (P * label.k)) next)
          (startExpr keys D))
      AbsBound term A C ∧
        TermBounded D c A C (N * (2 * (label.k - 1) + 1))
          (P * label.k) next rest
          (by intro q hq; exact hkeys q (by simp [hq]))

theorem clearedExpr_sum_bound {keys : Finset Nat}
    (D : ℤ) (c : Nat → Nat) (A C : ℤ)
    (N : Nat) (P : ℤ) (e : AffineExpr keys)
    (labels : List Label)
    (hkeys : ∀ label ∈ labels, label.k ∈ keys)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hterms : TermBounded D c A C N P e labels hkeys) :
    AbsBound (clearedExpr D c N P e labels hkeys)
      (labels.length * A) (labels.length * C) := by
  induction labels generalizing N P e with
  | nil =>
      simp [clearedExpr, AbsBound, startExpr, hA, hC]
  | cons label rest ih =>
      let hk := hkeys label (by simp)
      let next := stepExpr e P label hk
      let hrest : ∀ q ∈ rest, q.k ∈ keys := by
        intro q hq
        exact hkeys q (by simp [hq])
      let term := scaleExpr (8 * (N : ℤ) * (c label.k : ℤ))
        (subExpr (scaleExpr (D / (P * label.k)) next)
          (startExpr keys D))
      have hhead : AbsBound term A C := hterms.1
      have htail := ih (N * (2 * (label.k - 1) + 1))
        (P * label.k) next hrest hterms.2
      have hadd := absBound_add term
        (clearedExpr D c (N * (2 * (label.k - 1) + 1))
          (P * label.k) next rest hrest)
        A (rest.length * A) C (rest.length * C) hhead htail
      convert hadd using 1 <;>
        simp only [clearedExpr, List.length_cons, Nat.cast_succ] <;> ring

end Paper.F7Budget
