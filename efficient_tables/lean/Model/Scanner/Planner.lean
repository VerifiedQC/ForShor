import Model.Defs

/-!
# Planner profile transfer

Shows that tables with equal used peaks behave identically for the planner. Proves preservation of the child width, width trace, final state and strict-contraction legality (`childWidth_eq_of_peaks`, `finalState_eq_of_used_peaks`, `strictlyContracts_transfer`), a cost comparison `planCost_le_of_used_peaks_and_charges`, and the counterexample `profile_3_residue_wrap_counterexample`.
-/

namespace Paper.Planner

/-- Peak equality is exactly the condition needed to preserve a child width. -/
theorem childWidth_eq_of_peaks {k w : Nat} {p q : Profile}
    (ha : p.peakA = q.peakA) (hb : p.peakB = q.peakB) :
    childWidth k p w = childWidth k q w := by
  simp [childWidth, ha, hb]

/-- A fixed arity list and equal used peaks give the same complete width trace. -/
theorem widthTrace_eq_of_used_peaks
    (p q : Nat → Profile) (arities : List Nat) (w : Nat)
    (ha : ∀ k, k ∈ arities → (p k).peakA = (q k).peakA)
    (hb : ∀ k, k ∈ arities → (p k).peakB = (q k).peakB) :
    widthTrace p arities w = widthTrace q arities w := by
  induction arities generalizing w with
  | nil => rfl
  | cons k ks ih =>
      have hka := ha k (by simp)
      have hkb := hb k (by simp)
      have hw := childWidth_eq_of_peaks (k := k) (w := w) hka hkb
      simp only [widthTrace]
      rw [hw]
      congr 1
      apply ih
      · intro j hj
        exact ha j (by simp [hj])
      · intro j hj
        exact hb j (by simp [hj])

/-- Equal used peaks preserve the final multiplicity and width. -/
theorem finalState_eq_of_used_peaks
    (p q : Nat → Profile) (arities : List Nat) (n w : Nat)
    (ha : ∀ k, k ∈ arities → (p k).peakA = (q k).peakA)
    (hb : ∀ k, k ∈ arities → (p k).peakB = (q k).peakB) :
    finalState p arities n w = finalState q arities n w := by
  induction arities generalizing n w with
  | nil => rfl
  | cons k ks ih =>
      have hka := ha k (by simp)
      have hkb := hb k (by simp)
      have hw := childWidth_eq_of_peaks (k := k) (w := w) hka hkb
      change finalState p ks (n * (2 * k - 1)) (childWidth k (p k) w) =
        finalState q ks (n * (2 * k - 1)) (childWidth k (q k) w)
      rw [hw]
      apply ih
      · intro j hj
        exact ha j (by simp [hj])
      · intro j hj
        exact hb j (by simp [hj])

/-- Exact profile agreement preserves strict-contraction legality at every step. -/
theorem strictlyContracts_transfer
    (p q : Nat → Profile) (arities : List Nat) (w : Nat)
    (ha : ∀ k, k ∈ arities → (p k).peakA = (q k).peakA)
    (hb : ∀ k, k ∈ arities → (p k).peakB = (q k).peakB)
    (h : StrictlyContracts p arities w) :
    StrictlyContracts q arities w := by
  induction arities generalizing w with
  | nil => exact h
  | cons k ks ih =>
      have hka := ha k (by simp)
      have hkb := hb k (by simp)
      have hw := childWidth_eq_of_peaks (k := k) (w := w) hka hkb
      rcases h with ⟨hhead, htail⟩
      change childWidth k (q k) w < w ∧
        StrictlyContracts q ks (childWidth k (q k) w)
      constructor
      · simpa [hw] using hhead
      · rw [← hw]
        apply ih
        · intro j hj
          exact ha j (by simp [hj])
        · intro j hj
          exact hb j (by simp [hj])
        · exact htail

/--
If the replacement keeps every used scanner profile and lowers each used
charge, its total cost is no larger for any fixed terminal function. The
terminal function has no monotonicity requirement because final states agree.
-/
theorem planCost_le_of_used_peaks_and_charges
    (p q : Nat → Profile) (terminal : Nat → Nat)
    (arities : List Nat) (n w : Nat)
    (ha : ∀ k, k ∈ arities → (q k).peakA = (p k).peakA)
    (hb : ∀ k, k ∈ arities → (q k).peakB = (p k).peakB)
    (hc : ∀ k, k ∈ arities → (q k).charge ≤ (p k).charge) :
    planCost q terminal arities n w ≤ planCost p terminal arities n w := by
  induction arities generalizing n w with
  | nil => rfl
  | cons k ks ih =>
      have hka := ha k (by simp)
      have hkb := hb k (by simp)
      have hkc := hc k (by simp)
      have hw := childWidth_eq_of_peaks (k := k) (w := w) hka hkb
      let w' := childWidth k (p k) w
      have hlocal : 8 * n * (w' - 1) * (q k).charge ≤
          8 * n * (w' - 1) * (p k).charge :=
        Nat.mul_le_mul_left (8 * n * (w' - 1)) hkc
      change 8 * n * (childWidth k (q k) w - 1) * (q k).charge +
          planCost q terminal ks (n * (2 * k - 1)) (childWidth k (q k) w) ≤
        8 * n * (childWidth k (p k) w - 1) * (p k).charge +
          planCost p terminal ks (n * (2 * k - 1)) (childWidth k (p k) w)
      rw [hw]
      apply Nat.add_le_add hlocal
      apply ih
      · intro j hj
        exact ha j (by simp [hj])
      · intro j hj
        exact hb j (by simp [hj])
      · intro j hj
        exact hc j (by simp [hj])

/--
The retained arity-3 profile (12,8,8) has a sawtooth wrap: raising the input
from 119 to 120 lowers the next child width from 50 to 49.
-/
theorem profile_3_residue_wrap_counterexample :
    childWidth 3 ⟨12, 8, 8⟩ 119 = 50 ∧
    childWidth 3 ⟨12, 8, 8⟩ 120 = 49 ∧
    119 < 120 := by
  decide

end Paper.Planner




