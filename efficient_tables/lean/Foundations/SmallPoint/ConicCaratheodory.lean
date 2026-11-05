import Foundations.SmallPoint.Defs
import Mathlib.Algebra.BigOperators.Fin

namespace SmallPoint

theorem C_Lem3_carath {t m : ℕ} (v : Fin m → Fin (t + 1) → ℝ) :
    ∀ n : ℕ, ∀ S : Finset (Fin m), S.card = n → ∀ lam : Fin m → ℝ, (∀ j ∈ S, 0 < lam j) →
    ∃ (I : Finset (Fin m)) (lam' : Fin m → ℝ), I.card ≤ t + 1 ∧ (∀ j ∈ I, 0 < lam' j) ∧
      ∑ j ∈ S, lam j • v j = ∑ j ∈ I, lam' j • v j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS lam hlam
  by_cases hc : S.card ≤ t + 1
  · exact ⟨S, lam, hc, hlam, rfl⟩
  push_neg at hc
  -- linear dependence
  have hdep : ∃ g : Fin m → ℝ, ∑ j ∈ S, g j • v j = 0 ∧ ∃ i ∈ S, g i ≠ 0 := by
    have hnli : ¬ LinearIndependent ℝ (fun j : S => v j) := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp at this
      omega
    rw [Fintype.not_linearIndependent_iff] at hnli
    obtain ⟨g, hg, i, hi⟩ := hnli
    refine ⟨fun j => if h : j ∈ S then g ⟨j, h⟩ else 0, ?_, i.1, i.2, ?_⟩
    · rw [← hg, ← Finset.sum_coe_sort S]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [x.2]
    · simpa [i.2] using hi
  obtain ⟨g0, hg0, i0, hi0S, hi0⟩ := hdep
  obtain ⟨g, hg, hgpos⟩ : ∃ g : Fin m → ℝ, ∑ j ∈ S, g j • v j = 0 ∧ ∃ i ∈ S, 0 < g i := by
    rcases lt_or_gt_of_ne hi0 with h | h
    · refine ⟨fun j => - g0 j, ?_, i0, hi0S, by simpa using h⟩
      simp [neg_smul, Finset.sum_neg_distrib, hg0]
    · exact ⟨g0, hg0, i0, hi0S, h⟩
  set P := S.filter (fun j => 0 < g j) with hP
  have hne : P.Nonempty := by
    obtain ⟨i, hi, hgi⟩ := hgpos
    exact ⟨i, by simp [hP, hi, hgi]⟩
  obtain ⟨j0, hj0P, hmin⟩ := Finset.exists_min_image P (fun j => lam j / g j) hne
  have hj0S : j0 ∈ S := (Finset.mem_filter.1 hj0P).1
  have hj0g : 0 < g j0 := (Finset.mem_filter.1 hj0P).2
  set c := lam j0 / g j0 with hcdef
  have hcpos : 0 < c := div_pos (hlam j0 hj0S) hj0g
  have hnn : ∀ j ∈ S, 0 ≤ lam j - c * g j := by
    intro j hj
    by_cases hgj : 0 < g j
    · have := hmin j (by simp [hP, hj, hgj])
      have h2 : c * g j ≤ lam j := by
        have := (le_div_iff₀ hgj).1 this
        exact this
      linarith
    · push_neg at hgj
      have := hlam j hj
      nlinarith
  have hj0zero : lam j0 - c * g j0 = 0 := by
    rw [hcdef]; field_simp; ring
  set S' := S.filter (fun j => 0 < lam j - c * g j) with hS'
  have hsub : S' ⊆ S := Finset.filter_subset _ _
  have hlt : S'.card < n := by
    rw [← hS]
    apply Finset.card_lt_card
    refine ⟨hsub, fun h => ?_⟩
    have := (Finset.mem_filter.1 (h hj0S)).2
    linarith
  obtain ⟨I, lam', hI, hpos, hsum⟩ := ih S'.card hlt S' rfl (fun j => lam j - c * g j)
    (fun j hj => (Finset.mem_filter.1 hj).2)
  refine ⟨I, lam', hI, hpos, ?_⟩
  rw [← hsum]
  have h1 : ∑ j ∈ S, (lam j - c * g j) • v j = ∑ j ∈ S, lam j • v j := by
    have : ∑ j ∈ S, (lam j - c * g j) • v j
        = ∑ j ∈ S, lam j • v j - c • ∑ j ∈ S, g j • v j := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_smul, mul_smul]
    rw [this, hg]; simp
  rw [← h1]
  symm
  apply Finset.sum_subset hsub
  intro j hj hjn
  have : ¬ 0 < lam j - c * g j := fun h => hjn (Finset.mem_filter.2 ⟨hj, h⟩)
  have h0 : lam j - c * g j = 0 := le_antisymm (not_lt.1 this) (hnn j hj)
  simp [h0]

theorem conic_caratheodory {t : ℕ} (K : Set (Fin (t + 1) → ℝ))
    (m : ℕ) (wj : Fin m → Fin (t + 1) → ℝ)
    (hext : ∀ j, IsExtremeRayOfCone K (wj j))
    (w : Fin (t + 1) → ℝ) (hw : w = ∑ j, wj j) :
    ∃ (I : Finset (Fin m)) (lam : Fin m → ℝ),
      I.card ≤ t + 1 ∧ (∀ j ∈ I, 0 < lam j) ∧ w = ∑ j ∈ I, lam j • wj j := by
  obtain ⟨I, lam', hI, hpos, hsum⟩ := C_Lem3_carath wj _ Finset.univ rfl (fun _ => 1)
    (fun _ _ => one_pos)
  exact ⟨I, lam', hI, hpos, by rw [hw, ← hsum]; simp⟩

end SmallPoint
