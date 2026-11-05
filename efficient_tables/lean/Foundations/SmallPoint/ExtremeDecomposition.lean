import Foundations.SmallPoint.Defs
import Mathlib.Algebra.BigOperators.Fin

namespace SmallPoint

open Matrix

theorem C_Lem2_smul_mem {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ) (c : ℝ) (hc : 0 < c)
    (v : Fin n → ℝ) (hv : v ∈ coneK G) : c • v ∈ coneK G := by
  intro i
  have := hv i
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith

theorem C_Lem2_smul_ext {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ) (c : ℝ) (hc : 0 < c)
    (v : Fin n → ℝ) (hv : IsExtremeVector G v) : IsExtremeVector G (c • v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨C_Lem2_smul_mem G c hc v h1, smul_ne_zero hc.ne' h2, ?_⟩
  have h : tightRows G (c • v) = tightRows G v := by
    ext i
    simp [tightRows, Matrix.mulVec_smul, hc.ne']
  unfold tightRank at h3 ⊢
  rw [h]
  exact h3

theorem C_Lem2_kernel {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ)
    (w : Fin n → ℝ) (hw : w ∈ coneK G) (hne : w ≠ 0) (h : tightRank G w ≠ n - 1) :
    ∃ u : Fin n → ℝ, (∀ i ∈ tightRows G w, (G.map (Int.cast : ℤ → ℝ) *ᵥ u) i = 0) ∧
      ∀ c : ℝ, u ≠ c • w := by
  by_contra hcon
  push_neg at hcon
  apply h
  show Matrix.rank ((G.map (Int.cast : ℤ → ℝ)).submatrix ((↑) : tightRows G w → Fin m) id) = n - 1
  set A := (G.map (Int.cast : ℤ → ℝ)).submatrix ((↑) : tightRows G w → Fin m) id with hA
  have hker : LinearMap.ker A.mulVecLin = Submodule.span ℝ {w} := by
    apply le_antisymm
    · intro u hu
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu
      obtain ⟨c, hc⟩ := hcon u (fun i hi => by
        have := congrFun hu ⟨i, hi⟩
        exact this)
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      ext i
      exact i.2
  have h1 : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 1 := by
    rw [hker]; exact finrank_span_singleton hne
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [h1] at h2
  have h3 : Matrix.rank A = Module.finrank ℝ (LinearMap.range A.mulVecLin) := rfl
  simp at h2
  omega

theorem C_Lem2_step {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ)
    (hpointed : ∀ x ∈ coneK G, -x ∈ coneK G → x = 0)
    (w : Fin n → ℝ) (hw : w ∈ coneK G) (hne : w ≠ 0)
    (u : Fin n → ℝ) (hu : ∀ i ∈ tightRows G w, (G.map (Int.cast : ℤ → ℝ) *ᵥ u) i = 0)
    (hnc : ∀ c : ℝ, u ≠ c • w) :
    ∃ (c : ℝ) (p q : Fin n → ℝ), 0 < c ∧ p ∈ coneK G ∧ q ∈ coneK G ∧
      Set.ncard {i | (G.map (Int.cast : ℤ → ℝ) *ᵥ p) i ≠ 0} <
        Set.ncard {i | (G.map (Int.cast : ℤ → ℝ) *ᵥ w) i ≠ 0} ∧
      Set.ncard {i | (G.map (Int.cast : ℤ → ℝ) *ᵥ q) i ≠ 0} <
        Set.ncard {i | (G.map (Int.cast : ℤ → ℝ) *ᵥ w) i ≠ 0} ∧
      w = c • p + c • q := by
  set G' := G.map (Int.cast : ℤ → ℝ) with hG'
  set I : Set (Fin m) := {i | (G' *ᵥ w) i ≠ 0} with hI
  have hwneg : ∀ i, (G' *ᵥ w) i ≤ 0 := hw
  have hIneg : ∀ i ∈ I, (G' *ᵥ w) i < 0 := fun i hi =>
    lt_of_le_of_ne (hwneg i) hi
  have hIne : I.Nonempty := by
    by_contra hE
    rw [Set.not_nonempty_iff_eq_empty] at hE
    apply hne
    apply hpointed w hw
    intro i
    have : (G' *ᵥ w) i = 0 := by
      by_contra hh
      have : i ∈ I := hh
      rw [hE] at this
      exact this
    show (G' *ᵥ -w) i ≤ 0
    rw [Matrix.mulVec_neg, Pi.neg_apply, this]
    simp
  have hIfin : (I.toFinite.toFinset).Nonempty := by
    exact ⟨hIne.some, Set.Finite.mem_toFinset _ |>.mpr hIne.some_mem⟩
  set r : Fin m → ℝ := fun i => (G' *ᵥ u) i / (-(G' *ᵥ w) i) with hr
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image _ r hIfin
  obtain ⟨i1, hi1, hmin⟩ := Finset.exists_min_image _ r hIfin
  simp only [Set.Finite.mem_toFinset] at hi0 hi1 hmax hmin
  set M := r i0 with hM
  set mm := r i1 with hmm
  -- Gu on I in terms of r
  have hGu : ∀ i ∈ I, (G' *ᵥ u) i = r i * (-(G' *ᵥ w) i) := by
    intro i hi
    have := hIneg i hi
    show _ = (G' *ᵥ u) i / (-(G' *ᵥ w) i) * (-(G' *ᵥ w) i)
    rw [div_mul_cancel₀ _ (neg_ne_zero.mpr this.ne)]
  have hGp : ∀ i, (G' *ᵥ (u + M • w)) i = if i ∈ I then (r i - M) * (-(G' *ᵥ w) i) else 0 := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    by_cases hi : i ∈ I
    · rw [if_pos hi]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hGu i hi]
      ring
    · rw [if_neg hi]
      have hz : (G' *ᵥ w) i = 0 := by
        by_contra hh; exact hi hh
      have hzu := hu i hz
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz, hzu]
      ring
  have hGq : ∀ i, (G' *ᵥ (u + mm • w)) i = if i ∈ I then (r i - mm) * (-(G' *ᵥ w) i) else 0 := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    by_cases hi : i ∈ I
    · rw [if_pos hi]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hGu i hi]
      ring
    · rw [if_neg hi]
      have hz : (G' *ᵥ w) i = 0 := by
        by_contra hh; exact hi hh
      have hzu := hu i hz
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz, hzu]
      ring
  have hpm : u + M • w ∈ coneK G := by
    intro i
    rw [← hG', hGp i]
    split_ifs with hi
    · have := hmax i hi
      have h2 := hIneg i hi
      nlinarith
    · exact le_refl _
  have hqm : -(u + mm • w) ∈ coneK G := by
    intro i
    rw [← hG', Matrix.mulVec_neg, Pi.neg_apply, hGq i]
    split_ifs with hi
    · have := hmin i hi
      have h2 := hIneg i hi
      nlinarith
    · simp
  have hlt : mm < M := by
    by_contra hge
    push_neg at hge
    apply hnc (-M)
    have hz : u + M • w = 0 := by
      apply hpointed _ hpm
      intro i
      rw [← hG', Matrix.mulVec_neg, Pi.neg_apply, hGp i]
      split_ifs with hi
      · have h1 := hmax i hi
        have h2 := hmin i hi
        have : r i - M = 0 := by linarith
        rw [this]; simp
      · simp
    have : u = -(M • w) := by
      have := congrArg (fun x => x - M • w) hz
      simp at this
      exact this
    rw [this]; simp
  refine ⟨(M - mm)⁻¹, u + M • w, -(u + mm • w), inv_pos.mpr (by linarith), hpm, hqm, ?_, ?_, ?_⟩
  · apply Set.ncard_lt_ncard _ I.toFinite
    refine ⟨?_, ?_⟩
    · intro i hi
      by_contra hn
      have h1 : (G' *ᵥ (u + M • w)) i ≠ 0 := hi
      apply h1
      rw [hGp i, if_neg hn]
    · intro hsub
      have h1 : (G' *ᵥ (u + M • w)) i0 ≠ 0 := hsub hi0
      apply h1
      rw [hGp i0, if_pos hi0]
      simp [hM]
  · apply Set.ncard_lt_ncard _ I.toFinite
    refine ⟨?_, ?_⟩
    · intro i hi
      by_contra hn
      have h1 : (G' *ᵥ -(u + mm • w)) i ≠ 0 := hi
      apply h1
      rw [Matrix.mulVec_neg, Pi.neg_apply, hGq i, if_neg hn]
      simp
    · intro hsub
      have h1 : (G' *ᵥ -(u + mm • w)) i1 ≠ 0 := hsub hi1
      apply h1
      rw [Matrix.mulVec_neg, Pi.neg_apply, hGq i1, if_pos hi1]
      simp [hmm]
  · rw [← smul_add]
    have : u + M • w + -(u + mm • w) = (M - mm) • w := by
      rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hlt.ne'), one_smul]

theorem C_Lem2_key {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ)
    (hpointed : ∀ x ∈ coneK G, -x ∈ coneK G → x = 0) :
    ∀ (N : ℕ) (w : Fin n → ℝ), w ∈ coneK G →
      Set.ncard {i | (G.map (Int.cast : ℤ → ℝ) *ᵥ w) i ≠ 0} ≤ N →
      ∃ (k : ℕ) (v : Fin k → Fin n → ℝ),
        (∀ j, IsExtremeVector G (v j)) ∧ w = ∑ j, v j := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hw hN
    by_cases h0 : w = 0
    · exact ⟨0, fun j => j.elim0, fun j => j.elim0, by simp [h0]⟩
    by_cases hr : tightRank G w = n - 1
    · exact ⟨1, fun _ => w, fun _ => ⟨hw, h0, hr⟩, by simp⟩
    obtain ⟨u, hu, hnc⟩ := C_Lem2_kernel G w hw h0 hr
    obtain ⟨c, p, q, hc, hp, hq, hlp, hlq, hwe⟩ :=
      C_Lem2_step G hpointed w hw h0 u hu hnc
    obtain ⟨k1, v1, e1, s1⟩ := ih _ (by omega) p hp le_rfl
    obtain ⟨k2, v2, e2, s2⟩ := ih _ (by omega) q hq le_rfl
    refine ⟨k1 + k2, Fin.append (fun j => c • v1 j) (fun j => c • v2 j), ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
        exact C_Lem2_smul_ext G c hc _ (e1 i)
      · simp only [Fin.append_right]
        exact C_Lem2_smul_ext G c hc _ (e2 i)
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← s1, ← s2]
      exact hwe

theorem extreme_decomposition {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ)
    (hpointed : ∀ x ∈ coneK G, -x ∈ coneK G → x = 0)
    (w : Fin n → ℝ) (hw : w ∈ coneK G) :
    ∃ (k : ℕ) (v : Fin k → Fin n → ℝ),
      (∀ j, IsExtremeVector G (v j)) ∧ w = ∑ j, v j :=
  C_Lem2_key G hpointed _ w hw le_rfl

end SmallPoint
