import Foundations.SmallPoint.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace SmallPoint

theorem det_bound_aux (t : ℕ) (B : ℕ) (M : Matrix (Fin t) (Fin t) ℤ)
    (h : ∀ i j, |M i j| ≤ (B : ℤ)) : |M.det| ≤ (Nat.factorial t : ℤ) * (B : ℤ) ^ t := by
  rw [Matrix.det_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have key : ∀ σ : Equiv.Perm (Fin t),
      |(↑(Equiv.Perm.sign σ) : ℤ) • ∏ i, M (σ i) i| ≤ (B : ℤ) ^ t := by
    intro σ
    have h1 : |∏ i, M (σ i) i| ≤ (B : ℤ) ^ t := by
      rw [Finset.abs_prod]
      calc ∏ i, |M (σ i) i| ≤ ∏ _i : Fin t, (B : ℤ) :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => h _ _)
        _ = (B : ℤ) ^ t := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2 <;> simpa [h2] using h1
  calc ∑ σ : Equiv.Perm (Fin t), |(↑(Equiv.Perm.sign σ) : ℤ) • ∏ i, M (σ i) i|
      ≤ (Finset.univ : Finset (Equiv.Perm (Fin t))).card • (B : ℤ) ^ t :=
        Finset.sum_le_card_nsmul _ _ _ (fun σ _ => key σ)
    _ = (Nat.factorial t : ℤ) * (B : ℤ) ^ t := by
        simp [Finset.card_univ, Fintype.card_perm]

theorem indep_rows_aux (t s : ℕ) (n : ℕ) (G : Matrix (Fin s) (Fin n) ℤ) (w : Fin n → ℝ)
    (hr : tightRank G w = t) :
    ∃ r : Fin t → Fin s, (∀ i, r i ∈ tightRows G w) ∧
      LinearIndependent ℝ (fun i => (G.map (Int.cast : ℤ → ℝ)) (r i)) := by
  unfold tightRank at hr
  rw [Matrix.rank_eq_finrank_span_row] at hr
  set N := (G.map (Int.cast : ℤ → ℝ)).submatrix ((↑) : tightRows G w → Fin s) id with hN
  obtain ⟨κ, a, ha, hspan', hli⟩ := exists_linearIndependent' ℝ N.row
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = t := by
    rw [← finrank_span_eq_card hli, hspan', hr]
  let e : Fin t ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (a (e i)).1, fun i => (a (e i)).2, ?_⟩
  exact hli.comp e e.injective

section
open Matrix

theorem core_aux (t : ℕ) (B : ℕ) (A : Matrix (Fin t) (Fin (t + 1)) ℤ)
    (hA : ∀ i j, |A i j| ≤ (B : ℤ)) (w : Fin (t + 1) → ℝ) (hw0 : w ≠ 0)
    (hAw : ∀ i, (A.map (Int.cast : ℤ → ℝ) *ᵥ w) i = 0)
    (hli : LinearIndependent ℝ (fun i => (A.map (Int.cast : ℤ → ℝ)) i)) :
    ∃ (c : Fin (t + 1) → ℤ) (l : ℝ), w = l • (fun i => (c i : ℝ)) ∧
      ∀ i, |c i| ≤ (Nat.factorial t : ℤ) * (B : ℤ) ^ t := by
  classical
  let A0 : Matrix (Fin (t + 1)) (Fin (t + 1)) ℤ := fun i j => if h : i.val < t then A ⟨i, h⟩ j else 0
  have hA0c : ∀ (i : Fin t) j, A0 (Fin.castSucc i) j = A i j := by
    intro i j; simp [A0]
  have hA0l : ∀ j, A0 (Fin.last t) j = 0 := by
    intro j; simp [A0]
  let c : Fin (t + 1) → ℤ := fun j => (A0.updateRow (Fin.last t) (Pi.single j 1)).det
  have hcb : ∀ j, |c j| ≤ (Nat.factorial t : ℤ) * (B : ℤ) ^ t := by
    intro j
    have : c j = (-1) ^ ((Fin.last t : Fin (t+1)).val + j.val) *
        (A.submatrix id j.succAbove).det := by
      show (A0.updateRow (Fin.last t) (Pi.single j 1)).det = _
      rw [Matrix.det_succ_row _ (Fin.last t), Finset.sum_eq_single j]
      · simp only [Matrix.updateRow_self, Pi.single_eq_same, mul_one]
        congr 2
        ext i k
        simp [Matrix.submatrix_apply, Matrix.updateRow_apply, Fin.succAbove_last, hA0c,
          (Fin.castSucc_lt_last i).ne]
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
      · simp
    rw [this, abs_mul]
    simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact det_bound_aux t B _ (fun i k => hA _ _)
  let Ar : Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ := A0.map (Int.cast : ℤ → ℝ)
  let M : Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ := Ar.updateRow (Fin.last t) w
  have hMw : M *ᵥ w = (w ⬝ᵥ w) • (Pi.single (Fin.last t) (1 : ℝ) : Fin (t + 1) → ℝ) := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [M, Matrix.mulVec, dotProduct]
    · have := hAw i
      have h2 : (M *ᵥ w) (Fin.castSucc i) = 0 := by
        simp only [Matrix.mulVec, dotProduct, M, Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne, Ar,
          Matrix.map_apply, hA0c]
        simpa [Matrix.mulVec, dotProduct] using this
      rw [h2]
      simp [(Fin.castSucc_lt_last i).ne]
  have hcol : (adjugate M *ᵥ (Pi.single (Fin.last t) (1 : ℝ) : Fin (t + 1) → ℝ)) =
      fun j => (c j : ℝ) := by
    ext j
    have e1 : (adjugate M *ᵥ (Pi.single (Fin.last t) (1 : ℝ) : Fin (t + 1) → ℝ)) j =
        adjugate M j (Fin.last t) := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e1, Matrix.adjugate_apply, Matrix.updateRow_idem]
    simp only [c]
    symm
    refine (RingHom.map_det (Int.castRingHom ℝ) (A0.updateRow (Fin.last t) (Pi.single j 1))).trans ?_
    congr 1
    ext i k
    simp only [Matrix.updateRow_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Ar]
    split_ifs <;> simp [Pi.single_apply]
  have hadj : M *ᵥ (fun j => (c j : ℝ)) = M.det • (Pi.single (Fin.last t) (1 : ℝ) : Fin (t + 1) → ℝ) := by
    rw [← hcol, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hww : 0 < w ⬝ᵥ w := by
    have hnn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.1 h.symm) hw0
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv
    have h1 : v ⬝ᵥ (M *ᵥ w) = 0 := by rw [Matrix.dotProduct_mulVec, hvM]; simp
    rw [hMw] at h1
    simp [dotProduct_smul] at h1
    have hl : v (Fin.last t) = 0 := by
      rcases h1 with h | h
      · exact absurd h hw0
      · exact h
    have hu : ∀ i : Fin t, v (Fin.castSucc i) = 0 := by
      refine Fintype.linearIndependent_iff.1 hli (fun i => v (Fin.castSucc i)) ?_
      funext j
      have := congrFun hvM j
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, hl, zero_mul, add_zero] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      simp only [Pi.zero_apply] at this
      refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) this
      simp [M, Ar, hA0c]
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hl
    · simpa using hu i
  refine ⟨c, (w ⬝ᵥ w) / M.det, ?_, hcb⟩
  have hz : M *ᵥ (w - ((w ⬝ᵥ w) / M.det) • (fun j => (c j : ℝ))) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMw, hadj, smul_smul, div_mul_cancel₀ _ hdet, sub_self]
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hz
  exact sub_eq_zero.1 this

end

theorem cofactor_extreme (t s : ℕ) (B : ℕ) (G : Matrix (Fin s) (Fin (t + 1)) ℤ)
    (hG : ∀ i j, |G i j| ≤ (B : ℤ))
    (hK : ∀ x ∈ coneK G, ∀ j, 0 ≤ x j)
    (w : Fin (t + 1) → ℝ) (hw : IsExtremeVector G w) :
    ∃ (g : Fin (t + 1) → ℤ) (μ : ℝ), 0 < μ ∧ w = μ • (fun i => (g i : ℝ)) ∧
      (∀ i, 0 ≤ g i) ∧ ∀ i, g i ≤ (Nat.factorial t : ℤ) * (B : ℤ) ^ t := by
  obtain ⟨hwK, hw0, hrk⟩ := hw
  have hrk' : tightRank G w = t := by simpa using hrk
  obtain ⟨r, hr, hli⟩ := indep_rows_aux t s (t + 1) G w hrk'
  obtain ⟨c, l, hwl, hcb⟩ := core_aux t B (G.submatrix r id) (fun i j => hG _ _) w hw0
    (fun i => by
      have := hr i
      simpa [tightRows, Matrix.mulVec, dotProduct] using this)
    hli
  have hnn : ∀ j, 0 ≤ l * (c j : ℝ) := by
    intro j
    have := hK w hwK j
    rw [hwl] at this
    simpa using this
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hw0
    rw [hwl]; simp
  rcases lt_or_gt_of_ne hl0 with hl | hl
  · refine ⟨fun i => -c i, -l, by linarith, ?_, ?_, fun i => ?_⟩
    · rw [hwl]; ext i; simp
    · intro i
      have h1 := hnn i
      have : (c i : ℝ) ≤ 0 := by nlinarith
      have : c i ≤ 0 := by exact_mod_cast this
      show 0 ≤ -c i
      omega
    · exact (neg_le_abs _).trans (hcb i)
  · refine ⟨c, l, hl, hwl, ?_, fun i => (le_abs_self _).trans (hcb i)⟩
    intro i
    have h1 := hnn i
    have : (0 : ℝ) ≤ c i := by nlinarith
    exact_mod_cast this

end SmallPoint
