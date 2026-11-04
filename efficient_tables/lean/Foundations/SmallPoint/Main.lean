import Foundations.SmallPoint.Defs
import Foundations.SmallPoint.CofactorBound
import Foundations.SmallPoint.ExtremeDecomposition
import Foundations.SmallPoint.ConicCaratheodory
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean

namespace SmallPoint

open Matrix

theorem thm1_homog (t s B : ℕ) (hB : 1 ≤ B)
    (A : Matrix (Fin s) (Fin t) ℤ) (b : Fin s → ℤ)
    (hA : ∀ i j, |A i j| ≤ (B : ℤ)) (hb : ∀ i, |b i| ≤ (B : ℤ)) :
    ∃ G : Matrix (Fin (s + (t + 1))) (Fin (t + 1)) ℤ, (∀ i j, |G i j| ≤ (B : ℤ)) ∧
      ∀ x : Fin (t + 1) → ℝ, x ∈ coneK G ↔
        ((∀ k, 0 ≤ x k) ∧ ∀ r, ∑ c, (A r c : ℝ) * x c.castSucc ≤ b r * x (Fin.last t)) := by
  let G : Matrix (Fin (s + (t + 1))) (Fin (t + 1)) ℤ := Matrix.of fun i j =>
    Fin.addCases (motive := fun _ => ℤ)
      (fun r => Fin.lastCases (motive := fun _ => ℤ) (-b r) (fun c => A r c) j)
      (fun k => if k = j then -1 else 0) i
  have hG1 : ∀ r c, G (Fin.castAdd _ r) c.castSucc = A r c := by
    intro r c; simp [G]
  have hG2 : ∀ r, G (Fin.castAdd _ r) (Fin.last t) = -b r := by
    intro r; simp [G]
  have hG3 : ∀ k j, G (Fin.natAdd s k) j = if k = j then -1 else 0 := by
    intro k j; simp [G]
  have hrow1 : ∀ (x : Fin (t + 1) → ℝ) r, (G.map (Int.cast : ℤ → ℝ) *ᵥ x) (Fin.castAdd _ r) =
      ∑ c, (A r c : ℝ) * x c.castSucc - b r * x (Fin.last t) := by
    intro x r
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hG1, hG2]
    ring
  have hrow2 : ∀ (x : Fin (t + 1) → ℝ) k, (G.map (Int.cast : ℤ → ℝ) *ᵥ x) (Fin.natAdd s k) =
      - x k := by
    intro x k
    simp [Matrix.mulVec, dotProduct, hG3]
  refine ⟨G, ?_, ?_⟩
  · intro i j
    refine Fin.addCases (fun r => ?_) (fun k => ?_) i
    · refine Fin.lastCases ?_ (fun c => ?_) j
      · rw [hG2]; simpa using hb r
      · rw [hG1]; exact hA _ _
    · rw [hG3]
      split_ifs <;> simp <;> omega
  · intro x
    constructor
    · intro hx
      refine ⟨fun k => ?_, fun r => ?_⟩
      · have := hx (Fin.natAdd s k)
        rw [hrow2] at this
        linarith
      · have := hx (Fin.castAdd _ r)
        rw [hrow1] at this
        linarith
    · rintro ⟨h1, h2⟩ i
      refine Fin.addCases (fun r => ?_) (fun k => ?_) i
      · rw [hrow1]; linarith [h2 r]
      · rw [hrow2]; linarith [h1 k]

theorem small_integer_point (t s B : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B)
    (A : Matrix (Fin s) (Fin t) ℤ) (b : Fin s → ℤ)
    (hA : ∀ i j, |A i j| ≤ (B : ℤ)) (hb : ∀ i, |b i| ≤ (B : ℤ))
    (hP : HasIntegerPoint A b) :
    ∃ y : Fin t → ℤ, (fun j => (y j : ℝ)) ∈ polyhedronInt A b ∧
      ∀ i, 0 ≤ y i ∧ y i ≤ ((t : ℤ) + 1) * ((Nat.factorial t : ℕ) * (B : ℤ) ^ t) := by
  classical
  obtain ⟨G, hGb, hGiff⟩ := thm1_homog t s B hB A b hA hb
  set Dz : ℤ := ((Nat.factorial t : ℕ) : ℤ) * (B : ℤ) ^ t with hDz
  have hDz0 : 0 ≤ Dz := by positivity
  have hK : ∀ x ∈ coneK G, ∀ j, 0 ≤ x j := fun x hx => ((hGiff x).1 hx).1
  have hpt : ∀ x ∈ coneK G, -x ∈ coneK G → x = 0 := by
    intro x hx hnx
    funext j
    have h1 := hK x hx j
    have h2 := hK _ hnx j
    simp only [Pi.neg_apply] at h2
    simp only [Pi.zero_apply]
    linarith
  have hcl : ∀ (m : ℕ) (I : Finset (Fin m)) (c : Fin m → ℝ) (u : Fin m → Fin (t + 1) → ℝ),
      (∀ j ∈ I, 0 ≤ c j) → (∀ j ∈ I, u j ∈ coneK G) → ∑ j ∈ I, c j • u j ∈ coneK G := by
    intro m I c u hc hu i
    have : (G.map (Int.cast : ℤ → ℝ) *ᵥ ∑ j ∈ I, c j • u j) i =
        ∑ j ∈ I, c j * (G.map (Int.cast : ℤ → ℝ) *ᵥ u j) i := by
      simp [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]
    rw [this]
    exact Finset.sum_nonpos (fun j hj =>
      mul_nonpos_of_nonneg_of_nonpos (hc j hj) (hu j hj i))
  -- finishing step
  have hfin : ∀ V : Fin (t + 1) → ℤ, (fun i => (V i : ℝ)) ∈ coneK G → V (Fin.last t) = 1 →
      (∀ i, V i ≤ ((t : ℤ) + 1) * Dz) →
      ∃ y : Fin t → ℤ, (fun j => (y j : ℝ)) ∈ polyhedronInt A b ∧
        ∀ i, 0 ≤ y i ∧ y i ≤ ((t : ℤ) + 1) * Dz := by
    intro V hV hl hbd
    obtain ⟨h1, h2⟩ := (hGiff _).1 hV
    refine ⟨fun c => V c.castSucc, ⟨fun j => h1 _, fun r => ?_⟩, fun i => ⟨?_, hbd _⟩⟩
    · have := h2 r
      rw [hl] at this
      simpa [Matrix.mulVec, dotProduct] using this
    · have := h1 i.castSucc
      exact_mod_cast this
  obtain ⟨y, hy⟩ := hP
  let Z0 : Fin (t + 1) → ℤ := Fin.snoc (α := fun _ => ℤ) y 1
  have hZ0 : (fun i => (Z0 i : ℝ)) ∈ coneK G := by
    rw [hGiff]
    obtain ⟨hy1, hy2⟩ := hy
    constructor
    · intro k
      refine Fin.lastCases ?_ (fun c => ?_) k
      · simp [Z0]
      · simpa [Z0] using hy1 c
    · intro r
      have := hy2 r
      simpa [Z0, Matrix.mulVec, dotProduct] using this
  obtain ⟨k, v, hext, hsum⟩ := extreme_decomposition G hpt _ hZ0
  choose g μ hμ hvg hg0 hgb using fun j => cofactor_extreme t _ B G hGb hK (v j) (hext j)
  have hgK : ∀ j, (fun i => (g j i : ℝ)) ∈ coneK G := by
    intro j
    have := C_Lem2_smul_mem G (μ j)⁻¹ (inv_pos.2 (hμ j)) (v j) (hext j).1
    rw [hvg j, smul_smul, inv_mul_cancel₀ (hμ j).ne', one_smul] at this
    exact this
  have hsum' : (fun i => (Z0 i : ℝ)) = ∑ j, μ j • (fun i => (g j i : ℝ)) := by
    rw [hsum]; exact Finset.sum_congr rfl (fun j _ => hvg j)
  obtain ⟨I, lam, hI, hlam, hIsum⟩ := C_Lem3_carath (fun j => fun i => (g j i : ℝ)) k
    Finset.univ (by simp) μ (fun j _ => hμ j)
  have hZI : (fun i => (Z0 i : ℝ)) = ∑ j ∈ I, lam j • (fun i => (g j i : ℝ)) :=
    hsum'.trans hIsum
  set n : Fin k → ℤ := fun j => Int.floor (lam j) with hn
  have hn0 : ∀ j ∈ I, 0 ≤ n j := fun j hj => Int.floor_nonneg.2 (hlam j hj).le
  have hf0 : ∀ j, 0 ≤ lam j - (n j : ℝ) := fun j => sub_nonneg.2 (Int.floor_le _)
  have hf1 : ∀ j, lam j - (n j : ℝ) ≤ 1 := fun j => by
    have := Int.lt_floor_add_one (lam j)
    simp only [hn]; linarith
  let W : Fin (t + 1) → ℤ := fun i => Z0 i - ∑ j ∈ I, n j * g j i
  have hW : ∀ i, (W i : ℝ) = ∑ j ∈ I, (lam j - (n j : ℝ)) * (g j i : ℝ) := by
    intro i
    have h := congrFun hZI i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [W]
    push_cast
    rw [h, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hWK : (fun i => (W i : ℝ)) ∈ coneK G := by
    have := hcl k I (fun j => lam j - (n j : ℝ)) (fun j => fun i => (g j i : ℝ))
      (fun j _ => hf0 j) (fun j _ => hgK j)
    convert this using 1
    funext i
    rw [hW i]
    simp [Finset.sum_apply]
  have hW0 : ∀ i, 0 ≤ W i := by
    intro i
    have := hK _ hWK i
    exact_mod_cast this
  have hWb : ∀ i, W i ≤ ((t : ℤ) + 1) * Dz := by
    intro i
    have h1 : (W i : ℝ) ≤ ((t : ℝ) + 1) * (Dz : ℝ) := by
      calc (W i : ℝ) = ∑ j ∈ I, (lam j - (n j : ℝ)) * (g j i : ℝ) := hW i
        _ ≤ ∑ j ∈ I, (g j i : ℝ) := Finset.sum_le_sum (fun j _ => by
            have := hg0 j i
            have h0 : (0 : ℝ) ≤ g j i := by exact_mod_cast this
            exact mul_le_of_le_one_left h0 (hf1 j))
        _ ≤ ∑ j ∈ I, (Dz : ℝ) := Finset.sum_le_sum (fun j _ => by exact_mod_cast hgb j i)
        _ = (I.card : ℝ) * Dz := by simp
        _ ≤ ((t : ℝ) + 1) * Dz := by
            apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast hDz0)
            exact_mod_cast hI
    exact_mod_cast h1
  have hWl : W (Fin.last t) = 1 - ∑ j ∈ I, n j * g j (Fin.last t) := by
    simp [W, Z0]
  have hN0 : 0 ≤ ∑ j ∈ I, n j * g j (Fin.last t) :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (hn0 j hj) (hg0 j _))
  have hN1 : ∑ j ∈ I, n j * g j (Fin.last t) ≤ 1 := by
    have := hW0 (Fin.last t)
    omega
  rcases hN0.eq_or_lt with hN | hN
  · refine hfin W hWK ?_ hWb
    rw [hWl, ← hN]; simp
  · have hex : ∃ j0 ∈ I, n j0 * g j0 (Fin.last t) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have := Finset.sum_eq_zero hcon
      omega
    obtain ⟨j0, hj0, hne⟩ := hex
    have hle : n j0 * g j0 (Fin.last t) ≤ ∑ j ∈ I, n j * g j (Fin.last t) :=
      Finset.single_le_sum (f := fun j => n j * g j (Fin.last t))
        (fun j hj => mul_nonneg (hn0 j hj) (hg0 j _)) hj0
    have hn1 : 1 ≤ n j0 := by
      have := hn0 j0 hj0
      by_contra hc
      have : n j0 = 0 := by omega
      exact hne (by simp [this])
    have hg1 : 1 ≤ g j0 (Fin.last t) := by
      have := hg0 j0 (Fin.last t)
      by_contra hc
      have : g j0 (Fin.last t) = 0 := by omega
      exact hne (by simp [this])
    have hg1' : g j0 (Fin.last t) = 1 := by
      have : g j0 (Fin.last t) ≤ n j0 * g j0 (Fin.last t) := by nlinarith
      omega
    refine hfin (g j0) (hgK j0) hg1' (fun i => ?_)
    have := hgb j0 i
    nlinarith [hDz0, (by exact_mod_cast (Nat.zero_le t) : (0 : ℤ) ≤ t)]

end SmallPoint
