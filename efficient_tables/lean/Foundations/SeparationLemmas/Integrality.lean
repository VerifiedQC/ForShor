import Foundations.SeparationLemmas.Defs
import Mathlib

namespace SeparationLemmas

lemma C_Thm2_aux {ι : Type*} [Fintype ι] (H : ℕ) (ε lam : ι → ℤ) (c : ι → ℕ)
    (h : SeparationLemmas.GapSep H ε lam c) (a : ι) (hlam : lam a = 0) :
    ∀ n : ℕ, ∀ T : Finset ι, T.card = n → a ∈ T → ∀ N : ℤ,
      ∑ i ∈ T, (ε i : ℚ) * (2 : ℚ) ^ (lam i) = N →
      ∀ q : ℕ, q < c a → ∑ i ∈ T.filter (fun i => c i = q), (ε i : ℚ) * (2 : ℚ) ^ (lam i) = 0 := by
  obtain ⟨hcard, heps, hgap⟩ := h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hT haT N hS q hq
  have hne : T.Nonempty := ⟨a, haT⟩
  obtain ⟨i0, hi0, hmin⟩ := T.exists_min_image c hne
  by_cases hc0 : c i0 = c a
  · apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter] at hi
    have := hmin i hi.1
    omega
  have hlt0 : c i0 < c a := lt_of_le_of_ne (hmin a haT) hc0
  have hLne : (T.filter (fun i => c i = c i0)).Nonempty := ⟨i0, by simp [hi0]⟩
  obtain ⟨i1, haL, hmax⟩ := (T.filter (fun i => c i = c i0)).exists_max_image lam hLne
  have hca : c i1 = c i0 := (Finset.mem_filter.mp haL).2
  have hE : lam i1 + (H : ℤ) ≤ 0 := by
    have := hgap i1 a (by omega)
    omega
  have hR : ∀ j ∈ T.filter (fun i => ¬ c i = c i0), lam i1 + (H : ℤ) ≤ lam j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    apply hgap
    have := hmin j hj.1
    omega
  have hsplit := (Finset.sum_filter_add_sum_filter_not T (fun i => c i = c i0)
    (fun i => (ε i : ℚ) * (2 : ℚ) ^ (lam i)))
  set m : ℤ := ∑ j ∈ T.filter (fun i => ¬ c i = c i0),
    ε j * 2 ^ ((lam j - (lam i1 + H)).toNat) with hm
  have hRsum : ∑ j ∈ T.filter (fun i => ¬ c i = c i0), (ε j : ℚ) * (2 : ℚ) ^ (lam j)
      = (2 : ℚ) ^ (lam i1 + H) * (m : ℚ) := by
    rw [hm]; push_cast; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have e : (2 : ℚ) ^ (lam j) = 2 ^ (lam i1 + H) * 2 ^ ((lam j - (lam i1 + H)).toNat) := by
      have := hR j hj
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      omega
    rw [e]; ring
  set k : ℕ := (-(lam i1 + H)).toNat with hk
  have hkE : (k : ℤ) + (lam i1 + H) = 0 := by omega
  have e1 : (2 : ℚ) ^ k * 2 ^ (lam i1 + (H : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num), hkE]; simp
  have e2 : (2 : ℚ) ^ k * 2 ^ (lam i1) * 2 ^ H = 1 := by
    rw [← zpow_natCast, ← zpow_natCast (2:ℚ) H, ← zpow_add₀ (by norm_num),
      ← zpow_add₀ (by norm_num)]
    have : (k : ℤ) + lam i1 + (H : ℤ) = 0 := by omega
    rw [this]; simp
  set L := ∑ i ∈ T.filter (fun i => c i = c i0), (ε i : ℚ) * (2 : ℚ) ^ (lam i) with hL
  have hLN : L = N - 2 ^ (lam i1 + (H : ℤ)) * m := by
    rw [← hRsum]; linarith
  have hP : (2 : ℚ) ^ k * L = ((2 ^ k * N - m : ℤ) : ℚ) := by
    rw [hLN]; push_cast
    have : (2 : ℚ) ^ k * (N - 2 ^ (lam i1 + (H : ℤ)) * m)
        = 2 ^ k * N - (2 ^ k * 2 ^ (lam i1 + (H : ℤ))) * m := by ring
    rw [this, e1]; ring
  have hLbound : |L| ≤ ((T.filter (fun i => c i = c i0)).card : ℚ) * 2 ^ (lam i1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℚ) < 2) _)]
    have h1 : |(ε i : ℚ)| ≤ 1 := by
      have hi := heps i
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with h | h | h <;> rw [h] <;> norm_num
    have h2 : (2 : ℚ) ^ (lam i) ≤ 2 ^ (lam i1) :=
      zpow_le_zpow_right₀ (by norm_num) (hmax i hi)
    have h3 : (0 : ℚ) < 2 ^ (lam i) := zpow_pos (by norm_num) _
    nlinarith
  have hcL : ((T.filter (fun i => c i = c i0)).card : ℚ) < 2 ^ H := by
    have : (T.filter (fun i => c i = c i0)).card ≤ Fintype.card ι :=
      (Finset.card_le_univ _)
    have : (T.filter (fun i => c i = c i0)).card < 2 ^ H := lt_of_le_of_lt this hcard
    exact_mod_cast this
  have hx : (0 : ℚ) < 2 ^ k * 2 ^ (lam i1) := by positivity
  have hk0 : (0 : ℚ) < 2 ^ k := by positivity
  have hPabs : |((2 ^ k * N - m : ℤ) : ℚ)| < 1 := by
    rw [← hP, abs_mul, abs_of_pos hk0]
    have : (2 : ℚ) ^ k * |L| ≤ 2 ^ k * (((T.filter (fun i => c i = c i0)).card : ℚ) * 2 ^ (lam i1)) :=
      mul_le_mul_of_nonneg_left hLbound hk0.le
    nlinarith
  have hP0 : (2 ^ k * N - m : ℤ) = 0 := by
    have : |(2 ^ k * N - m : ℤ)| < 1 := by exact_mod_cast hPabs
    rw [abs_lt] at this; omega
  have hL0 : L = 0 := by
    have h1 : (2 : ℚ) ^ k * L = 0 := by rw [hP, hP0]; simp
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hk0.ne'
    · exact h
  have hRN : ∑ j ∈ T.filter (fun i => ¬ c i = c i0), (ε j : ℚ) * (2 : ℚ) ^ (lam j) = N := by
    rw [← hS, ← hsplit, hL0]; simp
  have hlt : (T.filter (fun i => ¬ c i = c i0)).card < n := by
    rw [← hT]
    apply Finset.card_lt_card
    rw [Finset.filter_ssubset]
    exact ⟨i0, hi0, by simp⟩
  have key := ih _ hlt _ rfl (by simp [haT, Ne.symm hc0]) N hRN q hq
  by_cases hqq : q = c i0
  · subst hqq; exact hL0
  · have e : (T.filter (fun i => ¬ c i = c i0)).filter (fun i => c i = q)
        = T.filter (fun i => c i = q) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, by omega⟩, b⟩
    rw [e] at key; exact key

theorem integrality_anchored {ι : Type*} [Fintype ι] (H : ℕ) (ε lam : ι → ℤ) (c : ι → ℕ)
    (hG : SeparationLemmas.GapSep H ε lam c) (a : ι) (hε : ε a = 0) (hlam : lam a = 0) :
    SeparationLemmas.IsIntQ (SeparationLemmas.total ε lam) ↔
      ((∀ q : ℕ, q < c a → SeparationLemmas.clusterSum ε lam c q = 0) ∧
        SeparationLemmas.IsIntQ (SeparationLemmas.clusterSum ε lam c (c a))) := by
  classical
  have hcs : ∀ q, SeparationLemmas.clusterSum ε lam c q
      = ∑ i ∈ Finset.univ.filter (fun i => c i = q), (ε i : ℚ) * (2 : ℚ) ^ (lam i) := by
    intro q; unfold SeparationLemmas.clusterSum; congr 1
  obtain ⟨hcard, heps, hgap⟩ := hG
  -- integrality of the part above the anchor cluster
  have hU : ∀ T : Finset ι, (∀ j ∈ T, c a < c j) →
      SeparationLemmas.IsIntQ (∑ j ∈ T, (ε j : ℚ) * (2 : ℚ) ^ (lam j)) := by
    intro T hT
    refine ⟨∑ j ∈ T, ε j * 2 ^ (lam j).toNat, ?_⟩
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    have := hgap a j (hT j hj)
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  have hsplit : SeparationLemmas.total ε lam =
      (∑ i ∈ Finset.univ.filter (fun i => c i < c a), (ε i : ℚ) * (2 : ℚ) ^ (lam i))
      + SeparationLemmas.clusterSum ε lam c (c a)
      + ∑ i ∈ Finset.univ.filter (fun i => c a < c i), (ε i : ℚ) * (2 : ℚ) ^ (lam i) := by
    unfold SeparationLemmas.total
    rw [hcs, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i < c a),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun i => ¬ c i < c a))
      (fun i => c i = c a), Finset.filter_filter, Finset.filter_filter, add_assoc]
    have e1 : Finset.univ.filter (fun i => ¬ c i < c a ∧ c i = c a)
        = Finset.univ.filter (fun i => c i = c a) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have e2 : Finset.univ.filter (fun i => ¬ c i < c a ∧ ¬ c i = c a)
        = Finset.univ.filter (fun i => c a < c i) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [e1, e2]
  have hUi := hU (Finset.univ.filter (fun i => c a < c i)) (by intro j hj; simpa using hj)
  constructor
  · intro hI
    obtain ⟨N, hN⟩ := hI
    have key := C_Thm2_aux H ε lam c ⟨hcard, heps, hgap⟩ a hlam _ Finset.univ rfl
      (Finset.mem_univ a) N (by rw [hN]; rfl)
    have hLz : ∀ q, q < c a → SeparationLemmas.clusterSum ε lam c q = 0 := by
      intro q hq; rw [hcs]; exact key q hq
    refine ⟨hLz, ?_⟩
    have hL0 : (∑ i ∈ Finset.univ.filter (fun i => c i < c a), (ε i : ℚ) * (2 : ℚ) ^ (lam i)) = 0 := by
      have : Finset.univ.filter (fun i => c i < c a)
          = (Finset.range (c a)).biUnion (fun q => Finset.univ.filter (fun i => c i = q)) := by
        ext x; simp
      rw [this, Finset.sum_biUnion]
      · apply Finset.sum_eq_zero
        intro q hq
        rw [← hcs]; exact hLz q (by simpa using hq)
      · intro p _ q _ hpq
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_filter] at hx hx'
        exact hpq (hx.2.symm.trans hx'.2)
    obtain ⟨M, hM⟩ := hUi
    refine ⟨N - M, ?_⟩
    have := hsplit
    rw [hL0, ← hN] at this
    push_cast
    rw [hM]; linarith
  · rintro ⟨hLz, ⟨M, hM⟩⟩
    obtain ⟨M2, hM2⟩ := hUi
    have hL0 : (∑ i ∈ Finset.univ.filter (fun i => c i < c a), (ε i : ℚ) * (2 : ℚ) ^ (lam i)) = 0 := by
      have : Finset.univ.filter (fun i => c i < c a)
          = (Finset.range (c a)).biUnion (fun q => Finset.univ.filter (fun i => c i = q)) := by
        ext x; simp
      rw [this, Finset.sum_biUnion]
      · apply Finset.sum_eq_zero
        intro q hq
        rw [← hcs]; exact hLz q (by simpa using hq)
      · intro p _ q _ hpq
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_filter] at hx hx'
        exact hpq (hx.2.symm.trans hx'.2)
    refine ⟨M + M2, ?_⟩
    rw [hsplit, hL0, ← hM, ← hM2]; push_cast; ring

end SeparationLemmas
