import Foundations.SeparationLemmas.Defs
import Mathlib

namespace SeparationLemmas

lemma C_Thm1_aux {ι : Type*} [Fintype ι] (H : ℕ) (ε lam : ι → ℤ) (c : ι → ℕ)
    (h : SeparationLemmas.GapSep H ε lam c) :
    ∀ n : ℕ, ∀ T : Finset ι, T.card = n →
      ∑ i ∈ T, (ε i : ℚ) * (2 : ℚ) ^ (lam i) = 0 →
      ∀ q : ℕ, ∑ i ∈ T.filter (fun i => c i = q), (ε i : ℚ) * (2 : ℚ) ^ (lam i) = 0 := by
  obtain ⟨hcard, heps, hgap⟩ := h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hT hS
  rcases T.eq_empty_or_nonempty with rfl | hne
  · intro q; simp
  obtain ⟨i0, hi0, hmin⟩ := T.exists_min_image c hne
  have hLne : (T.filter (fun i => c i = c i0)).Nonempty := ⟨i0, by simp [hi0]⟩
  obtain ⟨a, haL, hmax⟩ := (T.filter (fun i => c i = c i0)).exists_max_image lam hLne
  have hca : c a = c i0 := (Finset.mem_filter.mp haL).2
  have hsplit := (Finset.sum_filter_add_sum_filter_not T (fun i => c i = c i0)
    (fun i => (ε i : ℚ) * (2 : ℚ) ^ (lam i)))
  have hR : ∀ j ∈ T.filter (fun i => ¬ c i = c i0), lam a + (H : ℤ) ≤ lam j := by
    intro j hj
    rw [Finset.mem_filter] at hj
    apply hgap
    have := hmin j hj.1
    omega
  set m : ℤ := ∑ j ∈ T.filter (fun i => ¬ c i = c i0),
    ε j * 2 ^ ((lam j - (lam a + H)).toNat) with hm
  have hRsum : ∑ j ∈ T.filter (fun i => ¬ c i = c i0), (ε j : ℚ) * (2 : ℚ) ^ (lam j)
      = (2 : ℚ) ^ (lam a + H) * (m : ℚ) := by
    rw [hm]; push_cast; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have e : (2 : ℚ) ^ (lam j) = 2 ^ (lam a + H) * 2 ^ ((lam j - (lam a + H)).toNat) := by
      have := hR j hj
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      omega
    rw [e]; ring
  have hpos : (0 : ℚ) < 2 ^ (lam a + H) := zpow_pos (by norm_num) _
  have hB : (2 : ℚ) ^ (lam a + (H : ℤ)) = 2 ^ H * 2 ^ (lam a) := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]; ring
  have hLbound : |∑ i ∈ T.filter (fun i => c i = c i0), (ε i : ℚ) * (2 : ℚ) ^ (lam i)|
      ≤ ((T.filter (fun i => c i = c i0)).card : ℚ) * 2 ^ (lam a) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℚ) < 2) _)]
    have h1 : |(ε i : ℚ)| ≤ 1 := by
      have hi := heps i
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with h | h | h <;> rw [h] <;> norm_num
    have h2 : (2 : ℚ) ^ (lam i) ≤ 2 ^ (lam a) :=
      zpow_le_zpow_right₀ (by norm_num) (hmax i hi)
    have h3 : (0 : ℚ) < 2 ^ (lam i) := zpow_pos (by norm_num) _
    nlinarith
  have hcL : ((T.filter (fun i => c i = c i0)).card : ℚ) < 2 ^ H := by
    have : (T.filter (fun i => c i = c i0)).card ≤ Fintype.card ι :=
      (Finset.card_le_univ _)
    have : (T.filter (fun i => c i = c i0)).card < 2 ^ H := lt_of_le_of_lt this hcard
    exact_mod_cast this
  have hpa : (0 : ℚ) < 2 ^ (lam a) := zpow_pos (by norm_num) _
  have hLsum : ∑ i ∈ T.filter (fun i => c i = c i0), (ε i : ℚ) * (2 : ℚ) ^ (lam i)
      = - ((2 : ℚ) ^ (lam a + H) * (m : ℚ)) := by
    rw [← hRsum]; linarith
  have hmabs : |(m : ℚ)| < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : (2 : ℚ) ^ (lam a + H) ≤ |(2 : ℚ) ^ (lam a + H) * (m : ℚ)| := by
      rw [abs_mul, abs_of_pos hpos]; nlinarith
    rw [hLsum, abs_neg] at hLbound
    nlinarith
  have hm0 : m = 0 := by
    have : |m| < 1 := by exact_mod_cast hmabs
    rw [abs_lt] at this; omega
  rw [hm0] at hLsum hRsum
  simp at hLsum hRsum
  have hlt : (T.filter (fun i => ¬ c i = c i0)).card < n := by
    rw [← hT]
    apply Finset.card_lt_card
    rw [Finset.filter_ssubset]
    exact ⟨i0, hi0, by simp⟩
  have key := ih _ hlt _ rfl hRsum
  intro q
  by_cases hq : q = c i0
  · subst hq; exact hLsum
  · have := key q
    have e : (T.filter (fun i => ¬ c i = c i0)).filter (fun i => c i = q)
        = T.filter (fun i => c i = q) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, by omega⟩, b⟩
    rw [e] at this; exact this

theorem zero_criterion {ι : Type*} [Fintype ι] (H : ℕ) (ε lam : ι → ℤ) (c : ι → ℕ)
    (h : SeparationLemmas.GapSep H ε lam c) :
    SeparationLemmas.total ε lam = 0 ↔ ∀ q : ℕ, SeparationLemmas.clusterSum ε lam c q = 0 := by
  classical
  constructor
  · intro hS q
    unfold SeparationLemmas.clusterSum
    have := C_Thm1_aux H ε lam c h _ Finset.univ rfl hS q
    convert this
  · intro hq
    unfold SeparationLemmas.total
    have hs : ∑ i, (ε i : ℚ) * (2 : ℚ) ^ (lam i)
        = ∑ q ∈ Finset.univ.image c,
          ∑ i ∈ Finset.univ.filter (fun i => c i = q), (ε i : ℚ) * (2 : ℚ) ^ (lam i) :=
      (Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i))
        _).symm
    rw [hs]
    apply Finset.sum_eq_zero
    intro q _
    have := hq q
    unfold SeparationLemmas.clusterSum at this
    convert this

end SeparationLemmas
