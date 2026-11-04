import Points.Split

/-!
# Cyclic sequences of edges: pivots and transitions

A list `L` of distinct 2-sets with cyclic adjacency (`CycAdj L`) is read as a cyclic sequence
`eS i` (indices mod `|L|`). Consecutive edges share exactly one vertex, the pivot `piv i`. A
transition at `i` is a change of pivot; then `eS (i+1) = {piv i, piv (i+1)}`.

`card_trans_at`: at every vertex `x`, the number of transitions whose edge contains `x` is twice the
number of exits from `x`, hence even.
-/

namespace Pts

section Cyc

variable {L : List (Finset ℕ)} (hnd : L.Nodup) (h2 : ∀ f ∈ L, f.card = 2) (hcyc : CycAdj L)
  (hm : 2 ≤ L.length)

/-- The cyclic sequence. -/
def eS (L : List (Finset ℕ)) (i : ℕ) : Finset ℕ := L.getD (i % L.length) ∅

lemma eS_mem (hm : 2 ≤ L.length) (i : ℕ) : eS L i ∈ L := by
  unfold eS
  have : i % L.length < L.length := Nat.mod_lt _ (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
  exact List.getElem_mem _

lemma eS_mod (i : ℕ) : eS L (i % L.length) = eS L i := by unfold eS; rw [Nat.mod_mod]

lemma eS_add_len (i : ℕ) : eS L (i + L.length) = eS L i := by unfold eS; rw [Nat.add_mod_right]

include hcyc hm in
lemma eS_adj (i : ℕ) : (eS L i ∩ eS L (i + 1)).Nonempty := by
  have hne : L ≠ [] := by intro h; subst h; simp at hm
  have := (cyc_iff_index (R := Adj) ∅ hne).mp hcyc (i % L.length) (Nat.mod_lt _ (by omega))
  have h1 : (i % L.length + 1) % L.length = (i + 1) % L.length := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1] at this
  exact this

include hnd hm in
lemma eS_inj {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (h : eS L i = eS L j) : i = j := by
  unfold eS at h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).mp (by simpa using h)

lemma mod_succ_ne {i m : ℕ} (hm : 2 ≤ m) : i % m ≠ (i + 1) % m := by
  have hr := Nat.mod_lt i (by omega : 0 < m)
  have h1 : (i + 1) % m = (i % m + 1) % m := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m)]
  rw [h1]
  rcases Nat.lt_or_ge (i % m + 1) m with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · have : i % m + 1 = m := by omega
    rw [this, Nat.mod_self]; omega

include hnd hm in
lemma eS_ne (i : ℕ) : eS L i ≠ eS L (i + 1) := by
  intro h
  rw [← eS_mod i, ← eS_mod (i + 1)] at h
  exact mod_succ_ne hm (eS_inj hnd hm (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h)

/-- Two distinct 2-sets share at most one element. -/
lemma inter_unique {A B : Finset ℕ} (hA : A.card = 2) (hB : B.card = 2) (hAB : A ≠ B)
    {x y : ℕ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) : x = y := by
  by_contra hxy
  have hsub : ({x, y} : Finset ℕ) ⊆ A ∩ B := by
    intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  have hc : ({x, y} : Finset ℕ).card = 2 := Finset.card_pair hxy
  have h1 := Finset.eq_of_subset_of_card_le (hsub.trans Finset.inter_subset_left) (by omega)
  have h2' := Finset.eq_of_subset_of_card_le (hsub.trans Finset.inter_subset_right) (by omega)
  exact hAB (h1.symm.trans h2')

open Classical in
/-- The pivot between `eS i` and `eS (i+1)`. -/
noncomputable def piv (L : List (Finset ℕ)) (i : ℕ) : ℕ :=
  if h : (eS L i ∩ eS L (i + 1)).Nonempty then (eS L i ∩ eS L (i + 1)).min' h else 0

include hcyc hm in
lemma piv_mem (i : ℕ) : piv L i ∈ eS L i ∧ piv L i ∈ eS L (i + 1) := by
  unfold piv; rw [dif_pos (eS_adj hcyc hm i)]
  exact Finset.mem_inter.mp (Finset.min'_mem _ _)

include hnd h2 hcyc hm in
lemma piv_unique {i x : ℕ} (h1 : x ∈ eS L i) (h1' : x ∈ eS L (i + 1)) : x = piv L i := by
  have := piv_mem hcyc hm i
  exact inter_unique (h2 _ (eS_mem hm i)) (h2 _ (eS_mem hm (i + 1))) (eS_ne hnd hm i)
    (Finset.mem_inter.mpr ⟨h1, h1'⟩) (Finset.mem_inter.mpr this)

lemma piv_mod (i : ℕ) : piv L (i % L.length) = piv L i := by
  unfold piv
  have h1 : eS L (i % L.length + 1) = eS L (i + 1) := by
    rw [← eS_mod (i + 1), ← eS_mod (i % L.length + 1)]
    congr 1; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [eS_mod, h1]

include h2 hcyc hm in
/-- At a transition the edge is the pair of the two pivots. -/
lemma eS_trans {i : ℕ} (h : piv L i ≠ piv L (i + 1)) : eS L (i + 1) = {piv L i, piv L (i + 1)} := by
  have hA := (piv_mem hcyc hm i).2
  have hB := (piv_mem hcyc hm (i + 1)).1
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  · rw [h2 _ (eS_mem hm (i + 1)), Finset.card_pair h]

/-! ### Exits and entries -/

open Classical in
noncomputable def exits (L : List (Finset ℕ)) (x : ℕ) : Finset ℕ :=
  (Finset.range L.length).filter fun i => piv L i = x ∧ piv L (i + 1) ≠ x

open Classical in
noncomputable def entries (L : List (Finset ℕ)) (x : ℕ) : Finset ℕ :=
  (Finset.range L.length).filter fun i => piv L i ≠ x ∧ piv L (i + 1) = x

open Classical in
/-- Transitions whose edge contains `x`. -/
noncomputable def transAt (L : List (Finset ℕ)) (x : ℕ) : Finset ℕ :=
  (Finset.range L.length).filter fun i => piv L i ≠ piv L (i + 1) ∧ x ∈ eS L (i + 1)

include hm in
lemma card_pivots_shift (x : ℕ) :
    ((Finset.range L.length).filter fun i => piv L (i + 1) = x).card =
      ((Finset.range L.length).filter fun i => piv L i = x).card := by
  classical
  have hl : 0 < L.length := by omega
  apply Finset.card_bij (fun i _ => (i + 1) % L.length)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨Nat.mod_lt _ hl, by rw [piv_mod]; exact hi.2⟩
  · intro i hi j hj h
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    rcases Nat.lt_or_ge (i + 1) L.length with h1 | h1 <;>
      rcases Nat.lt_or_ge (j + 1) L.length with h3 | h3
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3] at h; omega
    · have : j + 1 = L.length := by omega
      rw [Nat.mod_eq_of_lt h1, this, Nat.mod_self] at h; omega
    · have : i + 1 = L.length := by omega
      rw [Nat.mod_eq_of_lt h3, this, Nat.mod_self] at h; omega
    · omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨(j + L.length - 1) % L.length, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hl, ?_⟩
      rw [← piv_mod, show ((j + L.length - 1) % L.length + 1) % L.length = j by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
          show j + L.length - 1 + 1 = j + L.length by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hj.1]]
      exact hj.2
    · rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        show j + L.length - 1 + 1 = j + L.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj.1]

include hm in
lemma card_exits_eq_entries (x : ℕ) : (exits L x).card = (entries L x).card := by
  classical
  have hA := card_pivots_shift hm x
  set B := (Finset.range L.length).filter fun i => piv L i = x ∧ piv L (i + 1) = x
  have hex : exits L x = ((Finset.range L.length).filter fun i => piv L i = x) \ B := by
    ext i; simp [exits, B]; tauto
  have hen : entries L x = ((Finset.range L.length).filter fun i => piv L (i + 1) = x) \ B := by
    ext i; simp [entries, B]; tauto
  have hB1 : B ∩ ((Finset.range L.length).filter fun i => piv L i = x) = B := by
    apply Finset.inter_eq_left.mpr; intro i; simp [B]; tauto
  have hB2 : B ∩ ((Finset.range L.length).filter fun i => piv L (i + 1) = x) = B := by
    apply Finset.inter_eq_left.mpr; intro i; simp [B]; tauto
  rw [hex, hen, Finset.card_sdiff, Finset.card_sdiff, hB1, hB2, hA]

include hnd h2 hcyc hm in
lemma card_trans_at (x : ℕ) : (transAt L x).card = 2 * (exits L x).card := by
  classical
  have hsplit : transAt L x = exits L x ∪ entries L x := by
    ext i
    simp only [transAt, exits, entries, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hne, hx⟩
      rw [eS_trans h2 hcyc hm hne] at hx
      simp at hx
      rcases hx with rfl | rfl
      · exact Or.inl ⟨hi, rfl, fun h => hne h.symm⟩
      · exact Or.inr ⟨hi, hne, rfl⟩
    · rintro (⟨hi, h1, h3⟩ | ⟨hi, h1, h3⟩)
      · refine ⟨hi, fun h => h3 (h ▸ h1), ?_⟩
        rw [← h1]; exact (piv_mem hcyc hm i).2
      · refine ⟨hi, fun h => h1 (h.trans h3), ?_⟩
        rw [← h3]; exact (piv_mem hcyc hm (i + 1)).1
  rw [hsplit, Finset.card_union_of_disjoint, ← card_exits_eq_entries hm x]
  · ring
  · rw [Finset.disjoint_left]
    intro i h1 h3
    simp only [exits, entries, Finset.mem_filter] at h1 h3
    exact h3.2.1 h1.2.1

/-! ### Index helpers -/

lemma succ_mod_inj {m i j : ℕ} (hi : i < m) (hj : j < m) (h : (i + 1) % m = (j + 1) % m) : i = j := by
  rcases Nat.lt_or_ge (i + 1) m with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) m with h3 | h3
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3] at h; omega
  · have : j + 1 = m := by omega
    rw [Nat.mod_eq_of_lt h1, this, Nat.mod_self] at h; omega
  · have : i + 1 = m := by omega
    rw [Nat.mod_eq_of_lt h3, this, Nat.mod_self] at h; omega
  · omega

/-- A property preserved along the pivot sequence holds at every pivot. -/
lemma piv_propagate (hm : 2 ≤ L.length) (Q : ℕ → Prop) (hstep : ∀ i, Q (piv L i) → Q (piv L (i + 1)))
    (j : ℕ) (hj : Q (piv L j)) : ∀ i, Q (piv L i) := by
  have hl : 0 < L.length := by omega
  have hfrom : ∀ k, Q (piv L (j % L.length + k)) := by
    intro k; induction k with
    | zero => rw [add_zero, piv_mod]; exact hj
    | succ k ih => exact hstep _ ih
  intro i
  rw [← piv_mod i]
  have hi' := Nat.mod_lt i hl
  have hj' := Nat.mod_lt j hl
  rcases le_or_gt (j % L.length) (i % L.length) with hle | hlt
  · have := hfrom (i % L.length - j % L.length)
    rwa [show j % L.length + (i % L.length - j % L.length) = i % L.length by omega] at this
  · have := hfrom (i % L.length + L.length - j % L.length)
    rw [show j % L.length + (i % L.length + L.length - j % L.length) = i % L.length + L.length by omega,
      ← piv_mod (i % L.length + L.length), Nat.add_mod_right, Nat.mod_mod] at this
    exact this

lemma eS_index (hm : 2 ≤ L.length) {f : Finset ℕ} (hf : f ∈ L) : ∃ i < L.length, eS L i = f := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hf
  exact ⟨i, hi, by simp [eS, Nat.mod_eq_of_lt hi, List.getD_eq_getElem?_getD, hi]⟩

lemma eS_pred (hm : 2 ≤ L.length) (i : ℕ) : eS L i = eS L (i + L.length - 1 + 1) := by
  rw [show i + L.length - 1 + 1 = i + L.length by omega, eS_add_len]

lemma succ_mod_eq (m i : ℕ) : (i % m + 1) % m = (i + 1) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma eS_succ_mod (i : ℕ) : eS L (i % L.length + 1) = eS L (i + 1) := by
  rw [← eS_mod (i % L.length + 1), succ_mod_eq, eS_mod]

lemma piv_succ_mod (i : ℕ) : piv L (i % L.length + 1) = piv L (i + 1) := by
  rw [← piv_mod (i % L.length + 1), succ_mod_eq, piv_mod]

end Cyc

end Pts
