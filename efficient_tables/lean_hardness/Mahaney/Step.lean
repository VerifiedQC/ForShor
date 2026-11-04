import Mahaney.Machine

/-!
# What the machine step computes

`stepS_encS`: on the encoding of a valid state (every prefix `< 2^i`), the polynomial-time step
writes the encoding of the list algorithm's next level, with query map
`gq R z j q = R (qs z j (bits j q))`.
-/

namespace Mahaney

open Complexity

/-- The query map the machine uses at level `j`. -/
def gq (R : List Bool → List Bool) (z : List Bool) (j q : ℕ) : List Bool := R (qs z j (bits j q))

section Reads

variable (z : List Bool) (i : ℕ) (L : List ℕ)

@[simp] lemma rZ_encS : rZ (encS z i L) = z := by simp [rZ, encS]
@[simp] lemma rI_encS : rI (encS z i L) = i := by simp [rI, encS]
@[simp] lemma rC_encS : rC (encS z i L) = L.length := by simp [rC, encS]
@[simp] lemma rB_encS : rB (encS z i L) = blocks i L := by simp [rB, encS]

end Reads

lemma blk_encS (z : List Bool) (i : ℕ) (L : List ℕ) {j : ℕ} (hj : j < L.length) :
    blk (encS z i L) j = bits i (L.getD j 0) := by
  simp only [blk, rB_encS, rI_encS, blocks]
  exact blocks_access L (bits i) i (fun x => length_bits i x) hj

lemma getD_mem {L : List ℕ} {j : ℕ} (hj : j < L.length) : L.getD j 0 ∈ L :=
  mem_iff_index.mpr ⟨j, hj, rfl⟩

lemma childS_encS (z : List Bool) (i : ℕ) {L : List ℕ} (hL : ∀ p ∈ L, p < 2 ^ i) {t : ℕ}
    (ht : t < 2 * L.length) :
    childS (encS z i L) t = bits (i + 1) ((children L).getD t 0) := by
  have hj : t / 2 < L.length := by omega
  rw [childS, blk_encS z i L hj, children_getD L ht]
  have hb : (decide (t % 2 = 1)).toNat = t % 2 := by
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]
  have := bits_append_bit (decide (t % 2 = 1)) (hL _ (getD_mem hj))
  rw [hb] at this
  exact this.symm

lemma lexLeB_bits {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    LexLeB (bits w a) (bits w b) ↔ a ≤ b := by
  rw [← lexLe_iff_bounded (by simp), ← val_le_iff_lexLe (by simp), val_bits_of_lt ha,
    val_bits_of_lt hb]

lemma bits_inj {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) : bits w a = bits w b ↔ a = b := by
  constructor
  · intro h; rw [← val_bits_of_lt ha, ← val_bits_of_lt hb, h]
  · rintro rfl; rfl

variable (R : List Bool → List Bool) (s : List Bool → ℕ)

lemma keepA_encS (z : List Bool) (i : ℕ) {L : List ℕ} (hL : ∀ p ∈ L, p < 2 ^ i) {t : ℕ}
    (ht : t < 2 * L.length) :
    keepA R (encS z i L) t ↔ ∀ q ∈ children L,
      gq R z (i + 1) q = gq R z (i + 1) ((children L).getD t 0) → q ≤ (children L).getD t 0 := by
  have hlt := children_lt hL
  have hlen := length_children L
  have hp : (children L).getD t 0 < 2 ^ (i + 1) := hlt _ (getD_mem (by omega))
  simp only [keepA, rZ_encS, rI_encS, rC_encS]
  constructor
  · intro H q hq heq
    obtain ⟨t', ht', rfl⟩ := mem_iff_index.mp hq
    have := H t' (by omega)
    rw [childS_encS z i hL (by omega), childS_encS z i hL ht, lexLeB_bits (hlt _ hq) hp] at this
    exact this heq
  · intro H t' ht' heq
    rw [childS_encS z i hL ht', childS_encS z i hL ht] at heq ⊢
    rw [lexLeB_bits (hlt _ (getD_mem (by omega))) hp]
    exact H _ (getD_mem (by omega)) heq

open Classical in
lemma cntA_encS (z : List Bool) (i : ℕ) {L : List ℕ} (hL : ∀ p ∈ L, p < 2 ^ i) :
    ((Finset.range (2 * rC (encS z i L))).filter fun t => keepA R (encS z i L) t).card =
      (pruneL1 (gq R z (i + 1)) (children L)).length := by
  rw [rC_encS]
  unfold pruneL1
  rw [length_filter_eq_card, length_children]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro t ht
  exact keepA_encS R z i hL (Finset.mem_range.mp ht)

open Classical in
lemma flatA_encS (z : List Bool) (i : ℕ) {L : List ℕ} (hL : ∀ p ∈ L, p < 2 ^ i) :
    ((List.range (2 * rC (encS z i L))).flatMap fun t =>
      if keepA R (encS z i L) t then childS (encS z i L) t else []) =
      blocks (i + 1) (pruneL1 (gq R z (i + 1)) (children L)) := by
  rw [rC_encS]
  unfold blocks pruneL1
  rw [filter_map_flatten, flatMap_eq_range (children L), length_children]
  apply List.flatMap_congr
  intro t ht
  have ht' := List.mem_range.mp ht
  rw [childS_encS z i hL ht']
  by_cases hk : keepA R (encS z i L) t
  · rw [if_pos hk, if_pos (by simpa using (keepA_encS R z i hL ht').mp hk)]
  · rw [if_neg hk, if_neg (by simpa using fun h => hk ((keepA_encS R z i hL ht').mpr h))]

lemma stageA_encS (z : List Bool) (i : ℕ) {L : List ℕ} (hL : ∀ p ∈ L, p < 2 ^ i) :
    stageA R (encS z i L) = encS z (i + 1) (pruneL1 (gq R z (i + 1)) (children L)) := by
  unfold stageA
  rw [cntA_encS R z i hL, flatA_encS R z i hL, rZ_encS, rI_encS]
  rfl

lemma rankS_encS (z : List Bool) (w : ℕ) {D : List ℕ} (hD : ∀ p ∈ D, p < 2 ^ w) {t : ℕ}
    (ht : t < D.length) : rankS (encS z w D) t = rankL D (D.getD t 0) := by
  classical
  have hp := hD _ (getD_mem ht)
  simp only [rankS, rC_encS, rankL]
  rw [length_filter_eq_card]
  congr 1
  apply Finset.filter_congr
  intro t' ht'
  have ht'' := Finset.mem_range.mp ht'
  have hq := hD _ (getD_mem ht'')
  rw [blk_encS z w D ht'', blk_encS z w D ht, lexLeB_bits hq hp, ne_eq, bits_inj hq hp]
  omega

open Classical in
lemma cntB_encS (z : List Bool) (w : ℕ) {D : List ℕ} (hD : ∀ p ∈ D, p < 2 ^ w) :
    ((Finset.range (rC (encS z w D))).filter fun t =>
      rankS (encS z w D) t < s (rZ (encS z w D))).card = (pruneL2 (s z) D).length := by
  rw [rC_encS, rZ_encS]
  unfold pruneL2
  rw [length_filter_eq_card]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro t ht
  rw [rankS_encS z w hD (Finset.mem_range.mp ht)]

open Classical in
lemma flatB_encS (z : List Bool) (w : ℕ) {D : List ℕ} (hD : ∀ p ∈ D, p < 2 ^ w) :
    ((List.range (rC (encS z w D))).flatMap fun t =>
      if rankS (encS z w D) t < s (rZ (encS z w D)) then blk (encS z w D) t else []) =
      blocks w (pruneL2 (s z) D) := by
  rw [rC_encS, rZ_encS]
  unfold blocks pruneL2
  rw [filter_map_flatten, flatMap_eq_range D]
  apply List.flatMap_congr
  intro t ht
  have ht' := List.mem_range.mp ht
  rw [rankS_encS z w hD ht', blk_encS z w D ht']
  by_cases hk : rankL D (D.getD t 0) < s z
  · rw [if_pos hk, if_pos (by simpa using hk)]
  · rw [if_neg hk, if_neg (by simpa using hk)]

lemma stageB_encS (z : List Bool) (w : ℕ) {D : List ℕ} (hD : ∀ p ∈ D, p < 2 ^ w) :
    stageB s (encS z w D) = encS z w (pruneL2 (s z) D) := by
  unfold stageB
  rw [cntB_encS s z w hD, flatB_encS s z w hD, rZ_encS, rI_encS]
  rfl

/-- **The step computes one level of the list algorithm.** -/
theorem stepS_encS (z : List Bool) (i : ℕ) {L : List ℕ} (hL : ∀ p ∈ L, p < 2 ^ i) :
    stepS R s (encS z i L) = encS z (i + 1) (stepL (gq R z) (s z) i L) := by
  have hD : ∀ p ∈ pruneL1 (gq R z (i + 1)) (children L), p < 2 ^ (i + 1) := fun p hp =>
    children_lt hL p (List.mem_filter.mp hp).1
  rw [stepS, stageA_encS R z i hL, stageB_encS s z (i + 1) hD]
  rfl

end Mahaney
