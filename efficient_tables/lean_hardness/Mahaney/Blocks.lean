import Mahaney.ListAlg
import Mahaney.Bits

/-!
# Index forms of the list operations

A machine loop visits indices `t < |l|`, so the list operations of `ListAlg` are restated by
index: membership, `flatMap`, filtering and counting, the children of a list, and access to
fixed-width blocks of a concatenation.
-/

namespace Mahaney

lemma range_map_getD (l : List ℕ) : (List.range l.length).map (fun t => l.getD t 0) = l := by
  apply List.ext_getElem (by simp)
  intro t h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

lemma mem_iff_index {l : List ℕ} {q : ℕ} : q ∈ l ↔ ∃ t < l.length, l.getD t 0 = q := by
  conv_lhs => rw [← range_map_getD l]
  simp

lemma flatMap_eq_range {β : Type*} (l : List ℕ) (F : ℕ → List β) :
    l.flatMap F = (List.range l.length).flatMap fun t => F (l.getD t 0) := by
  conv_lhs => rw [← range_map_getD l]
  rw [List.flatMap_map]

lemma filter_map_flatten {β : Type*} (l : List ℕ) (P : ℕ → Bool) (h : ℕ → List β) :
    ((l.filter P).map h).flatten = l.flatMap fun e => if P e then h e else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases hp : P a <;> simp [List.filter_cons, hp, ih]

lemma length_filter_eq_card (l : List ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (l.filter fun e => decide (P e)).length =
      ((Finset.range l.length).filter fun t => P (l.getD t 0)).card := by
  conv_lhs => rw [← range_map_getD l]
  rw [List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  congr 1
  ext t; simp [Function.comp_def]

/-- Block access in a concatenation of equal-width blocks. -/
lemma blocks_access {β : Type*} (L : List ℕ) (h : ℕ → List β) (w : ℕ)
    (hw : ∀ x, (h x).length = w) {j : ℕ} (hj : j < L.length) :
    (((L.map h).flatten).drop (j * w)).take w = h (L.getD j 0) := by
  induction L generalizing j with
  | nil => simp at hj
  | cons a L ih =>
    cases j with
    | zero => simp [List.take_append_of_le_length (le_of_eq (hw a).symm), hw a]
    | succ j =>
      simp only [List.map_cons, List.flatten_cons, List.length_cons] at hj ⊢
      rw [show (j + 1) * w = (h a).length + j * w by rw [hw a]; ring,
        ← List.drop_drop, List.drop_left]
      simpa using ih (by omega)

lemma length_children (L : List ℕ) : (children L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [children, List.flatMap_cons] at ih ⊢; omega

lemma children_getD (L : List ℕ) {t : ℕ} (ht : t < 2 * L.length) :
    (children L).getD t 0 = 2 * L.getD (t / 2) 0 + t % 2 := by
  induction L generalizing t with
  | nil => simp at ht
  | cons a L ih =>
    have hc : children (a :: L) = 2 * a :: (2 * a + 1) :: children L := by
      simp [children, List.flatMap_cons]
    rw [hc]
    match t, ht with
    | 0, _ => simp
    | 1, _ => simp
    | t + 2, ht =>
      simp only [List.getD_cons_succ]
      rw [ih (by simp at ht; omega)]
      have : (t + 2) / 2 = t / 2 + 1 := by omega
      rw [this, List.getD_cons_succ]
      omega

end Mahaney
