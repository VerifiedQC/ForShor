import Mahaney.Core

/-!
# The pruning algorithm on lists

The machine implementation keeps the candidate prefixes as a list, in the order the steps
produce them. `lvl` is that list algorithm, with the query map given per level as `g j`.
`lvl_toFinset` shows it agrees with `Core.level` on levels `≤ n` when `g j q` is the core's
query `f (query n j q)`; `lvl_nodup`, `lvl_lt` and `lvl_length` hold at every level.
-/

namespace Mahaney

variable {σ : Type*} [DecidableEq σ]

/-- Both one-bit extensions of every prefix, in order. -/
def children (L : List ℕ) : List ℕ := L.flatMap fun p => [2 * p, 2 * p + 1]

/-- Pruning 1 on a list: keep `p` when every `q` with the same query value is `≤ p`. -/
def pruneL1 (g : ℕ → σ) (E : List ℕ) : List ℕ :=
  E.filter fun p => decide (∀ q ∈ E, g q = g p → q ≤ p)

/-- Number of entries of `D` below `p`. -/
def rankL (D : List ℕ) (p : ℕ) : ℕ := (D.filter fun q => decide (q < p)).length

/-- Pruning 2 on a list: keep the entries of rank `< s`. -/
def pruneL2 (s : ℕ) (D : List ℕ) : List ℕ := D.filter fun p => decide (rankL D p < s)

/-- One level of the list algorithm, producing level `i + 1`. -/
def stepL (g : ℕ → ℕ → σ) (s i : ℕ) (L : List ℕ) : List ℕ :=
  pruneL2 s (pruneL1 (g (i + 1)) (children L))

/-- The list algorithm's levels. -/
def lvl (g : ℕ → ℕ → σ) (s : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | i + 1 => stepL g s i (lvl g s i)

lemma children_toFinset (L : List ℕ) : (children L).toFinset = expand L.toFinset := by
  ext p; simp [children, expand]

lemma children_nodup {L : List ℕ} (h : L.Nodup) : (children L).Nodup := by
  unfold children
  rw [List.nodup_flatMap]
  refine ⟨fun p _ => by simp, ?_⟩
  refine List.Pairwise.imp (fun {a b} hab => ?_) (List.nodup_iff_pairwise_ne.mp h)
  intro x hx hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  omega

lemma children_lt {L : List ℕ} {i : ℕ} (h : ∀ p ∈ L, p < 2 ^ i) :
    ∀ p ∈ children L, p < 2 ^ (i + 1) := by
  intro p hp
  simp only [children, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨q, hq, rfl | rfl⟩ := hp <;> have := h q hq <;> rw [pow_succ] <;> omega

lemma pruneL1_toFinset (g : ℕ → σ) (E : List ℕ) :
    (pruneL1 g E).toFinset = E.toFinset.filter fun p => ∀ q ∈ E.toFinset, g q = g p → q ≤ p := by
  ext p; simp [pruneL1]

lemma rankL_eq {D : List ℕ} (h : D.Nodup) (p : ℕ) : rankL D p = rank D.toFinset p := by
  unfold rankL rank
  rw [← List.toFinset_card_of_nodup (h.filter _)]
  congr 1
  ext q; simp

lemma pruneL2_toFinset {D : List ℕ} (h : D.Nodup) (s : ℕ) :
    (pruneL2 s D).toFinset = prune2 s D.toFinset := by
  ext p; simp [pruneL2, prune2, rankL_eq h]

lemma stepL_nodup (g : ℕ → ℕ → σ) (s i : ℕ) {L : List ℕ} (h : L.Nodup) :
    (stepL g s i L).Nodup :=
  ((children_nodup h).filter _).filter _

lemma lvl_nodup (g : ℕ → ℕ → σ) (s : ℕ) : ∀ i, (lvl g s i).Nodup
  | 0 => by simp [lvl]
  | i + 1 => stepL_nodup g s i (lvl_nodup g s i)

lemma stepL_lt (g : ℕ → ℕ → σ) (s i : ℕ) {L : List ℕ} (h : ∀ p ∈ L, p < 2 ^ i) :
    ∀ p ∈ stepL g s i L, p < 2 ^ (i + 1) := by
  intro p hp
  simp only [stepL, pruneL2, pruneL1, List.mem_filter] at hp
  exact children_lt h p hp.1.1

lemma lvl_lt (g : ℕ → ℕ → σ) (s : ℕ) : ∀ i, ∀ p ∈ lvl g s i, p < 2 ^ i
  | 0 => by simp [lvl]
  | i + 1 => stepL_lt g s i (lvl_lt g s i)

lemma stepL_length (g : ℕ → ℕ → σ) (s i : ℕ) {L : List ℕ} (h : L.Nodup) :
    (stepL g s i L).length ≤ s := by
  have hD : (pruneL1 (g (i + 1)) (children L)).Nodup := (children_nodup h).filter _
  rw [← List.toFinset_card_of_nodup (stepL_nodup g s i h)]
  unfold stepL
  rw [pruneL2_toFinset hD]
  exact prune2_card s _

lemma lvl_length (g : ℕ → ℕ → σ) (s : ℕ) (i : ℕ) : (lvl g s i).length ≤ max s 1 := by
  cases i with
  | zero => simp [lvl]
  | succ i => exact (stepL_length g s i (lvl_nodup g s i)).trans (le_max_left _ _)

/-- **Agreement with the core.** If `g j q` is the core's query value on levels `j ≤ n`, the
list algorithm computes the core's levels. -/
theorem lvl_toFinset {n : ℕ} {f : ℕ → σ} {g : ℕ → ℕ → σ} {s : ℕ}
    (hg : ∀ j ≤ n, ∀ q < 2 ^ j, g j q = f (query n j q)) :
    ∀ i ≤ n, (lvl g s i).toFinset = level n f s i
  | 0, _ => by simp [lvl, level]
  | i + 1, hi => by
    have ih := lvl_toFinset (s := s) hg i (by omega)
    have hlt := children_lt (lvl_lt g s i)
    have hD : (pruneL1 (g (i + 1)) (children (lvl g s i))).Nodup :=
      (children_nodup (lvl_nodup g s i)).filter _
    show (pruneL2 s (pruneL1 (g (i + 1)) (children (lvl g s i)))).toFinset = _
    rw [pruneL2_toFinset hD, pruneL1_toFinset, children_toFinset, ih]
    show prune2 s _ = prune2 s (prune1 n f (i + 1) (expand (level n f s i)))
    congr 1
    unfold prune1
    apply Finset.filter_congr
    intro p hp
    have hp' : p ∈ children (lvl g s i) := by
      rw [← List.mem_toFinset, children_toFinset, ih]; exact hp
    constructor
    · intro H q hq heq
      have hq' : q ∈ children (lvl g s i) := by
        rw [← List.mem_toFinset, children_toFinset, ih]; exact hq
      refine H q hq ?_
      rw [hg (i + 1) hi q (hlt q hq'), hg (i + 1) hi p (hlt p hp')]; exact heq
    · intro H q hq heq
      have hq' : q ∈ children (lvl g s i) := by
        rw [← List.mem_toFinset, children_toFinset, ih]; exact hq
      refine H q hq ?_
      rw [← hg (i + 1) hi q (hlt q hq'), ← hg (i + 1) hi p (hlt p hp')]; exact heq

end Mahaney
