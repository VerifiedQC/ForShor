import Points.CycleTable
import Mahaney.Blocks

/-!
# Directed Hamiltonian cycles and the line graph of the split-and-pendant graph

For a digraph `D` on `0, …, n−1` the graph `H D` has, for every vertex `v`, the path
`in v – mid v – out v` and a pendant `mid v – leaf v`, and for every arc `u → w` the edge
`out u – in w`. Vertices are numbered `4v, 4v+1, 4v+2, 4v+3`.

This file proves the direction **directed Hamiltonian cycle ⇒ Hamiltonian cycle of `L(H D)`**
(`ehc_of_dhc`); `SplitBack.lean` proves the converse for out-degree ≤ 2.
-/

namespace Pts

/-- A digraph on `0, …, n − 1`. -/
structure Dig where
  n : ℕ
  arcs : List (ℕ × ℕ)

/-- Well formed: no repeated arcs, no loops, vertices in range. -/
def Dig.ok (D : Dig) : Prop :=
  D.arcs.Nodup ∧ ∀ a ∈ D.arcs, a.1 < D.n ∧ a.2 < D.n ∧ a.1 ≠ a.2

/-- Every vertex has out-degree at most two. -/
def Dig.out2 (D : Dig) : Prop := ∀ u, (D.arcs.filter fun a => a.1 = u).length ≤ 2

/-- **Directed Hamiltonian cycle** (on at least two vertices). -/
def DHC (D : Dig) : Prop :=
  2 ≤ D.n ∧ ∃ L : List ℕ, L.Perm (List.range D.n) ∧ Chn (fun u w => (u, w) ∈ D.arcs) (L ++ L.take 1)

def vin (v : ℕ) : ℕ := 4 * v
def vmid (v : ℕ) : ℕ := 4 * v + 1
def vout (v : ℕ) : ℕ := 4 * v + 2
def vleaf (v : ℕ) : ℕ := 4 * v + 3

def gadE (v : ℕ) : List (Finset ℕ) := [{vin v, vmid v}, {vmid v, vleaf v}, {vmid v, vout v}]

def arcE (a : ℕ × ℕ) : Finset ℕ := {vout a.1, vin a.2}

/-- The edges of `H D`. -/
def HE (D : Dig) : List (Finset ℕ) := (List.range D.n).flatMap gadE ++ D.arcs.map arcE

/-! ### Index forms of chains -/

lemma chn_iff_index {α : Type*} {R : α → α → Prop} (d : α) :
    ∀ {Y : List α}, Chn R Y ↔ ∀ i, i + 1 < Y.length → R (Y.getD i d) (Y.getD (i + 1) d)
  | [] => by simp
  | [a] => by simp
  | a :: b :: Y => by
    rw [chn_cons_cons, chn_iff_index d (Y := b :: Y)]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => simpa using h1
      | succ i => simpa using h2 i (by simp at hi ⊢; omega)
    · intro h
      exact ⟨by simpa using h 0 (by simp), fun i hi => by simpa using h (i + 1) (by simp at hi ⊢; omega)⟩

/-- Cyclic chains in index form. -/
lemma cyc_iff_index {α : Type*} {R : α → α → Prop} (d : α) {L : List α} (hL : L ≠ []) :
    Chn R (L ++ L.take 1) ↔
      ∀ i < L.length, R (L.getD i d) (L.getD ((i + 1) % L.length) d) := by
  rw [chn_iff_index d]
  have hl : 0 < L.length := List.length_pos_iff.mpr hL
  have htake : (L.take 1).length = 1 := by simp; omega
  simp only [List.length_append, htake]
  have hget : ∀ j, j < L.length + 1 → (L ++ L.take 1).getD j d = L.getD (j % L.length) d := by
    intro j hj
    rcases Nat.lt_or_ge j L.length with h | h
    · rw [Nat.mod_eq_of_lt h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left h]
    · have : j = L.length := by omega
      subst this
      rw [Nat.mod_self, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (le_refl _), Nat.sub_self]
      cases L with
      | nil => exact absurd rfl hL
      | cons a L => simp
  constructor
  · intro h i hi
    have := h i (by omega)
    rwa [hget i (by omega), hget (i + 1) (by omega), Nat.mod_eq_of_lt hi] at this
  · intro h i hi
    rw [hget i (by omega), hget (i + 1) (by omega), Nat.mod_eq_of_lt (by omega : i < L.length)]
    exact h i (by omega)

/-! ### Chains of blocks -/

lemma chn_common {L : List (Finset ℕ)} {x : ℕ} (h : ∀ e ∈ L, x ∈ e) : Chn Adj L := by
  induction L with
  | nil => trivial
  | cons a L ih => cases L with
    | nil => trivial
    | cons b L =>
      exact ⟨⟨x, Finset.mem_inter.mpr ⟨h a (by simp), h b (by simp)⟩⟩,
        ih fun e he => h e (List.mem_cons_of_mem _ he)⟩

/-- A chain of blocks, closed by an extra element `z`. -/
lemma chn_blocks {α : Type*} {R : α → α → Prop} (B : ℕ → List α) (z : α) :
    ∀ n, 0 < n → (∀ i < n, B i ≠ [] ∧ Chn R (B i)) →
      (∀ i, i + 1 < n → ∀ x ∈ (B i).getLast?, ∀ y ∈ (B (i + 1)).head?, R x y) →
      (∀ x ∈ (B (n - 1)).getLast?, R x z) →
      Chn R ((List.range n).flatMap B ++ [z])
  | 0, h, _, _, _ => absurd h (by omega)
  | 1, _, hB, _, hz => by
    simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [chn_append]
    refine ⟨(hB 0 (by omega)).2, trivial, fun x hx y hy => ?_⟩
    simp at hy; subst hy; exact hz x hx
  | n + 2, _, hB, hlink, hz => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    obtain ⟨a0, l0, hal⟩ := List.exists_cons_of_ne_nil (hB (n + 1) (by omega)).1
    have ih := chn_blocks B a0 (n + 1) (by omega) (fun i hi => hB i (by omega))
      (fun i hi => hlink i (by omega)) (fun x hx => by
        apply hlink n (by omega) x (by simpa using hx)
        rw [hal]; simp)
    rw [chn_append] at ih ⊢
    obtain ⟨hpre, -, -⟩ := ih
    obtain ⟨hne, hch⟩ := hB (n + 1) (by omega)
    refine ⟨hpre, ?_, ?_⟩
    · rw [chn_append]
      exact ⟨hch, trivial, fun x hx y hy => by simp at hy; subst hy; exact hz x (by simpa using hx)⟩
    · intro x hx y hy
      have hy' : y ∈ (B (n + 1)).head? := by
        cases h : B (n + 1) with
        | nil => exact absurd h hne
        | cons a l => rw [h] at hy; simpa using hy
      -- the last element of the prefix is the last element of block `n`
      have hlast : ((List.range (n + 1)).flatMap B).getLast? = (B n).getLast? := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
          List.getLast?_append_of_ne_nil _ (hB n (by omega)).1]
      rw [hlast] at hx
      exact hlink n (by omega) x hx y hy'

/-! ### Directed cycle ⇒ edge cycle -/

section Forward

variable (D : Dig) (L : List ℕ)

def vtx (i : ℕ) : ℕ := L.getD i 0
def pre (i : ℕ) : ℕ := L.getD ((i + L.length - 1) % L.length) 0

/-- Arcs into `v` other than from `p`. -/
def extra (p v : ℕ) : List (Finset ℕ) := ((D.arcs.filter fun a => a.2 = v ∧ a.1 ≠ p)).map arcE

/-- The block of the `i`-th vertex of the cycle. -/
def blk (i : ℕ) : List (Finset ℕ) :=
  arcE (pre L i, vtx L i) :: (extra D (pre L i) (vtx L i) ++ gadE (vtx L i))

def tourE : List (Finset ℕ) := (List.range L.length).flatMap (blk D L)

end Forward

lemma blk_chain (D : Dig) (L : List ℕ) (i : ℕ) : Chn Adj (blk D L i) := by
  unfold blk gadE
  have hpre : ∀ e ∈ arcE (pre L i, vtx L i) :: (extra D (pre L i) (vtx L i) ++
      [({vin (vtx L i), vmid (vtx L i)} : Finset ℕ)]), vin (vtx L i) ∈ e := by
    intro e he
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, extra, List.mem_map,
      List.mem_filter, decide_eq_true_eq, List.not_mem_nil, or_false] at he
    rcases he with rfl | ⟨a, ⟨_, ha, _⟩, rfl⟩ | rfl
    · simp [arcE]
    · simp [arcE, ha]
    · simp
  have h := chn_common hpre
  have : (arcE (pre L i, vtx L i) :: (extra D (pre L i) (vtx L i) ++
      [{vin (vtx L i), vmid (vtx L i)}, {vmid (vtx L i), vleaf (vtx L i)},
        {vmid (vtx L i), vout (vtx L i)}])) =
      (arcE (pre L i, vtx L i) :: (extra D (pre L i) (vtx L i) ++
        [({vin (vtx L i), vmid (vtx L i)} : Finset ℕ)])) ++
        [{vmid (vtx L i), vleaf (vtx L i)}, {vmid (vtx L i), vout (vtx L i)}] := by simp
  rw [this, chn_append]
  refine ⟨h, ⟨⟨vmid (vtx L i), by simp⟩, trivial⟩, fun x hx y hy => ?_⟩
  simp only [List.cons_append, List.getLast?_cons, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
  subst hx; subst hy
  exact ⟨vmid (vtx L i), by simp⟩

lemma blk_ne_nil (D : Dig) (L : List ℕ) (i : ℕ) : blk D L i ≠ [] := by simp [blk]

lemma blk_last (D : Dig) (L : List ℕ) (i : ℕ) :
    (blk D L i).getLast? = some {vmid (vtx L i), vout (vtx L i)} := by
  rw [show blk D L i = (arcE (pre L i, vtx L i) :: (extra D (pre L i) (vtx L i) ++
      [{vin (vtx L i), vmid (vtx L i)}, {vmid (vtx L i), vleaf (vtx L i)}])) ++
      [{vmid (vtx L i), vout (vtx L i)}] by simp [blk, gadE]]
  exact List.getLast?_concat

lemma blk_head (D : Dig) (L : List ℕ) (i : ℕ) :
    (blk D L i).head? = some (arcE (pre L i, vtx L i)) := by simp [blk]

lemma pre_succ (L : List ℕ) {i : ℕ} (hi : i + 1 < L.length) : pre L (i + 1) = vtx L i := by
  unfold pre vtx; congr 1
  rw [show i + 1 + L.length - 1 = i + L.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma pre_zero (L : List ℕ) (hL : L ≠ []) : pre L 0 = vtx L (L.length - 1) := by
  unfold pre vtx; congr 1
  have : 0 < L.length := List.length_pos_iff.mpr hL
  rw [zero_add, Nat.mod_eq_of_lt (by omega)]

theorem tourE_cyc (D : Dig) (L : List ℕ) (hL : L ≠ []) : CycAdj (tourE D L) := by
  have hl : 0 < L.length := List.length_pos_iff.mpr hL
  unfold CycAdj
  have htake : (tourE D L).take 1 = [arcE (pre L 0, vtx L 0)] := by
    unfold tourE
    obtain ⟨k, hk⟩ : ∃ k, L.length = k + 1 := ⟨L.length - 1, by omega⟩
    rw [hk, List.range_succ_eq_map, List.flatMap_cons]
    simp [blk]
  rw [htake]
  apply chn_blocks (blk D L) _ L.length hl (fun i _ => ⟨blk_ne_nil D L i, blk_chain D L i⟩)
  · intro i hi x hx y hy
    rw [blk_last] at hx; rw [blk_head] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx; subst hy
    rw [pre_succ L hi]
    exact ⟨vout (vtx L i), by simp [arcE]⟩
  · intro x hx
    rw [blk_last] at hx
    simp only [Option.mem_def, Option.some.injEq] at hx
    subst hx
    rw [pre_zero L hL]
    exact ⟨vout (vtx L (L.length - 1)), by simp [arcE]⟩

/-! ### The tour uses every edge once -/

lemma perm_flatMap_append {α β : Type*} [DecidableEq β] (l : List α) (f g : α → List β) :
    (l.flatMap fun x => f x ++ g x).Perm (l.flatMap f ++ l.flatMap g) := by
  rw [List.perm_iff_count]
  intro b
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.count_append] at ih ⊢; omega

lemma sum_range_ite (n k c : ℕ) :
    ((List.range n).map fun x => if k = x then c else 0).sum = if k < n then c else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    split_ifs <;> omega

lemma group_by_target (arcs : List (ℕ × ℕ)) (n : ℕ) (h : ∀ a ∈ arcs, a.2 < n) :
    ((List.range n).flatMap fun v => arcs.filter fun a => a.2 = v).Perm arcs := by
  classical
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatMap]
  have key : ∀ v, List.count a (arcs.filter fun x => x.2 = v) = if a.2 = v then List.count a arcs else 0 := by
    intro v
    split_ifs with hv
    · exact List.count_filter (by simpa using hv)
    · apply List.count_eq_zero_of_not_mem
      intro hm
      exact hv (by simpa using (List.mem_filter.mp hm).2)
  simp only [Function.comp_def, key]
  by_cases ha : a ∈ arcs
  · have hlt := h a ha
    rw [sum_range_ite, if_pos hlt]
  · rw [List.count_eq_zero_of_not_mem ha]; simp

lemma sum_range_single (m i0 : ℕ) (f : ℕ → ℕ) (hz : ∀ i < m, i ≠ i0 → f i = 0) :
    ((List.range m).map f).sum = if i0 < m then f i0 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (fun i hi => hz i (by omega))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases h : i0 = m
    · subst h; simp
    · rw [hz m (by omega) (Ne.symm h)]
      split_ifs <;> omega

/-- The arcs of the blocks: the cycle arc into `vtx i` and the other arcs into it. -/
def blockArcs (D : Dig) (L : List ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  (pre L i, vtx L i) :: D.arcs.filter fun a => a.2 = vtx L i ∧ a.1 ≠ pre L i

lemma blockArcs_perm {D : Dig} {L : List ℕ} (hD : D.ok) (hL : L.Perm (List.range D.n))
    (harc : ∀ i < L.length, (pre L i, vtx L i) ∈ D.arcs) :
    ((List.range L.length).flatMap (blockArcs D L)).Perm D.arcs := by
  classical
  have hnd : L.Nodup := hL.nodup_iff.mpr List.nodup_range
  have hlen : L.length = D.n := by simpa using hL.length_eq
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatMap]
  have hterm : ∀ i < L.length, List.count a (blockArcs D L i) =
      (if (pre L i, vtx L i) = a then 1 else 0) +
        (if a.2 = vtx L i ∧ a.1 ≠ pre L i then List.count a D.arcs else 0) := by
    intro i _
    unfold blockArcs
    rw [List.count_cons]
    split_ifs with h1 h2 h2 <;> simp_all [List.count_filter]
    all_goals first
      | (apply List.count_eq_zero_of_not_mem; intro hm; have := (List.mem_filter.mp hm).2; simp_all)
      | omega
  by_cases hlt : a.2 < D.n
  · obtain ⟨i0, hi0, hv0⟩ : ∃ i0 < L.length, vtx L i0 = a.2 := by
      have : a.2 ∈ L := hL.symm.subset (List.mem_range.mpr hlt)
      obtain ⟨i0, hi0, h⟩ := List.mem_iff_getElem.mp this
      exact ⟨i0, hi0, by simp [vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0, h]⟩
    have hz : ∀ i < L.length, i ≠ i0 → List.count a (blockArcs D L i) = 0 := by
      intro i hi hne
      rw [hterm i hi]
      have hvne : vtx L i ≠ a.2 := by
        intro h
        apply hne
        have e1 : L[i] = a.2 := by
          simpa [vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h
        have e2 : L[i0] = a.2 := by
          simpa [vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0] using hv0
        exact (List.Nodup.getElem_inj_iff hnd).mp (e1.trans e2.symm)
      rw [if_neg (fun h => hvne (by rw [← h])), if_neg (fun h => hvne h.1.symm)]
    rw [Function.comp_def, sum_range_single _ i0 _ hz, if_pos hi0, hterm i0 hi0]
    by_cases ha : a ∈ D.arcs
    · have hc : List.count a D.arcs = 1 := List.count_eq_one_of_mem hD.1 ha
      rw [hc]
      by_cases hp : a.1 = pre L i0
      · rw [if_pos (Prod.ext hp.symm hv0), if_neg (fun h => h.2 hp)]
      · rw [if_neg (fun h => hp (by rw [← h])), if_pos ⟨hv0.symm, hp⟩]
    · rw [List.count_eq_zero_of_not_mem ha]
      rw [if_neg (fun h => ha (by rw [← h]; exact harc i0 hi0))]
      simp
  · have hna : a ∉ D.arcs := fun h => hlt (hD.2 a h).2.1
    rw [List.count_eq_zero_of_not_mem hna]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [Function.comp_apply, hterm i (List.mem_range.mp hi)]
    have hvlt : vtx L i < D.n := by
      have : vtx L i ∈ L := by
        simp [vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.mem_range.mp hi)]
      exact List.mem_range.mp (hL.subset this)
    rw [if_neg (fun h => hna (by rw [← h]; exact harc i (List.mem_range.mp hi))),
      if_neg (fun h => hlt (by rw [h.1]; exact hvlt))]
    rfl

theorem tourE_perm {D : Dig} {L : List ℕ} (hD : D.ok) (hL : L.Perm (List.range D.n))
    (harc : ∀ i < L.length, (pre L i, vtx L i) ∈ D.arcs) : (tourE D L).Perm (HE D) := by
  classical
  have hsplit : tourE D L = (List.range L.length).flatMap fun i =>
      (blockArcs D L i).map arcE ++ gadE (vtx L i) := by
    unfold tourE blk blockArcs extra; simp
  rw [hsplit]
  refine (perm_flatMap_append _ _ _).trans (List.perm_append_comm.trans ?_)
  unfold HE
  refine List.Perm.append ?_ ?_
  · have : (List.range L.length).flatMap (fun i => gadE (vtx L i)) = L.flatMap gadE := by
      conv_rhs => rw [← Mahaney.range_map_getD L]
      rw [List.flatMap_map]; rfl
    rw [this]; exact hL.flatMap_right gadE
  · rw [← List.map_flatMap]
    exact (blockArcs_perm hD hL harc).map arcE

/-- **Directed Hamiltonian cycle ⇒ Hamiltonian cycle of the line graph.** -/
theorem ehc_of_dhc {D : Dig} (hD : D.ok) (h : DHC D) : EHC (HE D) := by
  obtain ⟨hn, L, hL, hc⟩ := h
  have hlen : L.length = D.n := by simpa using hL.length_eq
  have hLne : L ≠ [] := by intro h; subst h; simp at hlen; omega
  have hcyc := (cyc_iff_index 0 hLne).mp hc
  have harc : ∀ i < L.length, (pre L i, vtx L i) ∈ D.arcs := by
    intro i hi
    have hl : 0 < L.length := by omega
    have := hcyc ((i + L.length - 1) % L.length) (Nat.mod_lt _ hl)
    have hmod : ((i + L.length - 1) % L.length + 1) % L.length = i := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [show i + L.length - 1 + 1 = i + L.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    rw [hmod] at this
    exact this
  exact ⟨tourE D L, tourE_perm hD hL harc, tourE_cyc D L hLne⟩

end Pts
