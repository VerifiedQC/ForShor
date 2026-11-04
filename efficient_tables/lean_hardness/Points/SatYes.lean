import Points.SatNo

/-!
# SAT → DHC₂: a satisfying assignment gives a Hamiltonian cycle

Given an assignment `α` making some literal true in every clause, each clause picks its *first*
true literal (`det`), whose cell takes the detour through the whole clause cycle. The successor
map `τ` walks row `0`, row `1`, …, each row rightward when `α x` and leftward otherwise.
That `τ` is a single cycle through every vertex is proved with *segments*: `Seg v w P` says that
iterating `τ` from `v` reaches `w`, passing (strictly before `w`) through every vertex in `P`.
-/

namespace Pts

open Complexity SAT

namespace TS

variable {G : TS}

/-! ### Segments of an orbit -/

section seg

variable (τ : V → V)

def Seg (v w : V) (P : V → Prop) : Prop := ∃ k, τ^[k] v = w ∧ ∀ u, P u → ∃ j < k, τ^[j] v = u

lemma seg_step {v : V} : Seg τ v (τ v) (· = v) := ⟨1, rfl, fun u hu => ⟨0, by omega, hu.symm⟩⟩

lemma seg_trans {v w z : V} {P Q : V → Prop} (h1 : Seg τ v w P) (h2 : Seg τ w z Q) :
    Seg τ v z (fun u => P u ∨ Q u) := by
  obtain ⟨k1, hk1, hP⟩ := h1
  obtain ⟨k2, hk2, hQ⟩ := h2
  refine ⟨k2 + k1, by rw [Function.iterate_add_apply, hk1, hk2], fun u hu => ?_⟩
  rcases hu with hu | hu
  · obtain ⟨j, hj, h⟩ := hP u hu; exact ⟨j, by omega, h⟩
  · obtain ⟨j, hj, h⟩ := hQ u hu
    exact ⟨j + k1, by omega, by rw [Function.iterate_add_apply, hk1, h]⟩

lemma seg_mono {v w : V} {P Q : V → Prop} (h : Seg τ v w P) (hPQ : ∀ u, Q u → P u) :
    Seg τ v w Q := by
  obtain ⟨k, hk, hP⟩ := h
  exact ⟨k, hk, fun u hu => hP u (hPQ u hu)⟩

lemma seg_nil (v : V) : Seg τ v v (fun _ => False) := ⟨0, rfl, fun _ h => h.elim⟩

/-- Chaining segments along `f m, f (m+1), …, f M`. -/
lemma seg_chain (f : ℕ → V) (P : ℕ → V → Prop) (m : ℕ) :
    ∀ M, m ≤ M → (∀ i, m ≤ i → i < M → Seg τ (f i) (f (i + 1)) (P i)) →
      Seg τ (f m) (f M) (fun u => ∃ i, m ≤ i ∧ i < M ∧ P i u) := by
  intro M hM h
  induction M, hM using Nat.le_induction with
  | base => exact seg_mono τ (seg_nil τ _) fun u ⟨i, h1, h2, _⟩ => by omega
  | succ M hM ih =>
    refine seg_mono τ (seg_trans τ (ih fun i h1 h2 => h i h1 (by omega)) (h M hM (by omega)))
      fun u ⟨i, h1, h2, hu⟩ => ?_
    rcases Nat.lt_or_ge i M with hi | hi
    · exact Or.inl ⟨i, h1, hi, hu⟩
    · exact Or.inr (by rwa [show i = M by omega] at hu)

/-- Single steps along a chain. -/
lemma seg_steps (f : ℕ → V) (m M : ℕ) (hM : m ≤ M) (h : ∀ i, m ≤ i → i < M → τ (f i) = f (i + 1)) :
    Seg τ (f m) (f M) (fun u => ∃ i, m ≤ i ∧ i < M ∧ u = f i) :=
  seg_mono τ (seg_chain τ f (fun i u => u = f i) m M hM fun i h1 h2 => by
    rw [← h i h1 h2]; exact seg_step τ) fun u h => h

end seg

/-! ### Clause spans -/

section span

variable (G)

/-- No clause end in `[s', s)`: `s'` and `s` lie in the same clause. -/
def same (s' s : ℕ) : Prop := ∀ t, s' ≤ t → t < s → ¬ G.cs t

/-- The first token of the clause containing `t`. -/
def st (t : ℕ) : ℕ := Nat.findGreatest G.clStart t

open Classical in
/-- The clause end at or after `t`. -/
noncomputable def en (t : ℕ) : ℕ := if h : ∃ b, t ≤ b ∧ G.cs b then Nat.find h else 0

variable {G}

lemma st_spec (t : ℕ) : G.clStart (G.st t) ∧ G.st t ≤ t ∧ ∀ u, G.st t < u → u ≤ t → ¬ G.clStart u :=
  ⟨Nat.findGreatest_spec (P := G.clStart) (Nat.zero_le t) (Or.inl rfl), Nat.findGreatest_le t,
    fun _ h1 h2 => Nat.findGreatest_is_greatest h1 h2⟩

lemma en_spec (hw : G.WF) {t : ℕ} (ht : t < G.T) :
    G.cs (G.en t) ∧ t ≤ G.en t ∧ G.en t < G.T ∧ ∀ u, t ≤ u → u < G.en t → ¬ G.cs u := by
  classical
  have hex : ∃ b, t ≤ b ∧ G.cs b := ⟨G.T - 1, by omega, hw.2.2⟩
  have he : G.en t = Nat.find hex := by unfold en; rw [dif_pos hex]
  have hs := Nat.find_spec hex
  refine ⟨he ▸ hs.2, he ▸ hs.1, lt_of_tok hw (he ▸ hs.2), fun u h1 h2 hc => ?_⟩
  rw [he] at h2
  exact Nat.find_min hex h2 ⟨h1, hc⟩

/-- The span `[st t, en t]` contains no clause end before `en t` and no clause start after
`st t`. -/
lemma span_no_cs (hw : G.WF) {t : ℕ} (ht : t < G.T) :
    ∀ u, G.st t ≤ u → u < G.en t → ¬ G.cs u := by
  intro u h1 h2 hc
  rcases Nat.lt_or_ge u t with h | h
  · exact (st_spec (G := G) t).2.2 (u + 1) (by omega) (by omega) (Or.inr (by simpa using hc))
  · exact (en_spec hw ht).2.2.2 u h h2 hc

lemma span_no_start (hw : G.WF) {t : ℕ} (ht : t < G.T) :
    ∀ u, G.st t < u → u ≤ G.en t → ¬ G.clStart u := by
  intro u h1 h2 hc
  rcases hc with h | h
  · omega
  · exact span_no_cs hw ht (u - 1) (by omega) (by omega) h

/-- Every token of a span has the same span. -/
lemma span_eq (hw : G.WF) {t s : ℕ} (ht : t < G.T) (h1 : G.st t ≤ s) (h2 : s ≤ G.en t) :
    G.st s = G.st t ∧ G.en s = G.en t := by
  have hsT : s < G.T := by have := (en_spec hw ht).2.2.1; omega
  have hA := st_spec (G := G) t; have hB := en_spec hw ht
  have hA' := st_spec (G := G) s; have hB' := en_spec hw hsT
  have hnc := span_no_cs hw ht; have hns := span_no_start hw ht
  constructor
  · rcases lt_trichotomy (G.st s) (G.st t) with h | h | h
    · exact absurd hA.1 (hA'.2.2 _ h (by omega))
    · exact h
    · exact absurd hA'.1 (hns _ h (by omega))
  · rcases lt_trichotomy (G.en s) (G.en t) with h | h | h
    · exact absurd hB'.1 (hnc _ (by omega) h)
    · exact h
    · exact absurd hB.1 (hB'.2.2.2 _ (by omega) h)

/-- Two tokens of one span are in the same clause. -/
lemma same_of_span (hw : G.WF) {t s' s : ℕ} (ht : t < G.T) (h1 : G.st t ≤ s') (h2 : s' ≤ s)
    (h3 : s ≤ G.en t) : G.same s' s :=
  fun u hu1 hu2 => span_no_cs hw ht u (by omega) (by omega)

/-- A token in the same clause as a later token of the span lies in the span. -/
lemma span_of_same (hw : G.WF) {t s' s : ℕ} (ht : t < G.T) (h1 : G.st t ≤ s) (h2 : s ≤ G.en t)
    (hs' : s' ≤ s) (h : G.same s' s) : G.st t ≤ s' := by
  by_contra hlt
  have hc := (st_spec (G := G) t).1
  rcases hc with hc | hc
  · omega
  · exact h (G.st t - 1) (by omega) (by omega) hc

end span

/-! ### The cycle of a satisfying assignment -/

section yes

variable (G) (α : ℕ → Bool)

/-- The literal starting at token `s` is true. -/
def good (s : ℕ) : Prop := ∃ x, G.lit x s ∧ (G.pos s ↔ α x = true)

/-- `s` is the first true literal of its clause. -/
def det (s : ℕ) : Prop := G.good α s ∧ ∀ s' < s, G.same s' s → ¬ G.good α s'

open Classical in
/-- The variable of the literal at `s`. -/
noncomputable def vr (s : ℕ) : ℕ := if h : ∃ x, G.lit x s then Nat.find h else 0

/-- The cell is traversed physically left-to-right. -/
def physR (x t : ℕ) : Prop := (α x = true ↔ ¬ G.mir x t)

/-- The cell takes the clause detour. -/
def dt (x t : ℕ) : Prop := G.lit x t ∧ G.det α t

open Classical in
/-- **The successor map** of the Hamiltonian cycle. -/
noncomputable def τy : V → V
  | .cell x t q =>
    if ¬ G.physR α x t then
      match q with
      | 0 => .cell x t 1 | 1 => G.port1 x t | 2 => .cell x t 3 | 3 => .cell x t 0
      | 4 => .cell x t 5 | _ => .cell x t 2
    else if G.dt α x t then
      match q with
      | 0 => .cell x t 3 | 1 => .cell x t 2 | 2 => .cell x t 5 | 3 => .cell x t 4
      | 4 => .rr t | _ => G.port5 x t
    else
      match q with
      | 0 => .cell x t 1 | 1 => .cell x t 2 | 2 => .cell x t 3 | 3 => .cell x t 4
      | 4 => .cell x t 5 | _ => G.port5 x t
  | .top x => if α x = true then G.eL x 0 else G.eR x (G.T - 1)
  | .bot x => .top ((x + 1) % G.T)
  | .rr t => if G.cs t then .qq t
      else if G.det α (t + 1) then .cell (G.vr (t + 1)) (t + 1) 1 else .rr (t + 1)
  | .qq t => if G.clStart t then (if G.det α t then .cell (G.vr t) t 1 else .rr t) else .qq (t - 1)

variable {G α}

lemma vr_spec {s : ℕ} (h : ∃ x, G.lit x s) : G.lit (G.vr s) s := by
  classical
  unfold vr; rw [dif_pos h]; exact Nat.find_spec h

lemma vr_eq {x s : ℕ} (h : G.lit x s) : G.vr s = x := lit_unique (vr_spec ⟨x, h⟩) h

lemma det_lit {s : ℕ} (h : G.det α s) : G.lit (G.vr s) s := by
  obtain ⟨⟨x, hx, -⟩, -⟩ := h; exact vr_spec ⟨x, hx⟩

lemma det_unique {s1 s2 : ℕ} (h1 : G.det α s1) (h2 : G.det α s2) (hle : s1 ≤ s2)
    (hs : G.same s1 s2) : s1 = s2 := by
  by_contra hne
  exact h2.2 s1 (by omega) hs h1.1

lemma dt_physR {x t : ℕ} (h : G.dt α x t) : G.physR α x t := by
  obtain ⟨hl, ⟨x', hx', hp⟩, -⟩ := h
  rw [lit_unique hx' hl] at hp
  unfold physR mir
  constructor
  · intro ha ⟨_, hnp⟩; exact hnp (hp.mpr ha)
  · intro hn; exact hp.mp (by by_contra hnp; exact hn ⟨hl, hnp⟩)

end yes

section yes2

variable {α : ℕ → Bool}

lemma det_ne (hw : G.WF) {s u : ℕ} (hsT : s < G.T) (hd : G.det α s) (h1 : G.st s ≤ u)
    (h2 : u ≤ G.en s) (hne : u ≠ s) : ¬ G.det α u := by
  intro hu
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hd.2 u h (same_of_span hw hsT h1 h.le (en_spec hw hsT).2.1) hu.1
  · exact hu.2 s h (same_of_span hw hsT (st_spec (G := G) s).2.1 h.le h2) hd.1

lemma τy_arc (hw : G.WF) {v : V} (hv : G.valid v) : G.τy α v ∈ G.outsV v := by
  rcases v with ⟨x, t, q⟩ | x | x | t | t
  · obtain ⟨hx, ht, hq⟩ := hv
    by_cases h1 : G.physR α x t
    · by_cases h2 : G.dt α x t
      · simp only [τy, h1, h2, not_true_eq_false, if_false, if_true]
        interval_cases q <;> simp [outsV, h2.1] <;> exact Or.inr rfl
      · simp only [τy, h1, h2, not_true_eq_false, if_false]
        interval_cases q <;> simp [outsV] <;> exact Or.inr rfl
    · simp only [τy, h1, not_false_eq_true, if_true]
      interval_cases q <;> simp [outsV] <;> exact Or.inr rfl
  · simp only [τy, outsV]; split_ifs <;> simp
  · simp [τy, outsV]
  · simp only [τy, outsV]
    split_ifs with h1 h2
    · simp
    · refine List.mem_cons_of_mem _ (G.mem_litCells.mpr ⟨_, ?_, det_lit h2, rfl⟩)
      have := lit_lt' hw (det_lit h2); omega
    · simp
  · simp only [τy, outsV]
    split_ifs with h1 h2
    · refine List.mem_cons_of_mem _ (G.mem_litCells.mpr ⟨_, ?_, det_lit h2, rfl⟩)
      have := lit_lt' hw (det_lit h2); omega
    · simp
    · simp

lemma seg_one {v w : V} (h : G.τy α v = w) : Seg (G.τy α) v w (· = v) := h ▸ seg_step _

/-- **The clause detour**: from `r s` around the whole clause cycle to the cell's node `1`. -/
lemma seg_clause (hw : G.WF) {s : ℕ} (hsT : s < G.T) (hd : G.det α s) :
    Seg (G.τy α) (.rr s) (.cell (G.vr s) s 1) (InSpan (G.st s) (G.en s)) := by
  classical
  have hA := st_spec (G := G) s
  have hB := en_spec hw hsT
  have hnc0 := span_no_cs hw hsT
  have hns0 := span_no_start hw hsT
  set a := G.st s with ha_def
  set b := G.en s with hb_def
  have hnc : ∀ u, a ≤ u → u < b → ¬ G.cs u := hnc0
  have hns : ∀ u, a < u → u ≤ b → ¬ G.clStart u := hns0
  have hnd : ∀ u, a ≤ u → u ≤ b → u ≠ s → ¬ G.det α u := fun u h1 h2 h3 => det_ne hw hsT hd h1 h2 h3
  have hab : a ≤ s := hA.2.1
  have hsb : s ≤ b := hB.2.1
  -- r s → ⋯ → r b
  have P1 := seg_steps (G.τy α) (fun i => V.rr i) s b hsb fun i h1 h2 => by
    simp only [τy, if_neg (hnc i (by omega) h2), if_neg (hnd (i + 1) (by omega) (by omega) (by omega))]
  have S1 : G.τy α (.rr b) = .qq b := by simp only [τy, if_pos hB.1]
  -- q b → ⋯ → q a
  have P2 := seg_steps (G.τy α) (fun i => V.qq (b - i)) 0 (b - a) (Nat.zero_le _) fun i h1 h2 => by
    simp only [τy, if_neg (hns (b - i) (by omega) (by omega)), Nat.sub_sub]
  simp only [Nat.sub_zero, show b - (b - a) = a by omega] at P2
  rcases Nat.eq_or_lt_of_le hab with heq | hlt
  · -- the detour enters at the clause's first token
    have S2 : G.τy α (.qq a) = .cell (G.vr s) s 1 := by
      have hcs : G.clStart s := heq ▸ hA.1
      simp only [τy, heq, if_pos hcs, if_pos hd]
    refine seg_mono _ (seg_trans _ (seg_trans _ (seg_trans _ P1 (seg_one S1)) P2) (seg_one S2))
      fun u ⟨t, h1, h2, hu⟩ => ?_
    rcases hu with rfl | rfl
    · rcases Nat.lt_or_ge t b with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨t, by omega, h, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr (by congr 1; omega)))
    · rcases Nat.lt_or_ge a t with h | h
      · exact Or.inl (Or.inr ⟨b - t, by omega, by omega, by congr 1; omega⟩)
      · exact Or.inr (by congr 1; omega)
  · have S2 : G.τy α (.qq a) = .rr a := by
      simp only [τy, if_pos hA.1, if_neg (hnd a le_rfl (by omega) (by omega))]
    have P3 := seg_steps (G.τy α) (fun i => V.rr i) a (s - 1) (by omega) fun i h1 h2 => by
      simp only [τy, if_neg (hnc i (by omega) (by omega)),
        if_neg (hnd (i + 1) (by omega) (by omega) (by omega))]
    have S3 : G.τy α (.rr (s - 1)) = .cell (G.vr s) s 1 := by
      simp only [τy, if_neg (hnc (s - 1) (by omega) (by omega)), show s - 1 + 1 = s by omega,
        if_pos hd]
    refine seg_mono _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _ P1
      (seg_one S1)) P2) (seg_one S2)) P3) (seg_one S3)) fun u ⟨t, h1, h2, hu⟩ => ?_
    rcases hu with rfl | rfl
    · rcases Nat.lt_or_ge t s with h | h
      · rcases Nat.lt_or_ge t (s - 1) with h' | h'
        · exact Or.inl (Or.inr ⟨t, h1, h', rfl⟩)
        · exact Or.inr (by congr 1; omega)
      · rcases Nat.lt_or_ge t b with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨t, h, h', rfl⟩))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by congr 1; omega)))))
    · rcases Nat.lt_or_ge a t with h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨b - t, by omega, by omega, by congr 1; omega⟩)))
      · exact Or.inl (Or.inl (Or.inr (by congr 1; omega)))

end yes2

section yes3

variable {α : ℕ → Bool}

/-- What a cell's traversal covers. -/
def cellSet (α : ℕ → Bool) (x t : ℕ) (u : V) : Prop :=
  (∃ q < 6, u = .cell x t q) ∨ (G.dt α x t ∧ InSpan (G.st t) (G.en t) u)

/-- **A cell's traversal**, from its logical entry to its logical exit. -/
lemma seg_cell (hw : G.WF) {x t : ℕ} (ht : t < G.T) :
    Seg (G.τy α) (if α x = true then G.eL x t else G.eR x t)
      (if α x = true then G.Rp x t else G.Lp x t) (G.cellSet α x t) := by
  by_cases hP : G.physR α x t
  · have hen : (if α x = true then G.eL x t else G.eR x t) = .cell x t 0 ∧
        (if α x = true then G.Rp x t else G.Lp x t) = G.port5 x t := by
      unfold physR at hP; unfold eL eR port5
      by_cases ha : α x = true <;> by_cases hm : G.mir x t <;> simp_all
    rw [hen.1, hen.2]
    by_cases hD : G.dt α x t
    · have e : ∀ q, G.τy α (.cell x t q) = match q with
          | 0 => .cell x t 3 | 1 => .cell x t 2 | 2 => .cell x t 5 | 3 => .cell x t 4
          | 4 => .rr t | _ => G.port5 x t := fun q => by
        simp only [τy, hP, hD, not_true_eq_false, if_false, if_true]
      have hv : G.vr t = x := vr_eq hD.1
      have C := seg_clause hw ht hD.2 (α := α)
      rw [hv] at C
      refine seg_mono _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _
        (seg_trans _ (seg_one (e 0)) (seg_one (e 3))) (seg_one (e 4))) C) (seg_one (e 1)))
        (seg_one (e 2))) (seg_one (e 5))) fun u hu => ?_
      rcases hu with ⟨q, hq, rfl⟩ | ⟨-, hu⟩
      · interval_cases q <;> simp
      · exact Or.inl (Or.inl (Or.inl (Or.inr hu)))
    · have e : ∀ q, G.τy α (.cell x t q) = match q with
          | 0 => .cell x t 1 | 1 => .cell x t 2 | 2 => .cell x t 3 | 3 => .cell x t 4
          | 4 => .cell x t 5 | _ => G.port5 x t := fun q => by
        simp only [τy, hP, hD, not_true_eq_false, if_false]
      refine seg_mono _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _
        (seg_one (e 0)) (seg_one (e 1))) (seg_one (e 2))) (seg_one (e 3))) (seg_one (e 4)))
        (seg_one (e 5))) fun u hu => ?_
      rcases hu with ⟨q, hq, rfl⟩ | ⟨h, -⟩
      · interval_cases q <;> simp
      · exact absurd h hD
  · have hen : (if α x = true then G.eL x t else G.eR x t) = .cell x t 4 ∧
        (if α x = true then G.Rp x t else G.Lp x t) = G.port1 x t := by
      unfold physR at hP; unfold eL eR port1
      by_cases ha : α x = true <;> by_cases hm : G.mir x t <;> simp_all
    rw [hen.1, hen.2]
    have e : ∀ q, G.τy α (.cell x t q) = match q with
        | 0 => .cell x t 1 | 1 => G.port1 x t | 2 => .cell x t 3 | 3 => .cell x t 0
        | 4 => .cell x t 5 | _ => .cell x t 2 := fun q => by
      simp only [τy, hP, not_false_eq_true, if_true]
    refine seg_mono _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _ (seg_trans _
      (seg_one (e 4)) (seg_one (e 5))) (seg_one (e 2))) (seg_one (e 3))) (seg_one (e 0)))
      (seg_one (e 1))) fun u hu => ?_
    rcases hu with ⟨q, hq, rfl⟩ | ⟨h, -⟩
    · interval_cases q <;> simp
    · exact absurd (dt_physR h) hP

/-- What a row's traversal covers. -/
def rowSet (α : ℕ → Bool) (x : ℕ) (u : V) : Prop :=
  u = .top x ∨ u = .bot x ∨ ∃ t < G.T, G.cellSet α x t u

/-- **A row's traversal**, from `top x` to `top (x + 1)`. -/
lemma seg_row (hw : G.WF) {x : ℕ} :
    Seg (G.τy α) (.top x) (.top ((x + 1) % G.T)) (G.rowSet α x) := by
  have hT := hw.2.1
  have hbot : G.τy α (.bot x) = .top ((x + 1) % G.T) := rfl
  by_cases ha : α x = true
  · let f : ℕ → V := fun t => if t < G.T then G.eL x t else .bot x
    have h0 : G.τy α (.top x) = f 0 := by simp [τy, ha, f, hT]
    have C := seg_chain (G.τy α) f (fun t => G.cellSet α x t) 0 G.T (Nat.zero_le _)
      fun t _ ht => by
        have := seg_cell hw ht (α := α) (x := x)
        simp only [ha, if_true] at this
        have e1 : f t = G.eL x t := by simp [f, ht]
        have e2 : f (t + 1) = G.Rp x t := by
          simp only [f, Rp]; try (split_ifs <;> rfl)
        rwa [e1, e2]
    have eT : f G.T = .bot x := by simp [f]
    rw [eT] at C
    refine seg_mono _ (seg_trans _ (seg_trans _ (seg_one h0) C) (seg_one hbot)) fun u hu => ?_
    rcases hu with rfl | rfl | ⟨t, ht, hu⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr rfl
    · exact Or.inl (Or.inr ⟨t, Nat.zero_le _, ht, hu⟩)
  · let f : ℕ → V := fun i => if i < G.T then G.eR x (G.T - 1 - i) else .bot x
    have h0 : G.τy α (.top x) = f 0 := by simp [τy, ha, f, hT]
    have C := seg_chain (G.τy α) f (fun i => G.cellSet α x (G.T - 1 - i)) 0 G.T (Nat.zero_le _)
      fun i _ hi => by
        have := seg_cell hw (show G.T - 1 - i < G.T by omega) (α := α) (x := x)
        simp only [ha, Bool.false_eq_true, if_false] at this
        have e1 : f i = G.eR x (G.T - 1 - i) := by simp [f, hi]
        have e2 : f (i + 1) = G.Lp x (G.T - 1 - i) := by
          simp only [f, Lp]
          try split_ifs
          all_goals first | omega | rfl | (congr 1; omega)
        rwa [e1, e2]
    have eT : f G.T = .bot x := by simp [f]
    rw [eT] at C
    refine seg_mono _ (seg_trans _ (seg_trans _ (seg_one h0) C) (seg_one hbot)) fun u hu => ?_
    rcases hu with rfl | rfl | ⟨t, ht, hu⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr rfl
    · refine Or.inl (Or.inr ⟨G.T - 1 - t, Nat.zero_le _, by omega, ?_⟩)
      rwa [show G.T - 1 - (G.T - 1 - t) = t by omega]

/-- **All rows**, from `top 0` back to `top 0`. -/
lemma seg_all (hw : G.WF) :
    Seg (G.τy α) (.top 0) (.top 0) (fun u => ∃ x < G.T, G.rowSet α x u) := by
  have hT := hw.2.1
  have C := seg_chain (G.τy α) (fun x => V.top (x % G.T)) (fun x => G.rowSet α (x % G.T)) 0 G.T
    (Nat.zero_le _) fun x _ _ => by
      have := seg_row hw (α := α) (x := x % G.T)
      rwa [succ_mod_eq] at this
  simp only [Nat.zero_mod, Nat.mod_self] at C
  refine seg_mono _ C fun u ⟨x, hx, hu⟩ => ⟨x, Nat.zero_le _, hx, by rwa [Nat.mod_eq_of_lt hx]⟩

/-- **Every vertex is covered**, when every clause has a true literal. -/
lemma cover (hw : G.WF)
    (hs : ∀ b, G.cs b → ∃ s x, s ≤ b ∧ G.same s b ∧ G.lit x s ∧ (G.pos s ↔ α x = true))
    {v : V} (hv : G.valid v) : ∃ x < G.T, G.rowSet α x v := by
  classical
  have span : ∀ t < G.T, ∀ u, (u = V.rr t ∨ u = V.qq t) → ∃ x < G.T, G.rowSet α x u := by
    intro t ht u hu
    have hB := en_spec hw ht
    obtain ⟨s0, x0, h1, h2, h3, h4⟩ := hs _ hB.1
    have hA := st_spec (G := G) t
    have hs0 : G.st t ≤ s0 := span_of_same hw ht (by omega) le_rfl h1 h2
    have hex : ∃ s, G.st t ≤ s ∧ s ≤ G.en t ∧ G.good α s := ⟨s0, hs0, h1, x0, h3, h4⟩
    set s := Nat.find hex
    obtain ⟨hs1, hs2, hsg⟩ := Nat.find_spec hex
    have hd : G.det α s := ⟨hsg, fun s' hlt hsame hg =>
      Nat.find_min hex hlt ⟨span_of_same hw ht hs1 hs2 hlt.le hsame, by omega, hg⟩⟩
    have hl := det_lit hd
    have hsT : s < G.T := by have := lit_lt' hw hl; omega
    obtain ⟨e1, e2⟩ := span_eq hw ht hs1 hs2
    refine ⟨G.vr s, by have := lit_lt' hw hl; omega, Or.inr (Or.inr ⟨s, hsT, Or.inr ⟨⟨hl, hd⟩, ?_⟩⟩)⟩
    rw [e1, e2]
    exact ⟨t, hA.2.1, hB.2.1, hu⟩
  rcases v with ⟨x, t, q⟩ | x | x | t | t
  · exact ⟨x, hv.1, Or.inr (Or.inr ⟨t, hv.2.1, Or.inl ⟨q, hv.2.2, rfl⟩⟩)⟩
  · exact ⟨x, hv, Or.inl rfl⟩
  · exact ⟨x, hv, Or.inr (Or.inl rfl)⟩
  · exact span t hv _ (Or.inl rfl)
  · exact span t hv _ (Or.inr rfl)

/-- **Token-level YES direction.** -/
theorem dhc_of_sat (hw : G.WF)
    (hs : ∀ b, G.cs b → ∃ s x, s ≤ b ∧ G.same s b ∧ G.lit x s ∧ (G.pos s ↔ α x = true)) :
    DHC G.dig := by
  have hT := hw.2.1
  let σ : ℕ → ℕ := fun u => G.enc (G.τy α (G.dec u))
  have hval : ∀ v, G.valid v → G.valid (G.τy α v) := fun v hv =>
    (outsV_valid hw hv _ (τy_arc hw hv)).1
  have hσ : ∀ v < G.dig.n, σ v < G.dig.n ∧ (v, σ v) ∈ G.dig.arcs := fun v hv => by
    have hd := G.dec_valid hv
    refine ⟨G.enc_lt (hval _ hd), G.mem_arcs.mpr ⟨hv, ?_⟩⟩
    exact List.mem_map.mpr ⟨_, τy_arc hw hd, rfl⟩
  have hit : ∀ v, G.valid v → ∀ k, σ^[k] (G.enc v) = G.enc ((G.τy α)^[k] v) ∧
      G.valid ((G.τy α)^[k] v) := by
    intro v hv k
    induction k with
    | zero => exact ⟨rfl, hv⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
      exact ⟨by simp only [σ, G.dec_enc ih.2], hval _ ih.2⟩
  have htop : G.valid (.top 0) := show 0 < G.T from hT
  obtain ⟨k, hk, hP⟩ := seg_all hw (α := α)
  obtain ⟨j, hj, -⟩ := hP (.top 0) ⟨0, hT, Or.inl rfl⟩
  refine dhc_of_cycle G.dig (by show 2 ≤ G.n; unfold n N6; nlinarith) σ hσ
    (b := G.enc (.top 0)) (p := k) (G.enc_lt htop) (by omega) ?_ fun v hv => ?_
  · rw [(hit _ htop k).1, hk]
  · obtain ⟨x, hx, hu⟩ := cover hw hs (G.dec_valid hv)
    obtain ⟨j, -, hj⟩ := hP _ ⟨x, hx, hu⟩
    exact ⟨j, by rw [(hit _ htop j).1, hj, G.enc_dec hv]⟩

end yes3

end TS

end Pts
