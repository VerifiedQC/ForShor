import Points.SatGraph
import Points.DigSigma

/-!
# SAT → DHC₂: a Hamiltonian cycle gives a satisfying assignment

From a directed Hamiltonian cycle of `G.dig` (as a successor map `τ` on vertices):
* every cell is traversed rightward, rightward with a detour, or leftward (`cell_cases`, by
  `decide` over the 64 local choices);
* the direction taken at `top x` propagates along the row (`rowR`, `rowL`), which defines the
  assignment `α x`;
* every clause is entered from outside only through a detour `cell x t 4 → r t` of one of its
  literals (`clause_entry`), and a detour is only possible when that literal is true.
-/

namespace Pts

open Complexity SAT

namespace TS

variable {G : TS}

/-- A Hamiltonian cycle as a successor map on vertices. -/
structure Cyc (G : TS) where
  τ : V → V
  val : ∀ v, G.valid v → G.valid (τ v)
  arc : ∀ v, G.valid v → τ v ∈ G.outsV v
  inj : ∀ v w, G.valid v → G.valid w → τ v = τ w → v = w
  reach : ∀ v w, G.valid v → G.valid w → ∃ k, τ^[k] v = w

lemma cyc_of_dhc (hw : G.WF) (h : DHC G.dig) : Nonempty (Cyc G) := by
  obtain ⟨σ, hσ, hinj, hreach⟩ := sigma_of_dhc h
  have hstep : ∀ v, G.valid v → ∃ w ∈ G.outsV v, σ (G.enc v) = G.enc w := fun v hv => by
    have h1 := (G.mem_arcs.mp (hσ _ (G.enc_lt hv)).2).2
    rw [outs, G.dec_enc hv] at h1
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h1
    exact ⟨w, hw, he.symm⟩
  let τ : V → V := fun v => G.dec (σ (G.enc v))
  have harc : ∀ v, G.valid v → τ v ∈ G.outsV v := fun v hv => by
    obtain ⟨w, hw', he⟩ := hstep v hv
    simp only [τ, he, G.dec_enc (outsV_valid hw hv w hw').1]; exact hw'
  have hval : ∀ v, G.valid v → G.valid (τ v) := fun v hv => G.dec_valid (hσ _ (G.enc_lt hv)).1
  have hit : ∀ v, G.valid v → ∀ k, τ^[k] v = G.dec (σ^[k] (G.enc v)) ∧ σ^[k] (G.enc v) < G.n := by
    intro v hv k
    induction k with
    | zero => exact ⟨(G.dec_enc hv).symm, G.enc_lt hv⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
      exact ⟨by simp only [τ, G.enc_dec ih.2], (hσ _ ih.2).1⟩
  refine ⟨⟨τ, hval, harc, fun v w hv hw h => ?_, fun v w hv hw => ?_⟩⟩
  · have := congrArg G.enc h
    simp only [τ, G.enc_dec (hσ _ (G.enc_lt hv)).1, G.enc_dec (hσ _ (G.enc_lt hw)).1] at this
    exact G.enc_inj hv hw (hinj _ (G.enc_lt hv) _ (G.enc_lt hw) this)
  · obtain ⟨k, hk⟩ := hreach _ (G.enc_lt hv) _ (G.enc_lt hw)
    exact ⟨k, by rw [(hit v hv k).1, hk, G.dec_enc hw]⟩

namespace Cyc

variable (c : Cyc G)

lemma iter_valid {v : V} (hv : G.valid v) (k : ℕ) : G.valid (c.τ^[k] v) := by
  induction k with
  | zero => exact hv
  | succ k ih => rw [Function.iterate_succ_apply']; exact c.val _ ih

lemma closed (S : V → Prop) {v : V} (hv : G.valid v) (hS : S v)
    (hcl : ∀ u, G.valid u → S u → S (c.τ u)) {w : V} (hw : G.valid w) : S w := by
  obtain ⟨k, rfl⟩ := c.reach v w hv hw
  induction k with
  | zero => exact hS
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hcl _ (c.iter_valid hv k) (ih (c.iter_valid hv k))

lemma entry (S : V → Prop) {v w : V} (hv : G.valid v) (hnv : ¬ S v) (hw : G.valid w) (hSw : S w) :
    ∃ u, G.valid u ∧ ¬ S u ∧ S (c.τ u) := by
  by_contra hno
  push Not at hno
  exact c.closed (fun u => ¬ S u) hv hnv (fun u hu h => hno u hu h) hw hSw

lemma surj {w : V} (hw : G.valid w) : ∃ u, G.valid u ∧ c.τ u = w := by
  obtain ⟨k, hk⟩ := c.reach (c.τ w) w (c.val w hw) hw
  refine ⟨c.τ^[k] w, c.iter_valid hw k, ?_⟩
  rw [← Function.iterate_succ_apply' c.τ, Function.iterate_succ_apply, hk]

end Cyc

/-! ### The finite cell lemma -/

theorem cell_cases (b0 b1 b2 b3 b4 b5 : Bool)
    (i1 : ¬(b0 = false ∧ b2 = true)) (i2 : ¬(b1 = true ∧ b5 = true))
    (i3 : ¬(b2 = false ∧ b4 = true))
    (s2 : b1 = true ∨ b5 = true) (s3 : b0 = false ∨ b2 = true) (s5 : b2 = false ∨ b4 = true)
    (a1 : ¬(b0 = true ∧ b1 = true ∧ b2 = true ∧ b3 = true)) (a2 : ¬(b0 = false ∧ b3 = true))
    (a3 : ¬(b2 = false ∧ b5 = true)) (a4 : ¬(b2 = true ∧ b3 = false ∧ b4 = true ∧ b5 = true)) :
    (b3 = false → b5 = false) ∧ (b3 = true → b1 = false) ∧ (b4 = false → b3 = false) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp_all

/-! ### Which arcs enter a cell's inner nodes -/

lemma pred_inner {u : V} {x t q : ℕ} (h : V.cell x t q ∈ G.outsV u) (hq : q = 2 ∨ q = 3 ∨ q = 5) :
    ∃ q', u = .cell x t q' := by
  have hp : ∀ {x' t'}, V.cell x t q ≠ G.Lp x' t' := fun h => by
    unfold Lp eR at h; split_ifs at h <;> simp only [reduceCtorEq, V.cell.injEq] at h <;> omega
  have hr : ∀ {x' t'}, V.cell x t q ≠ G.Rp x' t' := fun h => by
    unfold Rp eL at h; split_ifs at h <;> simp only [reduceCtorEq, V.cell.injEq] at h <;> omega
  have hl : ∀ {s}, V.cell x t q ∉ G.litCells s := fun h => by
    obtain ⟨_, _, _, h⟩ := G.mem_litCells.mp h; simp only [V.cell.injEq] at h; omega
  rcases u with ⟨x', t', q'⟩ | x' | x' | t' | t'
  · by_cases hx : x' = x ∧ t' = t
    · obtain ⟨rfl, rfl⟩ := hx; exact ⟨q', rfl⟩
    · exfalso
      rcases q' with _ | _ | _ | _ | _ | _ | q' <;>
        simp only [outsV, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      all_goals (try split_ifs at h) <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, V.cell.injEq,
          reduceCtorEq] at h
      all_goals first
        | omega
        | (rcases h with h | h <;> first | omega | exact hp h | exact hr h)
        | exact hp h | exact hr h
        | (rcases h with h | h <;> simp_all)
  · simp only [outsV, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, eL, eR,
      V.cell.injEq] at h
    exfalso; rcases h with h | h <;> split_ifs at h <;> omega
  · simp [outsV] at h
  · simp only [outsV] at h; split_ifs at h <;> simp only [List.mem_cons, List.mem_singleton,
      reduceCtorEq, false_or] at h <;> first | exact absurd h hl | simp at h
  · simp only [outsV] at h; split_ifs at h <;> simp only [List.mem_cons, List.mem_singleton,
      reduceCtorEq, false_or] at h <;> first | exact absurd h hl | cases h

/-! ### Cell modes along a Hamiltonian cycle -/

def port1 (x t : ℕ) : V := if G.mir x t then G.Rp x t else G.Lp x t
def port5 (x t : ℕ) : V := if G.mir x t then G.Lp x t else G.Rp x t

lemma port1_ne (x t q : ℕ) : G.port1 x t ≠ .cell x t q := fun h => by
  unfold port1 at h; split_ifs at h
  · exact Rp_valid' h.symm
  · exact Lp_valid' h.symm

lemma port5_ne (x t q : ℕ) : G.port5 x t ≠ .cell x t q := fun h => by
  unfold port5 at h; split_ifs at h
  · exact Lp_valid' h.symm
  · exact Rp_valid' h.symm

lemma dec_false_iff {a p q : V} (h : a = p ∨ a = q) (hpq : p ≠ q) :
    decide (a = p) = false ↔ a = q := by
  rcases h with rfl | rfl <;> simp [hpq, Ne.symm hpq]

namespace Cyc

variable (c : Cyc G)

lemma no_closed (S : V → Prop) {v w : V} (hv : G.valid v) (hS : S v)
    (hcl : ∀ u, G.valid u → S u → S (c.τ u)) (hw : G.valid w) (hnw : ¬ S w) : False :=
  hnw (c.closed S hv hS hcl hw)

section cell

variable {x t : ℕ} (hx : x < G.T) (ht : t < G.T)
include hx ht

lemma vc (q : ℕ) (hq : q < 6) : G.valid (.cell x t q) := ⟨hx, ht, hq⟩

lemma o0 : c.τ (.cell x t 0) = .cell x t 1 ∨ c.τ (.cell x t 0) = .cell x t 3 := by
  simpa [outsV] using c.arc _ (vc hx ht 0 (by norm_num))
lemma o1 : c.τ (.cell x t 1) = .cell x t 2 ∨ c.τ (.cell x t 1) = G.port1 x t := by
  simpa [outsV, port1] using c.arc _ (vc hx ht 1 (by norm_num))
lemma o2 : c.τ (.cell x t 2) = .cell x t 3 ∨ c.τ (.cell x t 2) = .cell x t 5 := by
  simpa [outsV] using c.arc _ (vc hx ht 2 (by norm_num))
lemma o3 : c.τ (.cell x t 3) = .cell x t 0 ∨ c.τ (.cell x t 3) = .cell x t 4 := by
  simpa [outsV] using c.arc _ (vc hx ht 3 (by norm_num))
lemma o4 : c.τ (.cell x t 4) = .cell x t 5 ∨ (G.lit x t ∧ c.τ (.cell x t 4) = .rr t) := by
  have := c.arc _ (vc hx ht 4 (by norm_num))
  simp only [outsV] at this
  split_ifs at this with hl <;> simp_all
lemma o5 : c.τ (.cell x t 5) = .cell x t 2 ∨ c.τ (.cell x t 5) = G.port5 x t := by
  simpa [outsV, port5] using c.arc _ (vc hx ht 5 (by norm_num))

/-- **Mode consequences** of `cell_cases` for the cell `(x, t)`. -/
theorem modes :
    (c.τ (.cell x t 3) = .cell x t 4 → c.τ (.cell x t 5) = G.port5 x t) ∧
    (c.τ (.cell x t 3) = .cell x t 0 → c.τ (.cell x t 1) = G.port1 x t) ∧
    (c.τ (.cell x t 4) ≠ .cell x t 5 → c.τ (.cell x t 3) = .cell x t 4) := by
  have h0 := c.o0 hx ht; have h1 := c.o1 hx ht; have h2 := c.o2 hx ht
  have h3 := c.o3 hx ht; have h4 := c.o4 hx ht; have h5 := c.o5 hx ht
  have V' := vc (G := G) hx ht
  have inj : ∀ q r, q < 6 → r < 6 → c.τ (.cell x t q) = c.τ (.cell x t r) → q = r :=
    fun q r hq hr h => by simpa using c.inj _ _ (V' q hq) (V' r hr) h
  have e0 := dec_false_iff h0 (by simp)
  have e1 := dec_false_iff h1 (Ne.symm (G.port1_ne x t 2))
  have e2 := dec_false_iff h2 (by simp)
  have e3 := dec_false_iff h3 (by simp)
  have e5 := dec_false_iff h5 (Ne.symm (G.port5_ne x t 2))
  have hp1 := G.port1_ne x t; have hp5 := G.port5_ne x t
  -- predecessors of the inner nodes
  have pre : ∀ q, (q = 2 ∨ q = 3 ∨ q = 5) → ∃ r < 6, c.τ (.cell x t r) = .cell x t q := by
    intro q hq
    obtain ⟨u, hu, hτ⟩ := c.surj (V' q (by omega))
    obtain ⟨r, rfl⟩ := pred_inner (hτ ▸ c.arc u hu) hq
    exact ⟨r, hu.2.2, hτ⟩
  have top_v : G.valid (.top x) := hx
  have ncl : ∀ (S : V → Prop), (S (.cell x t 0) ∨ S (.cell x t 2)) →
      (∀ u, G.valid u → S u → S (c.τ u)) → ¬ S (.top x) → False := by
    intro S hS hcl hnt
    rcases hS with hS | hS
    · exact c.no_closed S (V' 0 (by norm_num)) hS hcl top_v hnt
    · exact c.no_closed S (V' 2 (by norm_num)) hS hcl top_v hnt
  obtain ⟨m1, m2, m3⟩ := cell_cases (decide (c.τ (.cell x t 0) = .cell x t 1))
    (decide (c.τ (.cell x t 1) = .cell x t 2)) (decide (c.τ (.cell x t 2) = .cell x t 3))
    (decide (c.τ (.cell x t 3) = .cell x t 0)) (decide (c.τ (.cell x t 4) = .cell x t 5))
    (decide (c.τ (.cell x t 5) = .cell x t 2))
    (by rw [e0]; simp only [decide_eq_true_eq]; rintro ⟨ha, hb⟩
        exact absurd (inj 0 2 (by norm_num) (by norm_num) (ha.trans hb.symm)) (by norm_num))
    (by simp only [decide_eq_true_eq]; rintro ⟨ha, hb⟩
        exact absurd (inj 1 5 (by norm_num) (by norm_num) (ha.trans hb.symm)) (by norm_num))
    (by rw [e2]; simp only [decide_eq_true_eq]; rintro ⟨ha, hb⟩
        exact absurd (inj 2 4 (by norm_num) (by norm_num) (ha.trans hb.symm)) (by norm_num))
    (by
      obtain ⟨r, hr, hτ⟩ := pre 2 (by simp)
      simp only [decide_eq_true_eq]
      interval_cases r
      · rcases h0 with h | h <;> rw [h] at hτ <;> simp at hτ
      · exact Or.inl hτ
      · rcases h2 with h | h <;> rw [h] at hτ <;> simp at hτ
      · rcases h3 with h | h <;> rw [h] at hτ <;> simp at hτ
      · rcases h4 with h | ⟨-, h⟩ <;> rw [h] at hτ <;> simp at hτ
      · exact Or.inr hτ)
    (by
      obtain ⟨r, hr, hτ⟩ := pre 3 (by simp)
      rw [e0]; simp only [decide_eq_true_eq]
      interval_cases r
      · exact Or.inl hτ
      · rcases h1 with h | h <;> rw [h] at hτ
        · simp at hτ
        · exact absurd hτ (hp1 3)
      · exact Or.inr hτ
      · rcases h3 with h | h <;> rw [h] at hτ <;> simp at hτ
      · rcases h4 with h | ⟨-, h⟩ <;> rw [h] at hτ <;> simp at hτ
      · rcases h5 with h | h <;> rw [h] at hτ
        · simp at hτ
        · exact absurd hτ (hp5 3))
    (by
      obtain ⟨r, hr, hτ⟩ := pre 5 (by simp)
      rw [e2]; simp only [decide_eq_true_eq]
      interval_cases r
      · rcases h0 with h | h <;> rw [h] at hτ <;> simp at hτ
      · rcases h1 with h | h <;> rw [h] at hτ
        · simp at hτ
        · exact absurd hτ (hp1 5)
      · exact Or.inl hτ
      · rcases h3 with h | h <;> rw [h] at hτ <;> simp at hτ
      · exact Or.inr hτ
      · rcases h5 with h | h <;> rw [h] at hτ
        · simp at hτ
        · exact absurd hτ (hp5 5))
    (by
      simp only [decide_eq_true_eq]; rintro ⟨ha, hb, hc, hd⟩
      refine ncl (fun w => w = .cell x t 0 ∨ w = .cell x t 1 ∨ w = .cell x t 2 ∨ w = .cell x t 3)
        (Or.inl (Or.inl rfl)) ?_ (by simp)
      rintro u - (rfl | rfl | rfl | rfl) <;> simp [ha, hb, hc, hd])
    (by
      rw [e0]; simp only [decide_eq_true_eq]; rintro ⟨ha, hd⟩
      refine ncl (fun w => w = .cell x t 0 ∨ w = .cell x t 3) (Or.inl (Or.inl rfl)) ?_ (by simp)
      rintro u - (rfl | rfl) <;> simp [ha, hd])
    (by
      rw [e2]; simp only [decide_eq_true_eq]; rintro ⟨hc, hf⟩
      refine ncl (fun w => w = .cell x t 2 ∨ w = .cell x t 5) (Or.inr (Or.inl rfl)) ?_ (by simp)
      rintro u - (rfl | rfl) <;> simp [hc, hf])
    (by
      rw [e3]; simp only [decide_eq_true_eq]; rintro ⟨hc, hd, he, hf⟩
      refine ncl (fun w => w = .cell x t 2 ∨ w = .cell x t 3 ∨ w = .cell x t 4 ∨ w = .cell x t 5)
        (Or.inr (Or.inl rfl)) ?_ (by simp)
      rintro u - (rfl | rfl | rfl | rfl) <;> simp [hc, hd, he, hf])
  rw [e3, e5] at m1
  rw [e1] at m2
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at m2 m3
  refine ⟨m1, m2, fun h => ?_⟩
  rcases h3 with h' | h'
  · exact absurd h' (m3 h)
  · exact h'

end cell

end Cyc

/-! ### Logical directions and rows -/

lemma valid_cell {x t q : ℕ} (hx : x < G.T) (ht : t < G.T) (hq : q < 6) : G.valid (.cell x t q) :=
  ⟨hx, ht, hq⟩

namespace Cyc

variable (c : Cyc G)

section cell

variable {x t : ℕ} (hx : x < G.T) (ht : t < G.T)
include hx ht

/-- Rightward traversal leaves through the logical right exit. -/
lemma exitR (h : c.τ (.cell x t 3) = G.eR x t) :
    c.τ (.cell x t (if G.mir x t then 1 else 5)) = G.Rp x t := by
  have m := c.modes hx ht
  unfold eR at h
  by_cases hm : G.mir x t
  · simp only [hm, if_true] at h ⊢; have := m.2.1 h; simpa [port1, hm] using this
  · simp only [hm, if_false] at h ⊢; have := m.1 h; simpa [port5, hm] using this

lemma exitL (h : c.τ (.cell x t 3) = G.eL x t) :
    c.τ (.cell x t (if G.mir x t then 5 else 1)) = G.Lp x t := by
  have m := c.modes hx ht
  unfold eL at h
  by_cases hm : G.mir x t
  · simp only [hm, if_true] at h ⊢; have := m.1 h; simpa [port5, hm] using this
  · simp only [hm, if_false] at h ⊢; have := m.2.1 h; simpa [port1, hm] using this

lemma enterL {w : V} (hw : G.valid w) (hne : w ≠ .cell x t 3) (h : c.τ w = G.eL x t) :
    c.τ (.cell x t 3) = G.eR x t := by
  have h3 := c.o3 hx ht
  have hn : c.τ (.cell x t 3) ≠ G.eL x t := fun h' =>
    hne (c.inj _ _ hw (vc hx ht 3 (by norm_num)) (h.trans h'.symm))
  unfold eL at hn; unfold eR
  split_ifs at hn ⊢ <;> rcases h3 with h3 | h3 <;> simp_all

lemma enterR {w : V} (hw : G.valid w) (hne : w ≠ .cell x t 3) (h : c.τ w = G.eR x t) :
    c.τ (.cell x t 3) = G.eL x t := by
  have h3 := c.o3 hx ht
  have hn : c.τ (.cell x t 3) ≠ G.eR x t := fun h' =>
    hne (c.inj _ _ hw (vc hx ht 3 (by norm_num)) (h.trans h'.symm))
  unfold eR at hn; unfold eL
  split_ifs at hn ⊢ <;> rcases h3 with h3 | h3 <;> simp_all

end cell

/-- A row entered from the left is traversed rightward throughout. -/
lemma rowR {x : ℕ} (hx : x < G.T) (h : c.τ (.top x) = G.eL x 0) :
    ∀ t < G.T, c.τ (.cell x t 3) = G.eR x t := by
  intro t ht
  induction t with
  | zero => exact c.enterL hx ht (show G.valid (.top x) from hx) (by simp) h
  | succ t ih =>
    have h1 := c.exitR hx (by omega) (ih (by omega))
    unfold Rp at h1; rw [if_pos ht] at h1
    exact c.enterL hx ht (valid_cell hx (by omega) (by split_ifs <;> omega)) (by simp) h1

/-- A row entered from the right is traversed leftward throughout. -/
lemma rowL {x : ℕ} (hx : x < G.T) (h : c.τ (.top x) = G.eR x (G.T - 1)) :
    ∀ t < G.T, c.τ (.cell x t 3) = G.eL x t := by
  suffices ∀ d < G.T, c.τ (.cell x (G.T - 1 - d) 3) = G.eL x (G.T - 1 - d) by
    intro t ht; have := this (G.T - 1 - t) (by omega); rwa [show G.T - 1 - (G.T - 1 - t) = t by omega] at this
  intro d hd
  induction d with
  | zero => exact c.enterR hx (by omega) (show G.valid (.top x) from hx) (by simp) h
  | succ d ih =>
    have h1 := c.exitL hx (by omega) (ih (by omega))
    have e : G.T - 1 - d - 1 = G.T - 1 - (d + 1) := by omega
    unfold Lp at h1
    rw [if_neg (show ¬ (G.T - 1 - d = 0) by omega), e] at h1
    exact c.enterR hx (by omega)
      (valid_cell (q := if G.mir x (G.T - 1 - d) then 5 else 1) hx (by omega)
        (by split_ifs <;> omega))
      (fun h => by simp only [V.cell.injEq] at h; omega) h1

end Cyc

/-! ### Clauses -/

/-- The clause nodes of tokens `a … b`. -/
def InSpan (a b : ℕ) (w : V) : Prop := ∃ t, a ≤ t ∧ t ≤ b ∧ (w = .rr t ∨ w = .qq t)

lemma Lp_ne_rq (x t s : ℕ) : G.Lp x t ≠ .rr s ∧ G.Lp x t ≠ .qq s := by
  unfold Lp eR; split_ifs <;> simp

lemma Rp_ne_rq (x t s : ℕ) : G.Rp x t ≠ .rr s ∧ G.Rp x t ≠ .qq s := by
  unfold Rp eL; split_ifs <;> simp

/-- **Clauses are entered only through detours.** -/
lemma clause_entry {a b : ℕ} (ha : G.clStart a) (hb : G.cs b) {u v : V} (hv : v ∈ G.outsV u)
    (hSv : InSpan a b v) (hSu : ¬ InSpan a b u) :
    ∃ x t, u = .cell x t 4 ∧ G.lit x t ∧ v = .rr t := by
  obtain ⟨s, has, hsb, hs⟩ := hSv
  have hlc : ∀ {r}, v ∉ G.litCells r := fun h => by
    obtain ⟨_, _, _, h⟩ := G.mem_litCells.mp h; rcases hs with rfl | rfl <;> cases h
  rcases u with ⟨x, t, _ | _ | _ | _ | _ | _ | q⟩ | x | x | t | t
  all_goals simp only [outsV, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  · exfalso; rcases hv with rfl | rfl <;> rcases hs with h | h <;> cases h
  · exfalso; rcases hv with rfl | rfl
    · rcases hs with h | h <;> cases h
    · have := G.Lp_ne_rq x t s; have := G.Rp_ne_rq x t s
      split_ifs at hs <;> simp_all
  · exfalso; rcases hv with rfl | rfl <;> rcases hs with h | h <;> cases h
  · exfalso; rcases hv with rfl | rfl <;> rcases hs with h | h <;> cases h
  · rcases hv with rfl | hv
    · exfalso; rcases hs with h | h <;> cases h
    · split_ifs at hv with hl
      · simp only [List.mem_singleton] at hv; subst hv
        refine ⟨x, t, rfl, hl, ?_⟩
        rcases hs with h | h <;> cases h; rfl
      · simp at hv
  · exfalso; rcases hv with rfl | rfl
    · rcases hs with h | h <;> cases h
    · have := G.Lp_ne_rq x t s; have := G.Rp_ne_rq x t s
      split_ifs at hs <;> simp_all
  · exfalso; rcases hv with rfl | rfl <;> rcases hs with h | h <;> simp [eL, eR] at h
  · exfalso; subst hv; rcases hs with h | h <;> cases h
  · exfalso
    split_ifs at hv with hc
    · simp only [List.mem_singleton] at hv; subst hv
      rcases hs with h | h <;> cases h
      exact hSu ⟨s, has, hsb, Or.inl rfl⟩
    · rcases List.mem_cons.mp hv with rfl | hv
      · rcases hs with h | h <;> cases h
        have : ¬ (a ≤ t) := fun h => hSu ⟨t, h, by omega, Or.inl rfl⟩
        rcases ha with ha | ha
        · omega
        · exact hc (by rwa [show a - 1 = t by omega] at ha)
      · exact hlc hv
  · exfalso
    split_ifs at hv with hc
    · rcases List.mem_cons.mp hv with rfl | hv
      · rcases hs with h | h <;> cases h
        exact hSu ⟨s, has, hsb, Or.inr rfl⟩
      · exact hlc hv
    · simp only [List.mem_singleton] at hv; subst hv
      rcases hs with h | h <;> cases h
      have ht0 : t ≠ 0 := fun h => hc (Or.inl h)
      have : ¬ (t ≤ b) := fun h => hSu ⟨t, by omega, h, Or.inr rfl⟩
      exact hc (Or.inr (by rwa [show t - 1 = b by omega]))

/-- **Token-level NO direction.** A Hamiltonian cycle gives an assignment under which every
clause (tokens up to a clause end `b`) contains a true literal. -/
theorem sat_of_dhc (hw : G.WF) (h : DHC G.dig) :
    ∃ α : ℕ → Bool, ∀ b, G.cs b → ∃ s x, s ≤ b ∧ (∀ t, s ≤ t → t < b → ¬ G.cs t) ∧
      G.lit x s ∧ (G.pos s ↔ α x = true) := by
  obtain ⟨c⟩ := cyc_of_dhc hw h
  refine ⟨fun x => decide (c.τ (.top x) = G.eL x 0), fun b hb => ?_⟩
  have hbT : b < G.T := lt_of_tok hw hb
  set a := Nat.findGreatest G.clStart b with ha_def
  have ha : G.clStart a := Nat.findGreatest_spec (P := G.clStart) (Nat.zero_le b) (Or.inl rfl)
  have hab : a ≤ b := Nat.findGreatest_le b
  have hno : ∀ t, a ≤ t → t < b → ¬ G.cs t := fun t h1 h2 hc =>
    Nat.findGreatest_is_greatest (P := G.clStart) (by omega : a < t + 1) (by omega)
      (Or.inr (by simpa using hc))
  obtain ⟨u, hu, hSu, hSτ⟩ := c.entry (InSpan a b) (v := .top 0) (w := .rr a)
    (show (0 : ℕ) < G.T from hw.2.1) (by rintro ⟨_, _, _, h | h⟩ <;> cases h)
    (show a < G.T by omega) ⟨a, le_rfl, hab, Or.inl rfl⟩
  obtain ⟨x, t, rfl, hl, hτ⟩ := clause_entry ha hb (c.arc u hu) hSτ hSu
  obtain ⟨t', h1, h2, ht'⟩ := hSτ
  rw [hτ] at ht'
  have htt : t' = t := by rcases ht' with h | h <;> cases h; rfl
  subst htt
  have hx := hu.1; have ht := hu.2.1
  have hdet : c.τ (.cell x t' 3) = .cell x t' 4 :=
    (c.modes hx ht).2.2 (by rw [hτ]; simp)
  refine ⟨t', x, h2, fun t h3 h4 => hno t (by omega) h4, hl, ?_⟩
  have htop := c.arc _ (show G.valid (.top x) from hx)
  simp only [outsV, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at htop
  by_cases hp : G.pos t'
  · have hm : ¬ G.mir x t' := fun h => h.2 hp
    simp only [hp, true_iff, decide_eq_true_eq]
    by_contra hL
    have hR : c.τ (.top x) = G.eR x (G.T - 1) := htop.resolve_left hL
    have := c.rowL hx hR t' ht
    rw [hdet] at this; simp [eL, hm] at this
  · have hm : G.mir x t' := ⟨hl, hp⟩
    simp only [hp, false_iff, decide_eq_true_eq]
    intro hL
    have := c.rowR hx hL t' ht
    rw [hdet] at this; simp [eR, hm] at this

end TS

end Pts
