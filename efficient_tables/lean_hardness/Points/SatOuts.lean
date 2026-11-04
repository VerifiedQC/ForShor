import Points.SatLab

/-!
# Out-neighbours in closed form

`outs u = o1 u :: (if two u then [o2 u] else [])` for every vertex `u < n` (`outs_eq`), where
`o1`, `o2` are arithmetic in `u` and `T` with case distinctions on token predicates, and the
variable of a literal is found by a bounded search (`vf`). This is the form computed in
polynomial time in `SatFP.lean`.
-/

namespace Pts

open Complexity SAT

namespace TS

variable (G : TS)

/-- The variable of the literal at `s`, by bounded search. -/
def vf (s : ℕ) : ℕ := (List.range G.T).findIdx fun x => decide (G.lit x s)

def exLit (s : ℕ) : Prop := ∃ x < G.T, G.lit x s

instance : DecidablePred G.exLit := fun _ => by unfold exLit; infer_instance

variable {G}

lemma vf_spec {s : ℕ} (h : G.exLit s) : G.vf s < G.T ∧ G.lit (G.vf s) s := by
  obtain ⟨x, hx, hl⟩ := h
  have hex : ∃ a ∈ List.range G.T, decide (G.lit a s) = true :=
    ⟨x, List.mem_range.mpr hx, decide_eq_true hl⟩
  have hlt : G.vf s < (List.range G.T).length := List.findIdx_lt_length_of_exists hex
  have hget := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at hget
  refine ⟨by simpa using hlt, ?_⟩
  have e : (List.range G.T)[List.findIdx (fun x => decide (G.lit x s)) (List.range G.T)]'hlt = G.vf s :=
    List.getElem_range _
  rwa [e] at hget

lemma litCells_eq (s : ℕ) :
    G.litCells s = if G.exLit s then [.cell (G.vf s) s 1] else [] := by
  split_ifs with h
  · obtain ⟨h1, h2⟩ := vf_spec h
    have hl := G.litCells_length_le s
    have hm : V.cell (G.vf s) s 1 ∈ G.litCells s := G.mem_litCells.mpr ⟨_, h1, h2, rfl⟩
    match hc : G.litCells s with
    | [] => rw [hc] at hm; simp at hm
    | [a] => rw [hc] at hm; simp at hm; rw [hm]
    | a :: b :: l => rw [hc] at hl; simp at hl
  · refine List.eq_nil_iff_forall_not_mem.mpr fun v hv => h ?_
    obtain ⟨x, hx, hl, -⟩ := G.mem_litCells.mp hv
    exact ⟨x, hx, hl⟩

variable (G)

/-! ### Closed forms -/

def cE (x t q : ℕ) : ℕ := 6 * (x * G.T + t) + q
def eLn (x t : ℕ) : ℕ := G.cE x t (if G.mir x t then 4 else 0)
def eRn (x t : ℕ) : ℕ := G.cE x t (if G.mir x t then 0 else 4)
def topN (x : ℕ) : ℕ := G.N6 + x
def botN (x : ℕ) : ℕ := G.N6 + G.T + x
def rN (t : ℕ) : ℕ := G.N6 + 2 * G.T + t
def qN (t : ℕ) : ℕ := G.N6 + 3 * G.T + t
def LpN (x t : ℕ) : ℕ := if t = 0 then G.botN x else G.eRn x (t - 1)
def RpN (x t : ℕ) : ℕ := if t + 1 < G.T then G.eLn x (t + 1) else G.botN x
def p1N (x t : ℕ) : ℕ := if G.mir x t then G.RpN x t else G.LpN x t
def p5N (x t : ℕ) : ℕ := if G.mir x t then G.LpN x t else G.RpN x t

/-- Coordinates of a cell vertex. -/
def cx (u : ℕ) : ℕ := u / 6 / G.T
def ct (u : ℕ) : ℕ := u / 6 % G.T

/-- First out-neighbour. -/
def o1 (u : ℕ) : ℕ :=
  if u < G.N6 then
    (if u % 6 = 0 then G.cE (G.cx u) (G.ct u) 1
    else if u % 6 = 1 then G.cE (G.cx u) (G.ct u) 2
    else if u % 6 = 2 then G.cE (G.cx u) (G.ct u) 3
    else if u % 6 = 3 then G.cE (G.cx u) (G.ct u) 0
    else if u % 6 = 4 then G.cE (G.cx u) (G.ct u) 5
    else G.cE (G.cx u) (G.ct u) 2)
  else if u < G.N6 + G.T then G.eLn (u - G.N6) 0
  else if u < G.N6 + 2 * G.T then G.topN ((u - G.N6 - G.T + 1) % G.T)
  else if u < G.N6 + 3 * G.T then
    (if G.cs (u - G.N6 - 2 * G.T) then G.qN (u - G.N6 - 2 * G.T) else G.rN (u - G.N6 - 2 * G.T + 1))
  else (if G.clStart (u - G.N6 - 3 * G.T) then G.rN (u - G.N6 - 3 * G.T)
    else G.qN (u - G.N6 - 3 * G.T - 1))

/-- Second out-neighbour (when there is one). -/
def o2 (u : ℕ) : ℕ :=
  if u < G.N6 then
    (if u % 6 = 0 then G.cE (G.cx u) (G.ct u) 3
    else if u % 6 = 1 then G.p1N (G.cx u) (G.ct u)
    else if u % 6 = 2 then G.cE (G.cx u) (G.ct u) 5
    else if u % 6 = 3 then G.cE (G.cx u) (G.ct u) 4
    else if u % 6 = 4 then G.rN (G.ct u)
    else G.p5N (G.cx u) (G.ct u))
  else if u < G.N6 + G.T then G.eRn (u - G.N6) (G.T - 1)
  else if u < G.N6 + 2 * G.T then 0
  else if u < G.N6 + 3 * G.T then
    G.cE (G.vf (u - G.N6 - 2 * G.T + 1)) (u - G.N6 - 2 * G.T + 1) 1
  else G.cE (G.vf (u - G.N6 - 3 * G.T)) (u - G.N6 - 3 * G.T) 1

/-- There is a second out-neighbour. -/
def two (u : ℕ) : Prop :=
  if u < G.N6 then (u % 6 = 4 → G.lit (G.cx u) (G.ct u))
  else if u < G.N6 + G.T then True
  else if u < G.N6 + 2 * G.T then False
  else if u < G.N6 + 3 * G.T then
    ¬ G.cs (u - G.N6 - 2 * G.T) ∧ G.exLit (u - G.N6 - 2 * G.T + 1)
  else G.clStart (u - G.N6 - 3 * G.T) ∧ G.exLit (u - G.N6 - 3 * G.T)

instance : DecidablePred G.two := fun _ => by unfold two; infer_instance

variable {G}

@[simp] lemma enc_cell (x t q : ℕ) : G.enc (.cell x t q) = G.cE x t q := rfl
@[simp] lemma enc_top (x : ℕ) : G.enc (.top x) = G.topN x := rfl
@[simp] lemma enc_bot (x : ℕ) : G.enc (.bot x) = G.botN x := rfl
@[simp] lemma enc_rr (t : ℕ) : G.enc (.rr t) = G.rN t := rfl
@[simp] lemma enc_qq (t : ℕ) : G.enc (.qq t) = G.qN t := rfl

lemma enc_eL (x t : ℕ) : G.enc (G.eL x t) = G.eLn x t := by
  unfold eL eLn cE; rfl
lemma enc_eR (x t : ℕ) : G.enc (G.eR x t) = G.eRn x t := by
  unfold eR eRn cE; rfl
lemma enc_Lp (x t : ℕ) : G.enc (G.Lp x t) = G.LpN x t := by
  unfold Lp LpN; split_ifs
  · rfl
  · exact enc_eR _ _
lemma enc_Rp (x t : ℕ) : G.enc (G.Rp x t) = G.RpN x t := by
  unfold Rp RpN; split_ifs
  · exact enc_eL _ _
  · rfl

/-- **Out-neighbours in closed form.** -/
theorem outs_eq {u : ℕ} (hu : u < G.n) :
    G.outs u = G.o1 u :: (if G.two u then [G.o2 u] else []) := by
  unfold outs
  have hv := G.enc_dec hu
  by_cases h1 : u < G.N6
  · have hT : 0 < G.T := by
      rcases Nat.eq_zero_or_pos G.T with h | h
      · simp [N6, h] at h1
      · exact h
    have hd : G.dec u = .cell (G.cx u) (G.ct u) (u % 6) := by
      unfold dec cx ct; rw [if_pos h1]
    rw [hd]
    have hq : u % 6 < 6 := Nat.mod_lt _ (by norm_num)
    simp only [o1, o2, two, if_pos h1]
    generalize u % 6 = q at hq ⊢
    interval_cases q <;> simp only [outsV, List.map_cons, List.map_nil, enc_cell, if_true,
      Nat.reduceEqDiff, OfNat.ofNat_ne_zero, one_ne_zero, true_implies, imp_false,
      reduceCtorEq, if_false, not_true_eq_false, false_implies] <;>
      (try simp only [apply_ite G.enc, enc_Lp, enc_Rp, p1N, p5N])
    all_goals (try split_ifs) <;> simp_all
  · by_cases h2 : u < G.N6 + G.T
    · have hd : G.dec u = .top (u - G.N6) := by unfold dec; rw [if_neg h1, if_pos h2]
      rw [hd]; simp only [outsV, o1, o2, two, h1, h2, if_false, if_true, List.map_cons,
        List.map_nil, enc_eL, enc_eR]
    · by_cases h3 : u < G.N6 + 2 * G.T
      · have hd : G.dec u = .bot (u - G.N6 - G.T) := by
          unfold dec; rw [if_neg h1, if_neg h2, if_pos h3]
        rw [hd]; simp only [outsV, o1, two, h1, h2, h3, if_false, if_true, List.map_cons,
          List.map_nil, enc_top]
        try (congr 3; omega)
      · by_cases h4 : u < G.N6 + 3 * G.T
        · have hd : G.dec u = .rr (u - G.N6 - 2 * G.T) := by
            unfold dec; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          rw [hd]
          simp only [outsV, o1, o2, two, h1, h2, h3, h4, if_false, if_true, litCells_eq]
          split_ifs <;> simp_all
        · have hd : G.dec u = .qq (u - G.N6 - 3 * G.T) := by
            unfold dec; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          rw [hd]
          simp only [outsV, o1, o2, two, h1, h2, h3, h4, if_false, litCells_eq]
          split_ifs <;> simp_all

end TS

end Pts
