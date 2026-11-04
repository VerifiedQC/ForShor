import Points.DhcTable
import Complexitylib.SAT.Verifier

/-!
# The digraph of a CNF token stream (SAT → DHC₂, the construction)

The input is a stream of complexitylib's SAT encoding tokens (`bit b` = `00`/`11`, `litSep` = `01`,
`clauseSep` = `10`), of length `T`. Everything is indexed by token positions, so that the graph is
computable by bounded loops (see `SatFP.lean`).

* **Rows.** For every `x < T` there is a row of `T` six-node cells `cell x t q` (`t < T`, `q < 6`)
  between `top x` and `bot x`; `bot x → top (x + 1)` (cyclically). Cell `(x, t)` is *real* when
  the token `t` starts a literal on the variable `x` (`lit x t`); it is *mirrored* when that
  literal is negative.
* **Cell.** `0→{1,3}, 1→{2,·}, 2→{3,5}, 3→{0,4}, 4→{5,r t}, 5→{2,·}`; physically node `0` is
  entered from the left and node `4` from the right, node `1` leaves to the left and node `5` to
  the right; a mirrored cell swaps left and right. Its only Hamiltonian traversals are
  rightward, rightward with a detour `4 → clause → 1`, and leftward (`cell_mode`).
* **Clauses.** The tokens `a … b` of a clause carry the cycle `r a → ⋯ → r b → q b → ⋯ → q a → r a`;
  a literal at token `s` enters it at `r s` and the predecessor of `r s` exits to its node `1`.

Vertices are numbered `cell x t q ↦ 6 (x T + t) + q`, then `top`, `bot`, `r`, `q` (`T` each).
-/

namespace Pts

open Complexity SAT

/-- A token stream: its length and its tokens. -/
structure TS where
  T : ℕ
  tok : ℕ → Option EncToken

namespace TS

variable (G : TS)

def isSep (t : ℕ) : Prop := G.tok t = some .litSep ∨ G.tok t = some .clauseSep
def bnd (t : ℕ) : Prop := t = 0 ∨ G.isSep (t - 1)
def isBit (t : ℕ) : Prop := G.tok t = some (.bit false) ∨ G.tok t = some (.bit true)
/-- Token `s` is the sign of a literal. -/
def sgn (s : ℕ) : Prop := G.isBit s ∧ G.bnd s
/-- Token `s` starts a literal on the variable `x`. -/
def lit (x s : ℕ) : Prop :=
  G.sgn s ∧ (∀ i < x, G.tok (s + 1 + i) = some (.bit true)) ∧ G.tok (s + 1 + x) = some .litSep
def pos (s : ℕ) : Prop := G.tok s = some (.bit true)
def mir (x s : ℕ) : Prop := G.lit x s ∧ ¬ G.pos s
def cs (t : ℕ) : Prop := G.tok t = some .clauseSep
def clStart (t : ℕ) : Prop := t = 0 ∨ G.cs (t - 1)

instance : DecidablePred G.isSep := fun _ => by unfold isSep; infer_instance
instance : DecidablePred G.bnd := fun _ => by unfold bnd; infer_instance
instance : DecidablePred G.isBit := fun _ => by unfold isBit; infer_instance
instance : DecidablePred G.sgn := fun _ => by unfold sgn; infer_instance
instance (x : ℕ) : DecidablePred (G.lit x) := fun _ => by unfold lit; infer_instance
instance : DecidablePred G.pos := fun _ => by unfold pos; infer_instance
instance (x : ℕ) : DecidablePred (G.mir x) := fun _ => by unfold mir; infer_instance
instance : DecidablePred G.cs := fun _ => by unfold cs; infer_instance
instance : DecidablePred G.clStart := fun _ => by unfold clStart; infer_instance

/-- A literal start determines its variable. -/
lemma lit_unique {G : TS} {x y s : ℕ} (hx : G.lit x s) (hy : G.lit y s) : x = y := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hy.2.1 x h; rw [hx.2.2] at this; cases this
  · have := hx.2.1 y h; rw [hy.2.2] at this; cases this

/-- The vertices. -/
inductive V
  | cell (x t q : ℕ)
  | top (x : ℕ)
  | bot (x : ℕ)
  | rr (t : ℕ)
  | qq (t : ℕ)
  deriving DecidableEq

def N6 : ℕ := 6 * (G.T * G.T)
/-- The number of vertices. -/
def n : ℕ := G.N6 + 4 * G.T

def enc : V → ℕ
  | .cell x t q => 6 * (x * G.T + t) + q
  | .top x => G.N6 + x
  | .bot x => G.N6 + G.T + x
  | .rr t => G.N6 + 2 * G.T + t
  | .qq t => G.N6 + 3 * G.T + t

def dec (u : ℕ) : V :=
  if u < G.N6 then .cell (u / 6 / G.T) (u / 6 % G.T) (u % 6)
  else if u < G.N6 + G.T then .top (u - G.N6)
  else if u < G.N6 + 2 * G.T then .bot (u - G.N6 - G.T)
  else if u < G.N6 + 3 * G.T then .rr (u - G.N6 - 2 * G.T)
  else .qq (u - G.N6 - 3 * G.T)

def valid : V → Prop
  | .cell x t q => x < G.T ∧ t < G.T ∧ q < 6
  | .top x => x < G.T
  | .bot x => x < G.T
  | .rr t => t < G.T
  | .qq t => t < G.T

lemma enc_lt {v : V} (hv : G.valid v) : G.enc v < G.n := by
  cases v with
  | cell x t q =>
    obtain ⟨hx, ht, hq⟩ := hv
    have : x * G.T + t + 1 ≤ G.T * G.T := by nlinarith
    simp only [enc, n, N6]; omega
  | _ => simp only [valid] at hv; simp only [enc, n]; omega

lemma dec_valid {u : ℕ} (hu : u < G.n) : G.valid (G.dec u) := by
  unfold dec
  split_ifs with h1 h2 h3 h4
  · have hT : 0 < G.T := by
      rcases Nat.eq_zero_or_pos G.T with h | h
      · simp [N6, h] at h1
      · exact h
    refine ⟨?_, Nat.mod_lt _ hT, Nat.mod_lt _ (by norm_num)⟩
    rw [Nat.div_lt_iff_lt_mul hT]
    unfold N6 at h1; omega
  all_goals simp only [valid]; unfold n at hu; omega

lemma enc_dec {u : ℕ} (hu : u < G.n) : G.enc (G.dec u) = u := by
  unfold dec
  split_ifs with h1 h2 h3 h4
  · simp only [enc]
    have := Nat.div_add_mod (u / 6) G.T
    have := Nat.div_add_mod u 6
    rw [mul_comm (u / 6 / G.T)]; omega
  all_goals simp only [enc]; omega

lemma dec_enc {v : V} (hv : G.valid v) : G.dec (G.enc v) = v := by
  cases v with
  | cell x t q =>
    obtain ⟨hx, ht, hq⟩ := hv
    have hlt : 6 * (x * G.T + t) + q < G.N6 := by
      have : x * G.T + t + 1 ≤ G.T * G.T := by nlinarith
      unfold N6; omega
    simp only [dec, enc, hlt, ite_true]
    have h6 : (6 * (x * G.T + t) + q) / 6 = x * G.T + t := by omega
    have h1 : (x * G.T + t) / G.T = x := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]
    have h2 : (x * G.T + t) % G.T = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    rw [h6, h1, h2, show (6 * (x * G.T + t) + q) % 6 = q by omega]
  | top x =>
    simp only [valid] at hv
    show G.dec (G.N6 + x) = _; unfold dec; rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
  | bot x =>
    simp only [valid] at hv
    show G.dec (G.N6 + G.T + x) = _; unfold dec
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega
  | rr t =>
    simp only [valid] at hv
    show G.dec (G.N6 + 2 * G.T + t) = _; unfold dec
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega
  | qq t =>
    simp only [valid] at hv
    show G.dec (G.N6 + 3 * G.T + t) = _; unfold dec
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; congr 1; omega

lemma enc_inj {v w : V} (hv : G.valid v) (hw : G.valid w) (h : G.enc v = G.enc w) : v = w := by
  rw [← G.dec_enc hv, ← G.dec_enc hw, h]

/-! ### Ports and arcs -/

/-- Logical left and right entries of a cell. -/
def eL (x t : ℕ) : V := .cell x t (if G.mir x t then 4 else 0)
def eR (x t : ℕ) : V := .cell x t (if G.mir x t then 0 else 4)
/-- Where leaving a cell to the left / right leads. -/
def Lp (x t : ℕ) : V := if t = 0 then .bot x else G.eR x (t - 1)
def Rp (x t : ℕ) : V := if t + 1 < G.T then G.eL x (t + 1) else .bot x

/-- The cells entered from the clause node before token `s` (at most one: `lit_unique`). -/
def litCells (s : ℕ) : List V := ((List.range G.T).filter fun x => G.lit x s).map fun x => .cell x s 1

/-- Out-neighbours. -/
def outsV : V → List V
  | .cell x t 0 => [.cell x t 1, .cell x t 3]
  | .cell x t 1 => [.cell x t 2, if G.mir x t then G.Rp x t else G.Lp x t]
  | .cell x t 2 => [.cell x t 3, .cell x t 5]
  | .cell x t 3 => [.cell x t 0, .cell x t 4]
  | .cell x t 4 => .cell x t 5 :: if G.lit x t then [.rr t] else []
  | .cell x t 5 => [.cell x t 2, if G.mir x t then G.Lp x t else G.Rp x t]
  | .cell _ _ _ => []
  | .top x => [G.eL x 0, G.eR x (G.T - 1)]
  | .bot x => [.top ((x + 1) % G.T)]
  | .rr t => if G.cs t then [.qq t] else .rr (t + 1) :: G.litCells (t + 1)
  | .qq t => if G.clStart t then .rr t :: G.litCells t else [.qq (t - 1)]

def outs (u : ℕ) : List ℕ := (G.outsV (G.dec u)).map G.enc

/-- **The digraph of a token stream.** -/
def dig : Dig := ⟨G.n, (List.range G.n).flatMap fun u => (G.outs u).map fun w => (u, w)⟩

lemma mem_arcs {u w : ℕ} : (u, w) ∈ G.dig.arcs ↔ u < G.n ∧ w ∈ G.outs u := by
  simp only [dig, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u', hu', w', hw', rfl, rfl⟩; exact ⟨hu', hw'⟩
  · rintro ⟨hu, hw⟩; exact ⟨u, hu, w, hw, rfl, rfl⟩

lemma litCells_length_le (s : ℕ) : (G.litCells s).length ≤ 1 := by
  unfold litCells
  rw [List.length_map]
  have hnd : ((List.range G.T).filter fun x => G.lit x s).Nodup := (List.nodup_range).filter _
  match h : (List.range G.T).filter fun x => G.lit x s with
  | [] => simp
  | [_] => simp
  | a :: b :: l =>
    exfalso
    have ha : a ∈ (List.range G.T).filter fun x => G.lit x s := by rw [h]; simp
    have hb : b ∈ (List.range G.T).filter fun x => G.lit x s := by rw [h]; simp
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    rw [h] at hnd
    exact (List.nodup_cons.mp hnd).1 (by rw [lit_unique ha.2 hb.2]; simp)

lemma mem_litCells {s : ℕ} {v : V} : v ∈ G.litCells s ↔ ∃ x < G.T, G.lit x s ∧ v = .cell x s 1 := by
  simp only [litCells, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hl⟩, rfl⟩; exact ⟨x, hx, hl, rfl⟩
  · rintro ⟨x, hx, hl, rfl⟩; exact ⟨x, ⟨hx, hl⟩, rfl⟩

lemma lit_lt {x s : ℕ} (G : TS) (hb : ∀ t, t < G.T ↔ (G.tok t).isSome) (h : G.lit x s) :
    s + 1 + x < G.T := by
  rw [hb, h.2.2]; rfl

lemma outsV_length_le (v : V) : (G.outsV v).length ≤ 2 := by
  have h1 := G.litCells_length_le
  rcases v with ⟨x, t, _ | _ | _ | _ | _ | _ | q⟩ | x | x | t | t <;> simp only [outsV] <;>
    (try split_ifs) <;> (try simp) <;> (try have := h1 t) <;> (try have := h1 (t + 1)) <;> omega

/-! ### Well-formedness of the digraph -/

/-- The token stream is well formed for the construction: tokens exactly below `T`, `T > 0`,
the last token closes a clause. -/
def WF : Prop := (∀ t, t < G.T ↔ (G.tok t).isSome) ∧ 0 < G.T ∧ G.cs (G.T - 1)

variable {G}

lemma lt_of_tok {t : ℕ} {e : EncToken} (hw : G.WF) (h : G.tok t = some e) : t < G.T := by
  rw [hw.1, h]; rfl

lemma lit_lt' (hw : G.WF) {x s : ℕ} (h : G.lit x s) : s + 1 + x < G.T := lt_of_tok hw h.2.2

lemma eL_valid {x t : ℕ} (hx : x < G.T) (ht : t < G.T) : G.valid (G.eL x t) := by
  unfold eL; refine ⟨hx, ht, ?_⟩; split_ifs <;> omega

lemma eR_valid {x t : ℕ} (hx : x < G.T) (ht : t < G.T) : G.valid (G.eR x t) := by
  unfold eR; refine ⟨hx, ht, ?_⟩; split_ifs <;> omega

lemma Lp_valid {x t : ℕ} (hx : x < G.T) (ht : t < G.T) :
    G.valid (G.Lp x t) ∧ ∀ q, G.Lp x t ≠ .cell x t q := by
  unfold Lp
  split_ifs with h0
  · exact ⟨hx, fun q h => by cases h⟩
  · refine ⟨eR_valid hx (by omega), fun q h => ?_⟩
    unfold eR at h; simp only [V.cell.injEq] at h; omega

lemma Rp_valid {x t : ℕ} (hx : x < G.T) :
    G.valid (G.Rp x t) ∧ ∀ q, G.Rp x t ≠ .cell x t q := by
  unfold Rp
  split_ifs with h0
  · refine ⟨eL_valid hx h0, fun q h => ?_⟩
    unfold eL at h; simp only [V.cell.injEq] at h; omega
  · exact ⟨hx, fun q h => by cases h⟩

lemma Lp_valid' {x t q : ℕ} (h : V.cell x t q = G.Lp x t) : False := by
  unfold Lp at h; split_ifs at h with h0
  first | cases h | (unfold eR at h; simp only [V.cell.injEq] at h; omega)

lemma Rp_valid' {x t q : ℕ} (h : V.cell x t q = G.Rp x t) : False := by
  unfold Rp at h; split_ifs at h with h0
  all_goals first | cases h | (unfold eL at h; simp only [V.cell.injEq] at h; omega)

lemma outsV_valid (hw : G.WF) {v : V} (hv : G.valid v) : ∀ w ∈ G.outsV v, G.valid w ∧ w ≠ v := by
  have hT := hw.2.1
  rcases v with ⟨x, t, q⟩ | x | x | t | t
  · obtain ⟨hx, ht, hq⟩ := hv
    have hL := Lp_valid (G := G) hx ht
    have hR := Rp_valid (G := G) (t := t) hx
    interval_cases q <;> simp only [outsV] <;> intro w hw' <;>
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw'
    all_goals first
      | (rcases hw' with rfl | rfl <;> (try split_ifs) <;>
          first
            | exact ⟨⟨hx, ht, by omega⟩, by simp⟩
            | exact ⟨hL.1, hL.2 _⟩
            | exact ⟨hR.1, hR.2 _⟩)
      | (rcases hw' with rfl | hw' <;> [exact ⟨⟨hx, ht, by omega⟩, by simp⟩; skip]
         split_ifs at hw' with hl
         · simp only [List.mem_singleton] at hw'; subst hw'; exact ⟨ht, by simp⟩
         · simp at hw')
  · simp only [valid] at hv
    simp only [outsV, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro w (rfl | rfl)
    · exact ⟨eL_valid hv hT, by simp [eL]⟩
    · exact ⟨eR_valid hv (by omega), by simp [eR]⟩
  · simp only [valid] at hv
    simp only [outsV, List.mem_singleton]
    rintro w rfl
    exact ⟨Nat.mod_lt _ hT, by simp⟩
  · simp only [valid] at hv
    simp only [outsV]
    split_ifs with hc
    · simp only [List.mem_singleton]; rintro w rfl; exact ⟨hv, by simp⟩
    · intro w hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · refine ⟨?_, by simp⟩
        show t + 1 < G.T
        by_contra hge
        exact hc (by rw [show t = G.T - 1 by omega]; exact hw.2.2)
      · obtain ⟨x, hx, hl, rfl⟩ := G.mem_litCells.mp hw'
        exact ⟨⟨hx, by have := lit_lt' hw hl; omega, by norm_num⟩, by simp⟩
  · simp only [valid] at hv
    simp only [outsV]
    split_ifs with hc
    · intro w hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact ⟨hv, by simp⟩
      · obtain ⟨x, hx, hl, rfl⟩ := G.mem_litCells.mp hw'
        exact ⟨⟨hx, hv, by norm_num⟩, by simp⟩
    · simp only [List.mem_singleton]; rintro w rfl
      refine ⟨by show t - 1 < G.T; omega, ?_⟩
      have : t ≠ 0 := fun h => hc (Or.inl h)
      simp only [ne_eq, V.qq.injEq]; omega

lemma litCells_nodup (s : ℕ) : (G.litCells s).Nodup :=
  ((List.nodup_range).filter _).map fun a b h => by cases h; rfl

lemma outsV_nodup (v : V) : (G.outsV v).Nodup := by
  have hc : ∀ s, ∀ w ∈ G.litCells s, ∀ t, w ≠ .rr t := fun s w hw t h => by
    obtain ⟨x, _, _, rfl⟩ := G.mem_litCells.mp hw; cases h
  rcases v with ⟨x, t, _ | _ | _ | _ | _ | _ | q⟩ | x | x | t | t <;> simp only [outsV]
  · simp
  · refine List.nodup_cons.mpr ⟨?_, by simp⟩
    simp only [List.mem_singleton]
    intro h
    split_ifs at h <;> first
      | exact (Rp_valid' h)
      | exact (Lp_valid' h)
  · simp
  · simp
  · split_ifs <;> simp
  · refine List.nodup_cons.mpr ⟨?_, by simp⟩
    simp only [List.mem_singleton]
    intro h
    split_ifs at h <;> first
      | exact (Rp_valid' h)
      | exact (Lp_valid' h)
  · simp
  · refine List.nodup_cons.mpr ⟨?_, by simp⟩
    simp only [List.mem_singleton, eL, eR, V.cell.injEq]
    rintro ⟨-, h1, h2⟩
    rw [← h1] at h2
    split_ifs at h2 <;> omega
  · simp
  · split_ifs
    · simp
    · exact List.nodup_cons.mpr ⟨fun h => hc _ _ h _ rfl, litCells_nodup _⟩
  · split_ifs
    · exact List.nodup_cons.mpr ⟨fun h => hc _ _ h _ rfl, litCells_nodup _⟩
    · simp

lemma outs_spec (hw : G.WF) {u w : ℕ} (hu : u < G.n) (h : w ∈ G.outs u) :
    w < G.n ∧ w ≠ u ∧ ∃ v ∈ G.outsV (G.dec u), w = G.enc v := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
  obtain ⟨hvv, hne⟩ := outsV_valid hw (G.dec_valid hu) v hv
  refine ⟨G.enc_lt hvv, fun he => hne ?_, v, hv, rfl⟩
  rw [← G.dec_enc hvv, he]

lemma outs_nodup (hw : G.WF) {u : ℕ} (hu : u < G.n) : (G.outs u).Nodup := by
  refine (G.outsV_nodup _).map_on fun a ha b hb h => G.enc_inj ?_ ?_ h
  · exact (outsV_valid hw (G.dec_valid hu) a ha).1
  · exact (outsV_valid hw (G.dec_valid hu) b hb).1

theorem dig_ok (hw : G.WF) : G.dig.ok := by
  refine ⟨?_, fun a ha => ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun u hu => ?_, ?_⟩
    · exact (outs_nodup hw (List.mem_range.mp hu)).map fun a b h => by simpa using h
    · refine List.nodup_range.pairwise_of_forall_ne fun u _ w _ hne => ?_
      simp only [Function.onFun, List.disjoint_left, List.mem_map]
      rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
      exact hne (congrArg Prod.fst hb).symm
  · obtain ⟨u, w⟩ := a
    obtain ⟨hu, hwu⟩ := G.mem_arcs.mp ha
    obtain ⟨h1, h2, -⟩ := outs_spec hw hu hwu
    exact ⟨hu, h1, Ne.symm h2⟩

theorem dig_out2 : G.dig.out2 := by
  intro u
  have : (G.dig.arcs.filter fun a => a.1 = u) =
      (List.range G.n).flatMap fun u' => if u' = u then (G.outs u').map fun w => (u', w) else [] := by
    simp only [dig, List.filter_flatMap]
    congr 1; funext u'
    split_ifs with h
    · subst h; exact List.filter_eq_self.mpr (by simp)
    · exact List.filter_eq_nil_iff.mpr (by simp; intro _ _; exact h)
  rw [this, List.length_flatMap]
  rw [sum_range_single _ u _ (fun i _ hi => by simp [hi])]
  split_ifs <;> simp [outs, G.outsV_length_le]

end TS

end Pts
