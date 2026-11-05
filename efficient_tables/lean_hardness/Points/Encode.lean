import Points.Reduction
import Mahaney.TableLang
import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.NatCodes
import Complexitylib.Classes.NP.Reduction

/-!
# Stage 2: the reduction on bit strings, in polynomial time

Encodings.
* A graph on `n` vertices is `pair 1^n M` with `M` an `n × n` adjacency matrix (row-major); the
  edges are the pairs `a < b` with `M[a n + b] = 1`, in index order (`edgesOf`). `EHPLang` is the
  set of such strings whose edges have an edge-Hamiltonian path.
* A table instance `(k, pts, K)` is `pair 1^k (pair K.bits (encL (pts.map encPt)))`, the points as
  self-delimiting blocks (`encPt`: constructor and sign bits, then `|z|` in binary). `GenLang` is
  the set of encodings of instances of `GenTableOpt`.

`ehp_le_gen : EHPLang ≤ₚ GenLang` (complexitylib's polynomial-time many-one reducibility), and
`genLang_NPHard_of : NPHard EHPLang → NPHard GenLang`.
-/

namespace Pts

open Complexity TableGeneration Operations Mahaney

/-! ### Encodings -/

/-- A list of strings as consecutive self-delimiting blocks. -/
def encL : List (List Bool) → List Bool
  | [] => []
  | s :: L => pair s (encL L)

def encPt : Point → List Bool
  | .int z => pair [false, decide (z < 0)] z.natAbs.bits
  | .frac m => pair [true, decide (m < 0)] m.natAbs.bits

def encG (k : ℕ) (pts : List Point) (K : ℕ) : List Bool :=
  pair (un k) (pair K.bits (encL (pts.map encPt)))

/-- The points-as-input problem as a language. -/
def GenLang : Language := {w | ∃ k pts K, w = encG k pts K ∧ GenTableOpt k pts K}

lemma pair_eq_append (x y : List Bool) : pair x y = pair x [] ++ y := by simp [pair]

lemma pair_ne_nil (x y : List Bool) : pair x y ≠ [] := by simp [pair, delimit]

lemma encL_injective : Function.Injective encL := by
  intro L M h
  induction L generalizing M with
  | nil => cases M with
    | nil => rfl
    | cons s M => exact absurd h.symm (pair_ne_nil _ _)
  | cons s L ih => cases M with
    | nil => exact absurd h (pair_ne_nil _ _)
    | cons t M =>
      obtain ⟨h1, h2⟩ := pair_inj h
      rw [h1, ih h2]

lemma encPt_injective : Function.Injective encPt := by
  have key : ∀ {z w : ℤ}, decide (z < 0) = decide (w < 0) → z.natAbs = w.natAbs → z = w := by
    intro z w h1 h2
    rcases Int.natAbs_eq_natAbs_iff.mp h2 with h | h
    · exact h
    · subst h; by_cases hw : w < 0 <;> simp [hw] at h1 <;> omega
  intro p q h
  cases p <;> cases q <;> simp only [encPt] at h <;> obtain ⟨h1, h2⟩ := pair_inj h <;>
    simp only [List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and, and_true,
      true_and] at h1
  · rw [key h1 (bits_injective h2)]
  · rw [key h1 (bits_injective h2)]

lemma encG_injective {k k' : ℕ} {p p' : List Point} {K K' : ℕ}
    (h : encG k p K = encG k' p' K') : k = k' ∧ p = p' ∧ K = K' := by
  obtain ⟨h1, h2⟩ := pair_inj h
  obtain ⟨h3, h4⟩ := pair_inj h2
  refine ⟨by simpa using congrArg List.length h1, ?_, bits_injective h3⟩
  exact (List.map_injective_iff.mpr encPt_injective) (encL_injective h4)

lemma mem_GenLang (k : ℕ) (p : List Point) (K : ℕ) :
    encG k p K ∈ GenLang ↔ GenTableOpt k p K := by
  constructor
  · rintro ⟨k', p', K', h, hg⟩
    obtain ⟨rfl, rfl, rfl⟩ := encG_injective h
    exact hg
  · exact fun hg => ⟨k, p, K, rfl, hg⟩

/-! ### Graphs as adjacency matrices -/

def edgeCond (n : ℕ) (M : List Bool) (i : ℕ) : Prop := i / n < i % n ∧ M[i]?.getD false = true

instance (n : ℕ) (M : List Bool) : DecidablePred (edgeCond n M) := fun i => by
  unfold edgeCond; infer_instance

/-- The edges of the graph, in index order. -/
def edgesOf (n : ℕ) (M : List Bool) : List (Finset ℕ) :=
  (List.range (n * n)).filterMap fun i => if edgeCond n M i then some {i / n, i % n} else none

/-- The edge-Hamiltonian path problem as a language. -/
def EHPLang : Language :=
  {x | ∃ n M, x = pair (un n) M ∧ M.length = n * n ∧ EHP (edgesOf n M)}

lemma pair_eq_pair_ord {a b c d : ℕ} (hab : a < b) (hcd : c < d) (h : ({a, b} : Finset ℕ) = {c, d}) :
    a = c ∧ b = d := by
  have ha : a ∈ ({c, d} : Finset ℕ) := h ▸ by simp
  have hb : b ∈ ({c, d} : Finset ℕ) := h ▸ by simp
  have hc : c ∈ ({a, b} : Finset ℕ) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  omega

lemma edgesOf_card (n : ℕ) (M : List Bool) : ∀ e ∈ edgesOf n M, e.card = 2 := by
  intro e he
  simp only [edgesOf, List.mem_filterMap, List.mem_range] at he
  obtain ⟨i, _, hi⟩ := he
  split_ifs at hi with hc
  simp only [Option.some.injEq] at hi
  subst hi
  exact Finset.card_pair (Nat.ne_of_lt hc.1)

lemma edgesOf_nodup (n : ℕ) (M : List Bool) : (edgesOf n M).Nodup := by
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro i j e hi hj
  split_ifs at hi hj with hci hcj
  · simp only [Option.mem_def, Option.some.injEq] at hi hj
    obtain ⟨h1, h2⟩ := pair_eq_pair_ord hci.1 hcj.1 (hi.trans hj.symm)
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod j n, h1, h2]
  all_goals simp at hi hj

lemma length_filterMap_range (m : ℕ) (c : ℕ → Prop) [DecidablePred c] {β : Type*} (g : ℕ → β) :
    ((List.range m).filterMap fun i => if c i then some (g i) else none).length =
      ((Finset.range m).filter c).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filterMap_append, List.length_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases hc : c m
    · simp [hc, Finset.card_insert_of_notMem (by simp : m ∉ (Finset.range m).filter c)]
    · simp [hc]

/-! ### Label bits -/

/-- `8^a + 8^b` in binary, LSB first, for `a < b`. -/
def labBits (a b : ℕ) : List Bool :=
  List.replicate (3 * a) false ++ true :: List.replicate (3 * b - 3 * a - 1) false ++ [true]

lemma lsbVal_append (L M : List Bool) : lsbVal (L ++ M) = lsbVal L + 2 ^ L.length * lsbVal M := by
  induction L with
  | nil => simp [lsbVal]
  | cons b L ih => simp [lsbVal, ih, Nat.bit_val, pow_succ]; ring

lemma lsbVal_replicate_false (p : ℕ) : lsbVal (List.replicate p false) = 0 := by
  induction p with
  | zero => rfl
  | succ p ih => simp [List.replicate_succ, lsbVal, ih, Nat.bit_val]

lemma labBits_val {a b : ℕ} (hab : a < b) : lsbVal (labBits a b) = 8 ^ a + 8 ^ b := by
  have e8a : (8 : ℕ) ^ a = 2 ^ (3 * a) := by rw [pow_mul]; norm_num
  have e8b : (8 : ℕ) ^ b = 2 ^ (3 * a) * 2 ^ (3 * b - 3 * a - 1) * 2 := by
    rw [← pow_add, ← pow_succ, show 3 * a + (3 * b - 3 * a - 1) + 1 = 3 * b by omega, pow_mul]
    norm_num
  unfold labBits
  rw [lsbVal_append, lsbVal_append, lsbVal_replicate_false, List.length_append,
    List.length_replicate, List.length_cons, List.length_replicate]
  simp only [lsbVal, Nat.bit_val, lsbVal_append, lsbVal_replicate_false, List.length_replicate,
    Bool.toNat_true, Bool.toNat_false]
  rw [e8a, e8b]
  ring

lemma labBits_canon (a b : ℕ) : Canon (labBits a b) := by
  right; simp [labBits]

lemma lab_nonneg (e : Finset ℕ) : 0 ≤ lab e := by
  simp only [lab, oct_empty]; positivity

lemma encPt_lab {a b : ℕ} (hab : a < b) :
    encPt (.int (lab {a, b})) = pair [false, false] (labBits a b) := by
  have hpos := lab_nonneg {a, b}
  have hneg : decide (lab {a, b} < 0) = false := decide_eq_false (by omega)
  have hbits : (lab {a, b}).natAbs.bits = labBits a b := by
    rw [← bits_lsbVal_of_canon (labBits_canon a b), labBits_val hab, lab_pair (Nat.ne_of_lt hab),
      show ((8 : ℤ) ^ a + 8 ^ b) = ((8 ^ a + 8 ^ b : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
  simp only [encPt, hneg, hbits]

lemma encPt_zero : encPt (.int 0) = pair [false, false] [] := by simp [encPt]

/-! ### The map -/

/-- Well-formed graph encodings. -/
def WFG (x : List Bool) : Prop :=
  x = pair (pairFst x) (pairSnd x) ∧ (∀ i < (pairFst x).length, (pairFst x)[i]?.getD false = true) ∧
    (pairSnd x).length = (pairFst x).length * (pairFst x).length

/-- Entry `i` of the output's point list. -/
def entry (n : ℕ) (M : List Bool) (i : ℕ) : List Bool :=
  if edgeCond n M i then pair (pair [false, false] (labBits (i / n) (i % n))) [] else []

open Classical in
/-- The reduction on strings. -/
noncomputable def redG (x : List Bool) : List Bool :=
  if WFG x then
    pair (un 2) (pair (7 * (((Finset.range ((pairFst x).length * (pairFst x).length)).filter
        (edgeCond (pairFst x).length (pairSnd x))).card + 1)).bits
      (pair (pair [false, false] []) ((List.range ((pairFst x).length * (pairFst x).length)).flatMap
        (entry (pairFst x).length (pairSnd x)))))
  else encG 0 [] 0

lemma encL_points (n : ℕ) (M : List Bool) :
    encL ((pointsOf (edgesOf n M)).map encPt) =
      pair (pair [false, false] []) ((List.range (n * n)).flatMap (entry n M)) := by
  have hflat : ∀ L : List (List Bool), encL L = (L.map fun s => pair s []).flatten := by
    intro L; induction L with
    | nil => rfl
    | cons s L ih => rw [encL, pair_eq_append, ih]; simp
  rw [hflat, pair_eq_append (pair [false, false] [])]
  simp only [pointsOf, ptsZ, List.map_cons, List.map_map, encPt_zero, List.flatten_cons]
  congr 1
  unfold edgesOf
  induction (List.range (n * n)) with
  | nil => rfl
  | cons i l ih =>
    by_cases hc : edgeCond n M i
    · simp only [List.filterMap_cons, hc, if_true, List.map_cons, Function.comp_apply,
        List.flatten_cons, List.flatMap_cons, entry]
      rw [encPt_lab hc.1, ih]
    · simp only [List.filterMap_cons, hc, if_false, List.flatMap_cons, entry, List.nil_append]
      exact ih

lemma redG_wf {x : List Bool} (hx : WFG x) :
    redG x = encG 2 (pointsOf (edgesOf (pairFst x).length (pairSnd x)))
      (7 * ((edgesOf (pairFst x).length (pairSnd x)).length + 1)) := by
  classical
  rw [redG, if_pos hx, encG, encL_points]
  congr 3
  unfold edgesOf
  rw [length_filterMap_range]

/-! ### Correctness -/

lemma WFG_iff (x : List Bool) : WFG x ↔ ∃ n M, x = pair (un n) M ∧ M.length = n * n := by
  constructor
  · rintro ⟨hx, hall, hlen⟩
    refine ⟨(pairFst x).length, pairSnd x, ?_, hlen⟩
    have : pairFst x = un (pairFst x).length := by
      apply List.eq_replicate_iff.mpr ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      simpa [List.getElem?_eq_getElem hi] using hall i hi
    calc x = pair (pairFst x) (pairSnd x) := hx
      _ = pair (un (pairFst x).length) (pairSnd x) := by rw [← this]
  · rintro ⟨n, M, rfl, hM⟩
    refine ⟨by simp, fun i hi => ?_, by simpa using hM⟩
    simp at hi ⊢; simp [List.getElem?_replicate, hi]

theorem redG_correct (x : List Bool) : x ∈ EHPLang ↔ redG x ∈ GenLang := by
  classical
  by_cases hx : WFG x
  · rw [redG_wf hx, mem_GenLang]
    obtain ⟨n, M, rfl, hM⟩ := (WFG_iff x).mp hx
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
    rw [← reduction_correct (edgesOf_nodup n M) (edgesOf_card n M)]
    constructor
    · rintro ⟨n', M', h, _, hE⟩
      obtain ⟨h1, rfl⟩ := pair_inj h
      have : n' = n := by simpa using (congrArg List.length h1).symm
      subst this; exact hE
    · exact fun hE => ⟨n, M, rfl, hM, hE⟩
  · rw [redG, if_neg hx, mem_GenLang]
    constructor
    · rintro ⟨n, M, rfl, hM, _⟩; exact absurd ((WFG_iff _).mpr ⟨n, M, rfl, hM⟩) hx
    · rintro ⟨hk, _⟩; exact absurd hk (by decide)

/-! ### Polynomial time -/

lemma WFG_FPPred : FPPred WFG := by
  have h1 := FPPred.strEq (f := id) (g := fun w => pair (pairFst w) (pairSnd w)) id_mem_FP
    (by polytime)
  have h2 : FPPred fun w : List Bool =>
      ∀ i < (pairFst w).length, (pairFst w)[i]?.getD false = true := by
    have hb := FPPred.getBit (bits := fun y : List Bool => pairFst (pairFst y))
      (i := fun y => (pairSnd y).length) (by polytime) UnaryFn.index
    refine (FPPred.forall_lt (UnaryFn.length pairFst_mem_FP) hb).of_iff fun w => ?_
    simp [pairFst_pair, pairSnd_pair]
  have h3 : FPPred fun w : List Bool =>
      (pairSnd w).length = (pairFst w).length * (pairFst w).length :=
    FPPred.eq (UnaryFn.length pairSnd_mem_FP)
      ((UnaryFn.length pairFst_mem_FP).mul (UnaryFn.length pairFst_mem_FP))
  exact (h1.and (h2.and h3)).of_iff fun w => by simp [WFG]

/-- The edge test, read from `pair x 1^i`. -/
lemma edgeCond_FPPred : FPPred fun y : List Bool =>
    edgeCond (pairFst (pairFst y)).length (pairSnd (pairFst y)) (pairSnd y).length := by
  have hn : UnaryFn fun y : List Bool => (pairFst (pairFst y)).length := UnaryFn.length (by polytime)
  have ha := UnaryFn.index.div hn
  have hb := UnaryFn.index.mod hn
  have hbit := FPPred.getBit (bits := fun y : List Bool => pairSnd (pairFst y))
    (i := fun y => (pairSnd y).length) (by polytime) UnaryFn.index
  exact (FPPred.lt ha hb).and hbit

lemma labBits_FP {a b : List Bool → ℕ} (ha : UnaryFn a) (hb : UnaryFn b) :
    (fun y => labBits (a y) (b y)) ∈ FP := by
  unfold labBits
  have h1 := ((UnaryFn.const 3).mul ha).replicate_mem_FP false
  have h2 := ((((UnaryFn.const 3).mul hb).sub ((UnaryFn.const 3).mul ha)).sub
    (UnaryFn.const 1)).replicate_mem_FP false
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP h1 (mem_FP_comp h2 (Cobham.cons_mem_FP true)))
    (constFn_mem_FP [true])

lemma entry_FP : (fun y : List Bool =>
    entry (pairFst (pairFst y)).length (pairSnd (pairFst y)) (pairSnd y).length) ∈ FP := by
  classical
  have hn : UnaryFn fun y : List Bool => (pairFst (pairFst y)).length := UnaryFn.length (by polytime)
  have hl := labBits_FP (UnaryFn.index.div hn) (UnaryFn.index.mod hn)
  have hblk : (fun y : List Bool => pair (pair [false, false]
      (labBits ((pairSnd y).length / (pairFst (pairFst y)).length)
        ((pairSnd y).length % (pairFst (pairFst y)).length))) []) ∈ FP :=
    mem_FP_pair (mem_FP_pair (constFn_mem_FP _) hl) (constFn_mem_FP [])
  exact mem_FP_of_eq (FPPred.ite_mem_FP edgeCond_FPPred hblk (constFn_mem_FP [])) fun y => by
    simp [entry]

theorem redG_mem_FP : redG ∈ FP := by
  classical
  have hnn : UnaryFn fun x : List Bool => (pairFst x).length * (pairFst x).length :=
    (UnaryFn.length pairFst_mem_FP).mul (UnaryFn.length pairFst_mem_FP)
  have hcnt := UnaryFn.count hnn edgeCond_FPPred
  have hK := bits_mem_FP (((UnaryFn.const 7).mul (hcnt.add (UnaryFn.const 1))))
  have hflat := flatMap_range_mem_FP entry_FP hnn.mem_FP
  have hyes : (fun x : List Bool => pair (un 2) (pair (7 * (((Finset.range
        ((pairFst x).length * (pairFst x).length)).filter
        (edgeCond (pairFst x).length (pairSnd x))).card + 1)).bits
      (pair (pair [false, false] []) ((List.range ((pairFst x).length * (pairFst x).length)).flatMap
        (entry (pairFst x).length (pairSnd x)))))) ∈ FP := by
    refine mem_FP_of_eq (mem_FP_pair (constFn_mem_FP (un 2)) (mem_FP_pair hK
      (mem_FP_pair (constFn_mem_FP (pair [false, false] [])) hflat))) fun x => ?_
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  refine mem_FP_of_eq (FPPred.ite_mem_FP WFG_FPPred hyes (constFn_mem_FP (encG 0 [] 0)))
    fun x => ?_
  unfold redG
  congr

/-! ### The headline -/

/-- **Edge-Hamiltonian path reduces to the points-as-input table problem** (Karp reduction over
complexitylib's Turing machines). -/
theorem ehp_le_gen : EHPLang ≤ₚ GenLang := ⟨redG, redG_mem_FP, redG_correct⟩

theorem genLang_NPHard_of (h : NPHard EHPLang) : NPHard GenLang :=
  fun L hL => (h L hL).trans ehp_le_gen

end Pts
