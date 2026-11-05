import Points.SatFP
import Complexitylib.SAT.CookLevin.Assembly

/-!
# Stage 3c: SAT ≤ₚ the points-as-input table problem, and NP-hardness

The reduction `satRed` maps a CNF encoding `φ.encode` (φ nonempty) to the encoded table instance
of the digraph of its tokens; the empty formula goes to a fixed yes-instance, and strings that
encode no formula go to the no-instance `encG 0 [] 0`.

* `encL_tableOf`: the encoded points are two concatenations over vertex ranges.
* `satRed_mem_FP`: the reduction is polynomial-time.
* `sat_le_gen : SAT.language ≤ₚ GenLang` and **`genLang_NPHard : NPHard GenLang`**.
-/

namespace Pts

open Complexity SAT Mahaney TableGeneration Operations

namespace TS

/-! ### The encoded points -/

/-- One encoded point `8^a + 8^b − 9`. -/
def blk (a b : ℕ) : List Bool := pair (pair [false, false] (dBits a b)) []

/-- The point of the arc edge `{4u + 2, 4w}`. -/
def ablk (u w : ℕ) : List Bool := blk (min (4 * u + 2) (4 * w)) (max (4 * u + 2) (4 * w))

/-- The gadget points of vertex `v`. -/
def gblk (v : ℕ) : List Bool := blk (4 * v) (4 * v + 1) ++ blk (4 * v + 1) (4 * v + 3) ++
  blk (4 * v + 1) (4 * v + 2)

variable (G : TS)

/-- The arc points of vertex `u`. -/
def oblk (u : ℕ) : List Bool := ablk u (G.o1 u) ++ if G.two u then ablk u (G.o2 u) else []

/-- All encoded points. -/
def outBits : List Bool :=
  (List.range G.n).flatMap gblk ++ (List.range G.n).flatMap G.oblk

/-- The number of arcs. -/
def nArcs : ℕ := G.n + ((Finset.range G.n).filter G.two).card

variable {G}

lemma encL_eq (L : List (List Bool)) : encL L = (L.map fun s => pair s []).flatten := by
  induction L with
  | nil => rfl
  | cons s L ih => rw [encL, pair_eq_append, ih]; simp

lemma F_pair {a b : ℕ} (hab : a < b) :
    pair (encPt (.int (dl {0, 1} {a, b}))) [] = blk a b := by rw [encPt_dl hab]; rfl

lemma F_arc (u w : ℕ) : pair (encPt (.int (dl {0, 1} (arcE (u, w))))) [] = ablk u w := by
  show pair (encPt (.int (dl {0, 1} {4 * u + 2, 4 * w}))) [] = ablk u w
  unfold ablk
  have hne : 4 * u + 2 ≠ 4 * w := by omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, F_pair h]
  · rw [min_eq_right h.le, max_eq_left h.le,
      show ({4 * u + 2, 4 * w} : Finset ℕ) = {4 * w, 4 * u + 2} from Finset.pair_comm _ _, F_pair h]

lemma length_outs_sum :
    ((List.range G.n).map fun u => (G.outs u).length).sum = G.nArcs := by
  have : ∀ u ∈ List.range G.n, (G.outs u).length = 1 + if G.two u then 1 else 0 := by
    intro u hu; rw [outs_eq (List.mem_range.mp hu)]; split_ifs <;> simp
  rw [List.map_congr_left this, nArcs]
  induction G.n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; omega
    · omega

lemma arcs_length : G.dig.arcs.length = G.nArcs := by
  rw [← length_outs_sum]
  simp [dig, List.length_flatMap]

/-- **The encoded points of the table instance.** -/
theorem encL_tableOf (hn : 0 < G.n) :
    encL ((tableOf G.dig).map encPt) = G.outBits := by
  have hhead : (HE G.dig).headD ∅ = {0, 1} := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hn
    simp only [HE, dig, hm, zero_add, List.range_succ_eq_map, List.flatMap_cons, gadE, vin, vmid,
      List.cons_append, List.headD_cons]
    try rfl
  rw [encL_eq, tableOf, pointsC, ptsC, hhead, List.map_map, List.map_map]
  unfold HE outBits
  simp only [List.map_append, List.flatten_append]
  have fmf : ∀ {α β γ : Type} (F : α → List β) (g : γ → List α) (L : List γ),
      ((L.flatMap g).map F).flatten = L.flatMap fun v => ((g v).map F).flatten := by
    intro α β γ F g L; induction L with
    | nil => rfl
    | cons a L ih => simp [List.flatMap_cons, ih]
  simp only [dig]
  simp only [List.map_map]
  rw [fmf, fmf]
  congr 1
  · refine List.flatMap_congr fun v _ => ?_
    simp only [gadE, vin, vmid, vleaf, vout, List.map_cons, List.map_nil, Function.comp_apply,
      List.flatten_cons, List.flatten_nil, List.append_nil, gblk, List.append_assoc]
    rw [F_pair (by omega), F_pair (by omega), F_pair (by omega)]
  · refine List.flatMap_congr fun u hu => ?_
    rw [List.map_map, outs_eq (List.mem_range.mp hu), oblk]
    split_ifs
    · simp only [List.map_cons, List.map_nil, Function.comp_apply, F_arc, List.flatten_cons,
        List.flatten_nil, List.append_nil]
    · simp only [List.map_cons, List.map_nil, Function.comp_apply, F_arc, List.flatten_cons,
        List.flatten_nil, List.append_nil]

/-! ### The reduction -/

/-- A fixed satisfiable formula: `x₀`. -/
def yesφ : CNF := [[⟨true, 0⟩]]


open Classical in
/-- **The reduction** from SAT encodings to table instances. -/
noncomputable def satRed (z : List Bool) : List Bool :=
  if z ∈ Valid then
    if z = [] then encG 2 (tableOf (ofList (CNF.tokens yesφ)).dig) (7 * (3 * (ofList (CNF.tokens yesφ)).dig.n + (ofList (CNF.tokens yesφ)).dig.arcs.length))
    else pair (un 2) (pair (7 * (3 * (ofBits z).n + (ofBits z).nArcs)).bits (ofBits z).outBits)
  else encG 0 [] 0

lemma n_pos {G : TS} (hw : G.WF) : 0 < G.n := by
  have := hw.2.1; unfold n; omega

lemma out_eq_encG {G : TS} (hn : 0 < G.n) :
    pair (un 2) (pair (7 * (3 * G.n + G.nArcs)).bits G.outBits) =
      encG 2 (tableOf G.dig) (7 * (3 * G.dig.n + G.dig.arcs.length)) := by
  rw [encG, encL_tableOf hn, arcs_length]; rfl

lemma encode_inj {φ ψ : CNF} (h : φ.encode = ψ.encode) : φ = ψ := by
  have := congrArg CNF.decode? h
  rw [CNF.decode?_encode, CNF.decode?_encode] at this
  exact Option.some.inj this

theorem satRed_correct (z : List Bool) : z ∈ SAT.language ↔ satRed z ∈ GenLang := by
  classical
  unfold satRed
  by_cases hv : z ∈ Valid
  · rw [if_pos hv]
    obtain ⟨φ, rfl⟩ := (valid_iff _).mp hv
    by_cases h0 : φ.encode = []
    · rw [if_pos h0, mem_GenLang]
      have hyes : CNF.Satisfiable yesφ := ⟨[true], rfl⟩
      have hne : yesφ ≠ [] := List.cons_ne_nil _ _
      have hY := (sat_iff_table hne).mp hyes
      constructor
      · intro _; exact hY
      intro _
      have : φ = [] := encode_inj (by rw [h0]; rfl)
      exact ⟨φ, rfl, this ▸ CNF.satisfiable_nil⟩
    · rw [if_neg h0]
      have hφ : φ ≠ [] := by rintro rfl; exact h0 rfl
      have hw := wf_tokens hφ
      rw [ofBits_encode, out_eq_encG (n_pos hw), mem_GenLang, ← sat_iff_table hφ]
      constructor
      · rintro ⟨ψ, h, hs⟩; rwa [encode_inj h]
      · exact fun hs => ⟨φ, rfl, hs⟩
  · rw [if_neg hv, mem_GenLang]
    constructor
    · rintro ⟨φ, rfl, -⟩; exact absurd ((valid_iff _).mpr ⟨φ, rfl⟩) hv
    · rintro ⟨hk, -⟩; exact absurd hk (by decide)

/-! ### Polynomial time -/

lemma dBits_FP {a b : List Bool → ℕ} (ha : UnaryFn a) (hb : UnaryFn b) :
    (fun y => dBits (a y) (b y)) ∈ FP := by
  classical
  have r := fun {f : List Bool → ℕ} (hf : UnaryFn f) (c : Bool) => hf.replicate_mem_FP c
  have h0 := Cobham.appendFn_mem_FP (constFn_mem_FP [false, false, false])
    (r (((UnaryFn.const 3).mul hb).sub (UnaryFn.const 3)) true)
  have h1 := r ((UnaryFn.const 3).mul hb) true
  have h2 := Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP
    (constFn_mem_FP [true, true, true, false]) (r (((UnaryFn.const 3).mul ha).sub (UnaryFn.const 4)) true))
    (r (((UnaryFn.const 3).mul hb).sub ((UnaryFn.const 3).mul ha)) false)) (constFn_mem_FP [true])
  exact mem_FP_of_eq (FPPred.ite_mem_FP (FPPred.eq ha (UnaryFn.const 0))
    (FPPred.ite_mem_FP (FPPred.eq hb (UnaryFn.const 1)) (constFn_mem_FP []) h0)
    (FPPred.ite_mem_FP (FPPred.eq ha (UnaryFn.const 1)) h1 h2)) fun y => by simp [dBits]

lemma blk_FP {a b : List Bool → ℕ} (ha : UnaryFn a) (hb : UnaryFn b) :
    (fun y => blk (a y) (b y)) ∈ FP :=
  mem_FP_pair (mem_FP_pair (constFn_mem_FP _) (dBits_FP ha hb)) (constFn_mem_FP [])

lemma ablk_FP {u w : List Bool → ℕ} (hu : UnaryFn u) (hw : UnaryFn w) :
    (fun y => ablk (u y) (w y)) ∈ FP := by
  have h1 := ((UnaryFn.const 4).mul hu).add (UnaryFn.const 2)
  have h2 := (UnaryFn.const 4).mul hw
  exact blk_FP (h1.min h2) (h1.max h2)

theorem satRed_mem_FP : satRed ∈ FP := by
  classical
  have hid : (fun z : List Bool => z) ∈ FP := id_mem_FP
  have hT := fp_T hid
  have hn : UnaryFn fun z : List Bool => (ofBits z).n := (fp_N6 hid).add ((UnaryFn.const 4).mul hT)
  have hcount : UnaryFn fun z : List Bool => ((Finset.range (ofBits z).n).filter (ofBits z).two).card :=
    (UnaryFn.count hn (fp_two (Z := pairFst) pairFst_mem_FP UnaryFn.index)).of_eq fun z => by
      simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  have hK := bits_mem_FP (((UnaryFn.const 7).mul (((UnaryFn.const 3).mul hn).add (hn.add hcount))))
  have hE1 : (fun w : List Bool => gblk (pairSnd w).length) ∈ FP := by
    have hv := (UnaryFn.const 4).mul (UnaryFn.index)
    exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP
      (blk_FP hv (hv.add (UnaryFn.const 1))) (blk_FP (hv.add (UnaryFn.const 1)) (hv.add (UnaryFn.const 3))))
      (blk_FP (hv.add (UnaryFn.const 1)) (hv.add (UnaryFn.const 2)))
  have hE2 : (fun w : List Bool => (ofBits (pairFst w)).oblk (pairSnd w).length) ∈ FP := by
    have ho1 := fp_o1 (Z := pairFst) pairFst_mem_FP UnaryFn.index
    have ho2 := fp_o2 (Z := pairFst) pairFst_mem_FP UnaryFn.index
    have htwo := fp_two (Z := pairFst) pairFst_mem_FP UnaryFn.index
    exact Cobham.appendFn_mem_FP (ablk_FP UnaryFn.index ho1)
      (FPPred.ite_mem_FP htwo (ablk_FP UnaryFn.index ho2) (constFn_mem_FP []))
  have hout : (fun z : List Bool => (ofBits z).outBits) ∈ FP := by
    refine mem_FP_of_eq (Cobham.appendFn_mem_FP (flatMap_range_mem_FP hE1 hn.mem_FP)
      (flatMap_range_mem_FP hE2 hn.mem_FP)) fun z => ?_
    simp only [outBits, List.length_replicate, pairFst_pair, pairSnd_pair]
  have hyes : (fun z : List Bool =>
      pair (un 2) (pair (7 * (3 * (ofBits z).n + (ofBits z).nArcs)).bits (ofBits z).outBits)) ∈ FP :=
    mem_FP_of_eq (mem_FP_pair (constFn_mem_FP (un 2)) (mem_FP_pair hK hout)) fun z => by
      simp only [nArcs]
  have hnil : FPPred fun z : List Bool => z = [] :=
    (FPPred.eq (UnaryFn.length hid) (UnaryFn.const 0)).of_iff fun z => List.length_eq_zero_iff
  refine mem_FP_of_eq (FPPred.ite_mem_FP valid_FPPred (FPPred.ite_mem_FP hnil
    (constFn_mem_FP (encG 2 (tableOf (ofList (CNF.tokens yesφ)).dig) (7 * (3 * (ofList (CNF.tokens yesφ)).dig.n + (ofList (CNF.tokens yesφ)).dig.arcs.length)))) hyes)
    (constFn_mem_FP (encG 0 [] 0))) fun z => ?_
  unfold satRed
  congr

end TS

/-! ### The headline -/

/-- **SAT reduces to the points-as-input table problem** (Karp reduction over complexitylib's
Turing machines). -/
theorem sat_le_gen : SAT.language ≤ₚ GenLang :=
  ⟨TS.satRed, TS.satRed_mem_FP, TS.satRed_correct⟩

/-- **The points-as-input table problem is NP-hard.** -/
theorem genLang_NPHard : NPHard GenLang :=
  fun L hL => (SAT.NPHard_language L hL).trans sat_le_gen

