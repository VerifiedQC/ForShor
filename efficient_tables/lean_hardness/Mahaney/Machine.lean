import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.Iterate
import Mahaney.Blocks
import Mahaney.Left

/-!
# One level of the pruning algorithm as a polynomial-time string function

The machine state for input `z` at level `i` with candidate list `L` is
`encS z i L = pair z (pair 1^i (pair 1^|L| B))`, where `B` concatenates the `i`-bit blocks
`bits i p`, `p ∈ L`. The step `stepS = stageB ∘ stageA`:
* `stageA` writes the children of every block and keeps those that pass pruning 1, comparing
  the reduction's outputs on the left-set queries `qs`;
* `stageB` keeps the blocks of rank `< s z` (pruning 2).
This file proves both stages are in `FP`; `Mahaney.Step` proves what they compute.
-/

namespace Mahaney

open Complexity

/-- Unary numbers. -/
abbrev un (n : ℕ) : List Bool := List.replicate n true

/-- Concatenated `w`-bit blocks. -/
def blocks (w : ℕ) (L : List ℕ) : List Bool := (L.map (bits w)).flatten

/-- The left-set query for an `j`-bit prefix string `e` of input `z`: `e` padded with zeros to
`|z| + 1` bits, paired with `z`. -/
def qs (z : List Bool) (j : ℕ) (e : List Bool) : List Bool :=
  pair z (e ++ List.replicate (z.length + 1 - j) false)

/-- The machine state. -/
def encS (z : List Bool) (i : ℕ) (L : List ℕ) : List Bool :=
  pair z (pair (un i) (pair (un L.length) (blocks i L)))

/-! ### Reading the state -/

def rZ (w : List Bool) : List Bool := pairFst w
def rI (w : List Bool) : ℕ := (pairFst (pairSnd w)).length
def rC (w : List Bool) : ℕ := (pairFst (pairSnd (pairSnd w))).length
def rB (w : List Bool) : List Bool := pairSnd (pairSnd (pairSnd w))

/-- Block `j` of the state. -/
def blk (w : List Bool) (j : ℕ) : List Bool := ((rB w).drop (j * rI w)).take (rI w)

/-- Child `t` of the state's blocks: block `t / 2` extended by the bit `t % 2`. -/
def childS (w : List Bool) (t : ℕ) : List Bool := blk w (t / 2) ++ [decide (t % 2 = 1)]

section Stages

variable (R : List Bool → List Bool) (s : List Bool → ℕ)

/-- Pruning-1 test for child `t`. -/
def keepA (w : List Bool) (t : ℕ) : Prop :=
  ∀ t' < 2 * rC w, R (qs (rZ w) (rI w + 1) (childS w t')) = R (qs (rZ w) (rI w + 1) (childS w t)) →
    LexLeB (childS w t') (childS w t)

/-- Pruning-2 rank of block `t`. -/
noncomputable def rankS (v : List Bool) (t : ℕ) : ℕ := by
  classical
  exact ((Finset.range (rC v)).filter fun t' => LexLeB (blk v t') (blk v t) ∧ blk v t' ≠ blk v t).card

/-- Stage A: children, then pruning 1. -/
noncomputable def stageA (w : List Bool) : List Bool := by
  classical
  exact pair (rZ w) (pair (un (rI w + 1)) (pair
    (un ((Finset.range (2 * rC w)).filter fun t => keepA R w t).card)
    ((List.range (2 * rC w)).flatMap fun t => if keepA R w t then childS w t else [])))

/-- Stage B: pruning 2. -/
noncomputable def stageB (v : List Bool) : List Bool := by
  classical
  exact pair (rZ v) (pair (un (rI v)) (pair
    (un ((Finset.range (rC v)).filter fun t => rankS v t < s (rZ v)).card)
    ((List.range (rC v)).flatMap fun t => if rankS v t < s (rZ v) then blk v t else [])))

/-- One level of the algorithm. -/
noncomputable def stepS (w : List Bool) : List Bool := stageB s (stageA R w)

end Stages

/-! ### Polynomial time -/

/-- Reading the state through a polynomial-time map. -/
lemma rZ_comp {h : List Bool → List Bool} (hh : h ∈ FP) : (fun x => rZ (h x)) ∈ FP := by
  unfold rZ; polytime

lemma rI_comp {h : List Bool → List Bool} (hh : h ∈ FP) : UnaryFn fun x => rI (h x) := by
  unfold rI; exact UnaryFn.length (by polytime)

lemma rC_comp {h : List Bool → List Bool} (hh : h ∈ FP) : UnaryFn fun x => rC (h x) := by
  unfold rC; exact UnaryFn.length (by polytime)

lemma rB_comp {h : List Bool → List Bool} (hh : h ∈ FP) : (fun x => rB (h x)) ∈ FP := by
  unfold rB; polytime

lemma blk_comp {h : List Bool → List Bool} (hh : h ∈ FP) {j : List Bool → ℕ} (hj : UnaryFn j) :
    (fun x => blk (h x) (j x)) ∈ FP := by
  unfold blk
  exact take_mem_FP (drop_mem_FP (rB_comp hh) (hj.mul (rI_comp hh))) (rI_comp hh)

lemma childS_comp {h : List Bool → List Bool} (hh : h ∈ FP) {t : List Bool → ℕ} (ht : UnaryFn t) :
    (fun x => childS (h x) (t x)) ∈ FP := by
  unfold childS
  have hb := blk_comp hh (ht.div (UnaryFn.const 2))
  have hbit : (fun x => [decide (t x % 2 = 1)]) ∈ FP := by
    classical
    have := FPPred.flag_mem_FP (FPPred.eq (ht.mod (UnaryFn.const 2)) (UnaryFn.const 1))
    simpa using this
  exact Cobham.appendFn_mem_FP hb hbit

lemma qs_comp {zf e : List Bool → List Bool} (hz : zf ∈ FP) (he : e ∈ FP) {j : List Bool → ℕ}
    (hj : UnaryFn j) : (fun x => qs (zf x) (j x) (e x)) ∈ FP := by
  unfold qs
  have hpad : (fun x => List.replicate ((zf x).length + 1 - j x) false) ∈ FP :=
    ((UnaryFn.length hz).add (UnaryFn.const 1) |>.sub hj).replicate_mem_FP false
  exact mem_FP_pair hz (Cobham.appendFn_mem_FP he hpad)

/-! ### The stages are polynomial-time -/

section StagesFP

variable {R : List Bool → List Bool} (hR : R ∈ FP) {s : List Bool → ℕ} (hs : UnaryFn s)
include hR

/-- The pruning-1 test, read from `pair w 1^t`. -/
lemma keepA_FPPred : FPPred fun x => keepA R (pairFst x) (pairSnd x).length := by
  have hW : (fun y : List Bool => pairFst (pairFst y)) ∈ FP := by polytime
  have ht : UnaryFn fun y : List Bool => (pairSnd (pairFst y)).length :=
    UnaryFn.length (by polytime)
  have hA : (fun y => R (qs (rZ (pairFst (pairFst y))) (rI (pairFst (pairFst y)) + 1)
      (childS (pairFst (pairFst y)) (pairSnd y).length))) ∈ FP :=
    mem_FP_comp (qs_comp (rZ_comp hW) (childS_comp hW UnaryFn.index)
      ((rI_comp hW).add (UnaryFn.const 1))) hR
  have hB : (fun y => R (qs (rZ (pairFst (pairFst y))) (rI (pairFst (pairFst y)) + 1)
      (childS (pairFst (pairFst y)) (pairSnd (pairFst y)).length))) ∈ FP :=
    mem_FP_comp (qs_comp (rZ_comp hW) (childS_comp hW ht)
      ((rI_comp hW).add (UnaryFn.const 1))) hR
  have hL := FPPred.lexLeB (childS_comp hW UnaryFn.index) (childS_comp hW ht)
  have hbody := (FPPred.strEq hA hB).not.or hL
  have hn : UnaryFn fun x : List Bool => 2 * rC (pairFst x) :=
    (UnaryFn.const 2).mul (rC_comp pairFst_mem_FP)
  refine (FPPred.forall_lt hn hbody).of_iff fun x => ?_
  simp only [keepA, pairFst_pair, pairSnd_pair, List.length_replicate, imp_iff_not_or]

lemma stageA_mem_FP : stageA R ∈ FP := by
  classical
  have hp := keepA_FPPred hR
  have hE : (fun x => if keepA R (pairFst x) (pairSnd x).length
      then childS (pairFst x) (pairSnd x).length else []) ∈ FP :=
    FPPred.ite_mem_FP hp (childS_comp pairFst_mem_FP UnaryFn.index) (constFn_mem_FP [])
  have hm : UnaryFn fun w => 2 * rC w := (UnaryFn.const 2).mul (rC_comp id_mem_FP)
  have hflat := flatMap_range_mem_FP hE hm.mem_FP
  have hcnt := UnaryFn.count hm hp
  have hI : UnaryFn fun w => rI w + 1 := (rI_comp id_mem_FP).add (UnaryFn.const 1)
  refine mem_FP_of_eq (mem_FP_pair (rZ_comp id_mem_FP) (mem_FP_pair hI.mem_FP
    (mem_FP_pair hcnt.mem_FP hflat))) fun w => ?_
  simp only [stageA, pairFst_pair, pairSnd_pair, List.length_replicate]
  congr

omit hR in
/-- The pruning-2 rank, read from `pair v 1^t`. -/
lemma rankS_unary : UnaryFn fun x => rankS (pairFst x) (pairSnd x).length := by
  classical
  have hV : (fun y : List Bool => pairFst (pairFst y)) ∈ FP := by polytime
  have ht : UnaryFn fun y : List Bool => (pairSnd (pairFst y)).length :=
    UnaryFn.length (by polytime)
  have h1 := blk_comp hV UnaryFn.index
  have h2 := blk_comp hV ht
  have hbody := (FPPred.lexLeB h1 h2).and (FPPred.strEq h1 h2).not
  refine (UnaryFn.count (rC_comp pairFst_mem_FP) hbody).of_eq fun x => ?_
  simp only [rankS, pairFst_pair, pairSnd_pair, List.length_replicate]

omit hR in
include hs in
lemma stageB_mem_FP : stageB s ∈ FP := by
  classical
  have hp : FPPred fun x => rankS (pairFst x) (pairSnd x).length < s (rZ (pairFst x)) := by
    refine FPPred.lt rankS_unary ?_
    unfold rZ
    exact hs.comp (by polytime)
  have hE : (fun x => if rankS (pairFst x) (pairSnd x).length < s (rZ (pairFst x))
      then blk (pairFst x) (pairSnd x).length else []) ∈ FP :=
    FPPred.ite_mem_FP hp (blk_comp pairFst_mem_FP UnaryFn.index) (constFn_mem_FP [])
  have hm : UnaryFn fun v => rC v := rC_comp id_mem_FP
  have hflat := flatMap_range_mem_FP hE hm.mem_FP
  have hcnt := UnaryFn.count hm hp
  refine mem_FP_of_eq (mem_FP_pair (rZ_comp id_mem_FP) (mem_FP_pair (rI_comp id_mem_FP).mem_FP
    (mem_FP_pair hcnt.mem_FP hflat))) fun v => ?_
  simp only [stageB, pairFst_pair, pairSnd_pair, List.length_replicate, id]

include hs in
lemma stepS_mem_FP : stepS R s ∈ FP := mem_FP_comp (stageA_mem_FP hR) (stageB_mem_FP hs)

end StagesFP

end Mahaney
