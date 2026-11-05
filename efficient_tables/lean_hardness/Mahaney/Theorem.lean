import Mahaney.Step
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Models.TuringMachine.OutputBounds
import Complexitylib.SAT.CookLevin.Assembly
import Complexitylib.Classes.NP.Reduction
import Mathlib.Data.Set.Finite.List

/-!
# Mahaney's theorem on complexitylib's Turing machines

`mahaney : Sparse S → NPHard S → P = NP`, for complexitylib's `P`, `NP`, `NPHard` (multi-tape
Turing machines, Karp reductions). No hypothesis is cited: the left set is in NP
(`LeftSAT_mem_NP`), the pruning algorithm is iterated in `FP` (`iterS_mem_FP`), it decides
SAT (`decides_sat`), and Cook–Levin is complexitylib's `SAT.NPComplete_language`.
-/

namespace Mahaney

open Complexity

/-- A language is sparse when its members of length `≤ m` number at most a polynomial in `m`. -/
def Sparse (S : Language) : Prop :=
  ∃ p : Polynomial ℕ, ∀ m, {x | x ∈ S ∧ x.length ≤ m}.ncard ≤ p.eval m

/-! ### Polynomial-time numbers -/

lemma UnaryFn.polyEval (p : Polynomial ℕ) {f : List Bool → ℕ} (hf : UnaryFn f) :
    UnaryFn fun z => p.eval (f z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact (hp.add hq).of_eq fun z => by simp
  | monomial n a =>
    exact ((UnaryFn.const a).mul (hf.pow_const n)).of_eq fun z => by simp

lemma outLen {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ q : Polynomial ℕ, ∀ x, (f x).length ≤ q.eval x.length := by
  obtain ⟨k, tm, q, h⟩ := mem_FP_iff_computesInTime_polynomial.mp hf
  exact ⟨q, fun x => h.output_length_le x⟩

/-! ### The loop -/

section Loop

variable (R : List Bool → List Bool) (s : List Bool → ℕ)

/-- Valid abstract states: input, level, candidate list with every prefix `< 2^level`. -/
def AState : Type := {a : List Bool × ℕ × List ℕ // ∀ p ∈ a.2.2, p < 2 ^ a.2.1}

def encA (a : AState) : List Bool := encS a.1.1 a.1.2.1 a.1.2.2

def stepA (a : AState) : AState :=
  ⟨(a.1.1, a.1.2.1 + 1, stepL (gq R a.1.1) (s a.1.1) a.1.2.1 a.1.2.2),
    stepL_lt _ _ _ a.2⟩

def start (z : List Bool) : AState := ⟨(z, 0, [0]), by simp⟩

lemma iterate_stepA (z : List Bool) (k : ℕ) :
    ((stepA R s)^[k] (start z)).1 = (z, k, lvl (gq R z) (s z) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [stepA, ih]
    rfl

/-- The initial machine state. -/
def initS (z : List Bool) : List Bool := encS z 0 [0]

/-- The machine run: `|z| + 1` levels. -/
noncomputable def iterS (z : List Bool) : List Bool :=
  (stepS R s)^[(un (z.length + 1)).length] (initS z)

lemma length_blocks (w : ℕ) (L : List ℕ) : (blocks w L).length = L.length * w := by
  simp [blocks, List.length_flatten, Function.comp_def, List.sum_replicate]

lemma length_encS (z : List Bool) (i : ℕ) (L : List ℕ) :
    (encS z i L).length = 2 * z.length + 2 + (2 * i + 2 + (2 * L.length + 2 + L.length * i)) := by
  simp [encS, length_blocks]

lemma stepS_encA (a : AState) : stepS R s (encA a) = encA (stepA R s a) := by
  unfold encA stepA
  exact stepS_encS R s a.1.1 a.1.2.1 a.2

variable {R s}

lemma iterate_initS (z : List Bool) (k : ℕ) :
    (stepS R s)^[k] (initS z) = encS z k (lvl (gq R z) (s z) k) := by
  have hsemi : Function.Semiconj (encA) (stepA R s) (stepS R s) := fun a =>
    (stepS_encA R s a).symm
  have h0 : initS z = encA (start z) := rfl
  rw [h0, ← hsemi.iterate_right]
  unfold encA
  rw [iterate_stepA]

lemma iterS_eq (z : List Bool) :
    iterS R s z = encS z (z.length + 1) (lvl (gq R z) (s z) (z.length + 1)) := by
  unfold iterS
  rw [List.length_replicate, iterate_initS]

lemma iterS_mem_FP (hR : R ∈ FP) (hs : UnaryFn s) : iterS R s ∈ FP := by
  have hM : UnaryFn fun z => max (s z) 1 := hs.max (UnaryFn.const 1)
  have hn : UnaryFn fun z : List Bool => z.length + 1 := (UnaryFn.length id_mem_FP).add (UnaryFn.const 1)
  have hW : UnaryFn fun z : List Bool => 2 * z.length + 2 + (2 * (z.length + 1) + 2 +
      (2 * max (s z) 1 + 2 + max (s z) 1 * (z.length + 1))) := by
    refine ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 2)).add
      ((((UnaryFn.const 2).mul hn).add (UnaryFn.const 2)).add
        ((((UnaryFn.const 2).mul hM).add (UnaryFn.const 2)).add (hM.mul hn)))).of_eq fun z => ?_
    rfl
  have hinit : initS ∈ FP := by
    refine mem_FP_of_eq (f := fun z => pair z (pair [] (pair [true] []))) (by polytime) fun z => ?_
    simp [initS, encS, blocks, bits]
  have hruler : (fun z : List Bool => un (z.length + 1)) ∈ FP := hn.mem_FP
  refine iterate_mem_FP (stepS_mem_FP hR hs) hinit hruler hW.mem_FP ?_
  intro z k hk
  simp only [List.length_replicate] at hk ⊢
  rw [iterate_initS, length_encS]
  have hL := lvl_length (gq R z) (s z) k
  have h1 : (lvl (gq R z) (s z) k).length * k ≤ max (s z) 1 * (z.length + 1) :=
    Nat.mul_le_mul hL hk
  omega

end Loop

/-! ### Correctness -/

section Correct

variable {S : Language} {R : List Bool → List Bool} (hRS : ∀ x, x ∈ LeftSAT ↔ R x ∈ S)
  {s : List Bool → ℕ}

/-- The core's query map for input `z`. -/
def fz (R : List Bool → List Bool) (z : List Bool) (y : ℕ) : List Bool :=
  R (pair z (bits (z.length + 1) y))

/-- The core's satisfaction predicate for input `z`. -/
def satz (z : List Bool) (a : ℕ) : Prop := SAT.Witness z (bits (z.length + 1) a)

lemma pad_bits {n j q : ℕ} (hj : j ≤ n) (hq : q < 2 ^ j) :
    bits j q ++ List.replicate (n - j) false = bits n (query n j q) := by
  apply val_injective_of_length (by simp; omega)
  rw [val_append_zeros, val_bits_of_lt hq, val_bits_of_lt (query_lt hj hq), query]

lemma gq_eq (z : List Bool) {j q : ℕ} (hj : j ≤ z.length + 1) (hq : q < 2 ^ j) :
    gq R z j q = fz R z (query (z.length + 1) j q) := by
  simp only [gq, qs, fz]
  rw [pad_bits hj hq]

include hRS in
lemma left_red (z : List Bool) {y : ℕ} (hy : y < 2 ^ (z.length + 1)) :
    Left (z.length + 1) (satz z) y ↔ fz R z y ∈ S := by
  rw [fz, ← hRS]
  simp only [LeftSAT, LeftRel, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, length_bits,
    true_and, Left, satz]
  constructor
  · rintro ⟨a, ha, hw, hya⟩
    refine ⟨bits (z.length + 1) a, by simp, hw, ?_⟩
    rw [← lexLe_iff_bounded (by simp), ← val_le_iff_lexLe (by simp), val_bits_of_lt hy,
      val_bits_of_lt ha]
    exact hya
  · rintro ⟨α, hα, hw, hle⟩
    rw [← lexLe_iff_bounded (by simp [hα]), ← val_le_iff_lexLe (by simp [hα]),
      val_bits_of_lt hy] at hle
    refine ⟨val α, hα ▸ val_lt α, ?_, hle⟩
    have := bits_val α
    rw [hα] at this
    rw [this]; exact hw

/-- The sparse cover of the reduction's outputs. -/
noncomputable def coverT (R : List Bool → List Bool) (S : Language) (z : List Bool) :
    Finset (List Bool) := by
  classical
  exact ((Finset.range (2 ^ (z.length + 1))).image (fz R z)).filter (· ∈ S)

lemma coverT_card {p q : Polynomial ℕ} (hp : ∀ m, {x | x ∈ S ∧ x.length ≤ m}.ncard ≤ p.eval m)
    (hq : ∀ x, (R x).length ≤ q.eval x.length) (z : List Bool) :
    (coverT R S z).card ≤ p.eval (q.eval (3 * z.length + 3)) := by
  classical
  set m := q.eval (3 * z.length + 3)
  have hsub : (↑(coverT R S z) : Set (List Bool)) ⊆ {x | x ∈ S ∧ x.length ≤ m} := by
    intro x hx
    simp only [coverT, Finset.coe_filter, Finset.mem_image, Finset.mem_range,
      Set.mem_ofPred_eq] at hx
    obtain ⟨⟨y, _, rfl⟩, hS⟩ := hx
    refine ⟨hS, ?_⟩
    have := hq (pair z (bits (z.length + 1) y))
    simp only [pair_length, length_bits] at this
    simp only [fz, m]
    convert this using 2; ring
  have hfin : {x : List Bool | x ∈ S ∧ x.length ≤ m}.Finite :=
    (List.finite_length_le Bool m).subset fun x hx => hx.2
  calc (coverT R S z).card = (↑(coverT R S z) : Set (List Bool)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin
    _ ≤ p.eval m := hp m

include hRS in
/-- **The machine decides SAT.** -/
theorem decides_sat {p q : Polynomial ℕ}
    (hp : ∀ m, {x | x ∈ S ∧ x.length ≤ m}.ncard ≤ p.eval m)
    (hq : ∀ x, (R x).length ≤ q.eval x.length)
    (hs : ∀ z, s z = p.eval (q.eval (3 * z.length + 3))) (z : List Bool) :
    (∃ t < rC (iterS R s z), SAT.Witness z (blk (iterS R s z) t)) ↔ z ∈ SAT.language := by
  classical
  have hlv := lvl_toFinset (s := s z) (f := fz R z) (g := gq R z) (n := z.length + 1)
    (fun j hj q hq => gq_eq z hj hq) (z.length + 1) le_rfl
  have hacc := accepts_iff (sat := satz z) (f := fz R z) (S := S) (T := coverT R S z) (s := s z)
    (fun y hy => left_red hRS z hy)
    (fun y hy hyS => by
      simp only [coverT, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      exact ⟨⟨y, hy, rfl⟩, hyS⟩)
    (by rw [hs z]; exact coverT_card hp hq z)
  rw [iterS_eq, rC_encS, sat_iff_exists_full]
  have hlt := lvl_lt (gq R z) (s z) (z.length + 1)
  constructor
  · rintro ⟨t, ht, hw⟩
    rw [blk_encS z (z.length + 1) _ ht] at hw
    have hmem := getD_mem ht
    have : accepts (z.length + 1) (satz z) (fz R z) (s z) := by
      refine ⟨_, ?_, hlt _ hmem, hw⟩
      rw [← hlv]; exact List.mem_toFinset.mpr hmem
    obtain ⟨a, ha, hsa⟩ := hacc.mp this
    exact ⟨bits (z.length + 1) a, by simp, hsa⟩
  · rintro ⟨α, hα, hw⟩
    have : ∃ a < 2 ^ (z.length + 1), satz z a := ⟨val α, by rw [← hα]; exact val_lt α, by
      unfold satz; have := bits_val α; rw [hα] at this; rw [this]; exact hw⟩
    obtain ⟨a, ha, _, hsa⟩ := hacc.mpr this
    rw [← hlv, List.mem_toFinset] at ha
    obtain ⟨t, ht, rfl⟩ := mem_iff_index.mp ha
    exact ⟨t, ht, by rw [blk_encS z (z.length + 1) _ ht]; exact hsa⟩

end Correct

/-! ### Mahaney's theorem -/

/-- **Mahaney's theorem.** If a sparse language is NP-hard (under polynomial-time many-one
reductions), then `P = NP`. Over complexitylib's multi-tape Turing machines. -/
theorem mahaney {S : Language} (hS : Sparse S) (hH : NPHard S) : P = NP := by
  classical
  obtain ⟨R, hR, hRS⟩ := hH LeftSAT LeftSAT_mem_NP
  obtain ⟨q, hq⟩ := outLen hR
  obtain ⟨p, hp⟩ := hS
  set s : List Bool → ℕ := fun z => p.eval (q.eval (3 * z.length + 3)) with hsdef
  have hsF : UnaryFn s := UnaryFn.polyEval p (UnaryFn.polyEval q
    (((UnaryFn.const 3).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 3)))
  have hit := iterS_mem_FP (R := R) (s := s) hR hsF
  -- the acceptance test
  have hW : FPPred fun x => pair (pairFst x) (blk (iterS R s (pairFst x)) (pairSnd x).length) ∈
      pairLang SAT.Witness := by
    obtain ⟨g, hg, hgL⟩ := mem_P_iff_exists_decisionFn.mp SAT.pairLang_witness_mem_P
    refine ((FPPred.of_flag hg).comp (mem_FP_pair pairFst_mem_FP
      (blk_comp (mem_FP_comp pairFst_mem_FP hit) UnaryFn.index))).of_iff fun x => (hgL _).symm
  have hdec := FPPred.exists_lt (rC_comp hit) hW
  have hP : SAT.language ∈ P := by
    refine FPPred.mem_P (hdec.of_iff fun z => ?_)
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate, mem_pairLang_pair]
    exact decides_sat hRS hp hq (fun _ => rfl) z
  exact (SAT.NPComplete_language.mem_P_iff_P_eq_NP).mp hP

end Mahaney
