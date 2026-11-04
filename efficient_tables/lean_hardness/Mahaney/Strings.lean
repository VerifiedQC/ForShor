import Complexitylib.Tactic.PolyTime
import Complexitylib.Classes.P.BoundedQuant
import Mahaney.Bits

/-!
# Polynomial-time tests on bit strings

Equality of two polynomial-time strings and the bounded lexicographic test `LexLeB` are
polynomial-time predicates (`FPPred`).
-/

namespace Mahaney

open Complexity

/-- Equality of the bits of two polynomial-time strings at a polynomial-time position. -/
theorem FPPred.bitEq {F G : List Bool → List Bool} {I : List Bool → ℕ} (hF : F ∈ FP)
    (hG : G ∈ FP) (hI : UnaryFn I) :
    FPPred fun w => (F w)[I w]?.getD false = (G w)[I w]?.getD false := by
  have hA := FPPred.getBit hF hI
  have hB := FPPred.getBit hG hI
  refine ((hA.and hB).or (hA.not.and hB.not)).of_iff fun w => ?_
  cases (F w)[I w]?.getD false <;> cases (G w)[I w]?.getD false <;> simp

/-- Bitwise characterisation of list equality. -/
lemma eq_iff_bits (y a : List Bool) :
    y = a ↔ y.length = a.length ∧ ∀ i < y.length, y[i]?.getD false = a[i]?.getD false := by
  constructor
  · rintro rfl; simp
  · rintro ⟨hl, h⟩
    apply List.ext_getElem hl
    intro i hi hi'
    have := h i hi
    simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.getD_some]
      at this
    exact this

/-- **String equality is polynomial-time.** -/
theorem FPPred.strEq {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    FPPred fun z => f z = g z := by
  have hbit := FPPred.bitEq (mem_FP_comp pairFst_mem_FP hf) (mem_FP_comp pairFst_mem_FP hg)
    UnaryFn.index
  have hall := FPPred.forall_lt (UnaryFn.length hf) hbit
  refine ((FPPred.eq (UnaryFn.length hf) (UnaryFn.length hg)).and hall).of_iff fun z => ?_
  rw [eq_iff_bits]
  simp [Function.comp_def, pairFst_pair, pairSnd_pair]

/-- **The bounded lexicographic test is polynomial-time.** -/
theorem FPPred.lexLeB {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    FPPred fun z => LexLeB (f z) (g z) := by
  -- inner loop: reads `w' = pair (pair z 1^k) 1^j`
  have hf2 : (fun w : List Bool => f (pairFst (pairFst w))) ∈ FP :=
    mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hf
  have hg2 : (fun w : List Bool => g (pairFst (pairFst w))) ∈ FP :=
    mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hg
  have hinner := FPPred.forall_lt (n := fun w => (pairSnd w).length) UnaryFn.index
    (FPPred.bitEq hf2 hg2 UnaryFn.index)
  -- outer body: reads `w = pair z 1^k`
  have hf1 : (fun w : List Bool => f (pairFst w)) ∈ FP := mem_FP_comp pairFst_mem_FP hf
  have hg1 : (fun w : List Bool => g (pairFst w)) ∈ FP := mem_FP_comp pairFst_mem_FP hg
  have himp := (hinner.not.or ((FPPred.getBit hf1 UnaryFn.index).not.or
    (FPPred.getBit hg1 UnaryFn.index)))
  refine (FPPred.forall_lt (UnaryFn.length hf) himp).of_iff fun z => ?_
  simp only [LexLeB, pairFst_pair, pairSnd_pair, List.length_replicate]
  apply forall_congr'; intro k; apply imp_congr_right; intro _
  constructor
  · rintro (h | h | h) hag
    · exact absurd hag h
    · exact fun hy => absurd hy h
    · exact fun _ => h
  · intro h
    by_cases hag : ∀ j < k, (f z)[j]?.getD false = (g z)[j]?.getD false
    · by_cases hy : (f z)[k]?.getD false = true
      · exact Or.inr (Or.inr (h hag hy))
      · exact Or.inr (Or.inl hy)
    · exact Or.inl hag

end Mahaney
