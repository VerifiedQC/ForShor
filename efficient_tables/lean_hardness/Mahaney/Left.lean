import Complexitylib.Classes.NP.Verifier
import Complexitylib.Classes.P.Verdict
import Complexitylib.SAT.Headline
import Mahaney.Strings

/-!
# The left set of SAT is in NP (discharges `hleft`'s membership half)

A left-set query is a string `x`, read as `pair z y`: `z` a (claimed) CNF encoding and `y` a
bit string of length `|z| + 1`. It is in `LeftSAT` when some assignment `α` of length
`|z| + 1` satisfies the CNF encoded by `z` (`SAT.Witness z α`, from complexitylib) and
`y ≤ α` lexicographically. Satisfiability itself is `∃ α` with `|α| = |z| + 1`
(`sat_iff_exists_full`), because assignments pad with `false`.

`LeftSAT_mem_NP`: the verifier `LeftVer` is in `P` and witnesses are linear, so
`LeftSAT ∈ NP` by complexitylib's `mem_NP_of_poly_witness`.
-/

namespace Mahaney

open Complexity

/-- The left-set relation between a query `x` and a witness `α`. -/
def LeftRel (x α : List Bool) : Prop :=
  (pairSnd x).length = (pairFst x).length + 1 ∧ α.length = (pairFst x).length + 1 ∧
    SAT.Witness (pairFst x) α ∧ LexLeB (pairSnd x) α

/-- The left set of SAT. -/
def LeftSAT : Language := {x | ∃ α, LeftRel x α}

/-- Its verifier, on `pair x α`. -/
def LeftVer : Language := {u | LeftRel (pairFst u) (pairSnd u)}

theorem LeftVer_mem_P : LeftVer ∈ P := by
  apply FPPred.mem_P
  have hW : FPPred fun u => pair (pairFst (pairFst u)) (pairSnd u) ∈ pairLang SAT.Witness := by
    obtain ⟨g, hg, hgL⟩ := mem_P_iff_exists_decisionFn.mp SAT.pairLang_witness_mem_P
    exact ((FPPred.of_flag hg).comp (by polytime)).of_iff fun u => (hgL _).symm
  have h1 : FPPred fun u => (pairSnd (pairFst u)).length = (pairFst (pairFst u)).length + 1 := by
    polytime
  have h2 : FPPred fun u => (pairSnd u).length = (pairFst (pairFst u)).length + 1 := by
    polytime
  have h3 := FPPred.lexLeB (f := fun u => pairSnd (pairFst u)) (g := pairSnd) (by polytime)
    (by polytime)
  refine (h1.and (h2.and (hW.and h3))).of_iff fun u => ?_
  simp only [LeftVer, LeftRel, Set.mem_setOf_eq, mem_pairLang_pair]

theorem LeftSAT_mem_NP : LeftSAT ∈ NP := by
  refine mem_NP_of_poly_witness (Polynomial.X + 1) LeftVer_mem_P ?_ ?_
  · intro x α h
    simp only [LeftVer, LeftRel, Set.mem_setOf_eq, pairFst_pair, pairSnd_pair] at h
    have hx : (pairFst x).length ≤ x.length := pairFst_length_le x
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega
  · intro x
    simp [LeftSAT, LeftVer]

/-! ### Satisfiability through full-length assignments -/

lemma eval_pad (α : List Bool) (m : ℕ) (φ : SAT.CNF) :
    SAT.CNF.eval (α ++ List.replicate m false) φ = SAT.CNF.eval α φ := by
  have hget : ∀ i, SAT.Assignment.get (α ++ List.replicate m false) i = SAT.Assignment.get α i := by
    intro i
    simp only [SAT.Assignment.get]
    by_cases hi : i < α.length
    · rw [List.getElem?_append_left hi]
    · push_neg at hi
      rw [List.getElem?_append_right hi, List.getElem?_eq_none hi]
      by_cases hj : i - α.length < m
      · simp [List.getElem?_replicate, hj]
      · simp [List.getElem?_replicate, hj]
  have hc : SAT.Clause.eval (α ++ List.replicate m false) = SAT.Clause.eval α := by
    funext c
    unfold SAT.Clause.eval
    congr 1
    funext l
    unfold SAT.Lit.eval
    rw [hget]
  unfold SAT.CNF.eval
  rw [hc]

/-- A string is in the SAT language iff some full-length (`|z| + 1`) assignment witnesses it. -/
theorem sat_iff_exists_full (z : List Bool) :
    z ∈ SAT.language ↔ ∃ α, α.length = z.length + 1 ∧ SAT.Witness z α := by
  rw [SAT.mem_language_iff_witness]
  constructor
  · rintro ⟨α, φ, hz, hlen, hev⟩
    refine ⟨α ++ List.replicate (z.length + 1 - α.length) false, by simp; omega, φ, hz,
      by simp; omega, by rw [eval_pad]; exact hev⟩
  · rintro ⟨α, _, hw⟩
    exact ⟨α, hw⟩

end Mahaney
