import Foundations.Counting.TypedWords
import Mathlib.Tactic

/-!
# Consistency filter on decorated words

Defines when two decorated labels can share one ladder (`labelCompatibleFixed`, requiring the kink/column and charge to agree) and the filtered word list `consistentBudgetWordsFixed`. Proves the consistent words are completely retained (`consistentBudgetWordsFixed_complete`) and counted within the candidate bound (`consistentWordsFixed_count_le_candidates`); it also records a residue-varying example pair.
-/

namespace Paper.CountStage.TypedDecorationWords

/-- Labels can share one ladder exactly when both the kink/column and charge agree.
The residue/row coordinate is occurrence-specific and is intentionally omitted. -/
def labelCompatibleFixed (x y : DecoratedLabel) : Prop :=
  x.arity ≠ y.arity ∨ (x.col = y.col ∧ x.charge = y.charge)

instance : DecidableRel labelCompatibleFixed := by
  intro x y
  unfold labelCompatibleFixed
  infer_instance

def repeatedArityConsistentFixed (w : List DecoratedLabel) : Bool :=
  decide (List.Pairwise labelCompatibleFixed w)

def consistentBudgetWordsFixed (K U : Nat) : List (List DecoratedLabel) :=
  (typedBudgetWords (decorationLabels K) labelQ
    (fun x => by have hk := x.arity.property; unfold labelQ; omega) U).filter
      repeatedArityConsistentFixed

theorem consistentWordsFixed_count_le_candidates (K U : Nat) :
    (consistentBudgetWordsFixed K U).length ≤
      (typedBudgetWords (decorationLabels K) labelQ
        (fun x => by have hk := x.arity.property; unfold labelQ; omega) U).length := by
  exact List.length_filter_le _ _

theorem consistentWordsFixed_count_lt_three_U10 (K U : Nat) (hU : 1 ≤ U) :
    ((consistentBudgetWordsFixed K U).length : ℚ) < 3 * (U : ℚ) ^ 10 := by
  calc
    ((consistentBudgetWordsFixed K U).length : ℚ) ≤
        ((typedBudgetWords (decorationLabels K) labelQ
          (fun x => by have hk := x.arity.property; unfold labelQ; omega) U).length : ℚ) := by
            exact_mod_cast consistentWordsFixed_count_le_candidates K U
    _ < 3 * (U : ℚ) ^ 10 := actualDecorationWords_count_lt_three_U10 K U hU

theorem consistentBudgetWordsFixed_complete (K U : Nat) (w : List DecoratedLabel)
    (hlabels : ∀ x ∈ w, x ∈ decorationLabels K)
    (hbudget : qProduct labelQ w ≤ U)
    (hconsistent : List.Pairwise labelCompatibleFixed w) :
    w ∈ consistentBudgetWordsFixed K U := by
  apply List.mem_filter.mpr
  refine ⟨actualDecorationWords_complete K U w hlabels hbudget, ?_⟩
  simp [repeatedArityConsistentFixed, hconsistent]

/-- Two occurrences of the same arity may use different residues while sharing
the same column and charge. The corrected predicate accepts this pair. -/
def residueLabel0 : DecoratedLabel := ⟨⟨2, by omega⟩, 0, 0, 0⟩
def residueLabel1 : DecoratedLabel := ⟨⟨2, by omega⟩, 1, 0, 0⟩
def residueVaryingPair : List DecoratedLabel := [residueLabel0, residueLabel1]

theorem residueVaryingPair_same_arity : residueLabel0.arity = residueLabel1.arity := by
  decide

theorem residueVaryingPair_different_rows :
    residueLabel0.row ≠ residueLabel1.row := by
  decide

theorem residueVaryingPair_fixed_compatible :
    List.Pairwise labelCompatibleFixed residueVaryingPair := by
  decide

theorem residueVaryingPair_old_filter_rejects :
    ¬ List.Pairwise labelCompatible residueVaryingPair := by
  decide

theorem residueVaryingPair_is_member_at_k2 :
    ∀ x ∈ residueVaryingPair, x ∈ labelsAt ⟨2, by omega⟩ := by
  intro x hx
  simp [residueVaryingPair, residueLabel0, residueLabel1] at hx
  rcases hx with rfl | rfl
  · decide
  · decide

end Paper.CountStage.TypedDecorationWords
