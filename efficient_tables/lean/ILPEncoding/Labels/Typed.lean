import ILPEncoding.Labels.Labels
import Foundations.Counting.TypedConsistency

/-! # Typed Label Bridge
Defines `toTyped`, mapping an affine `Label` to a `DecoratedLabel`. Proves `toTyped_alphabet`, `typed_word_pairwise` for label words, and `actual_labels_in_fixed_words`.
-/

namespace Paper.F6TypedBridge

open Paper.AffineNat Paper.CountStage.TypedDecorationWords

def toTyped (label : Paper.AffineNat.Label) : DecoratedLabel :=
  ⟨⟨label.k, label.hk⟩, label.r, label.d, label.c⟩

theorem toTyped_labelsAt (label : Paper.AffineNat.Label)
    (hc : label.c ≤ 27 * label.k ^ 3) :
    toTyped label ∈ labelsAt ⟨label.k, label.hk⟩ := by
  unfold labelsAt
  apply List.mem_flatMap.mpr
  refine ⟨label.r, by simpa using label.hr, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨label.d, by simpa using label.hd, ?_⟩
  apply List.mem_map.mpr
  refine ⟨label.c, by simp; omega, rfl⟩

theorem toTyped_alphabet {K : Nat} (label : Paper.AffineNat.Label)
    (hk : label.k ≤ K) (hc : label.c ≤ 27 * label.k ^ 3) :
    toTyped label ∈ decorationLabels K := by
  unfold decorationLabels
  apply List.mem_flatMap.mpr
  have hge := label.hk
  have hlt : label.k - 2 < K - 1 := by omega
  refine ⟨label.k - 2, by simpa using hlt, ?_⟩
  have heq :
      (⟨label.k - 2 + 2, by omega⟩ : ArityIndex) =
        ⟨label.k, label.hk⟩ := Subtype.ext (by
          change label.k - 2 + 2 = label.k
          omega)
  simpa only [heq] using toTyped_labelsAt label hc

theorem compatible_of_shared (x y : Paper.AffineNat.Label)
    (hshared : x.k = y.k → x.d = y.d ∧ x.c = y.c) :
    labelCompatibleFixed (toTyped x) (toTyped y) := by
  by_cases hk : x.k = y.k
  · obtain ⟨hd,hc⟩ := hshared hk
    right
    exact ⟨hd,hc⟩
  · left
    intro heq
    exact hk (congrArg Subtype.val heq)

theorem typed_word_pairwise (labels : List Paper.AffineNat.Label)
    (d c : Nat → Nat)
    (hshared : ∀ label ∈ labels, label.d = d label.k ∧ label.c = c label.k) :
    List.Pairwise labelCompatibleFixed (labels.map toTyped) := by
  induction labels with
  | nil => simp
  | cons label rest ih =>
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro other hother
        rcases List.mem_map.mp hother with ⟨otherLabel, hmem, rfl⟩
        apply compatible_of_shared label otherLabel
        intro hk
        have hleft := hshared label (by simp)
        have hright := hshared otherLabel (by simp [hmem])
        constructor
        · calc
            label.d = d label.k := hleft.1
            _ = d otherLabel.k := by rw [hk]
            _ = otherLabel.d := hright.1.symm
        · calc
            label.c = c label.k := hleft.2
            _ = c otherLabel.k := by rw [hk]
            _ = otherLabel.c := hright.2.symm
      · apply ih
        intro other hmem
        exact hshared other (by simp [hmem])

theorem actual_labels_in_fixed_words (K U : Nat)
    (labels : List Paper.AffineNat.Label) (d c : Nat → Nat)
    (hcap : ∀ label ∈ labels, label.k ≤ K ∧
      label.c ≤ 27 * label.k ^ 3)
    (hshared : ∀ label ∈ labels, label.d = d label.k ∧ label.c = c label.k)
    (hbudget : qProduct labelQ (labels.map toTyped) ≤ U) :
    labels.map toTyped ∈ consistentBudgetWordsFixed K U := by
  apply consistentBudgetWordsFixed_complete
  · intro x hx
    rcases List.mem_map.mp hx with ⟨label, hmem, rfl⟩
    exact toTyped_alphabet label (hcap label hmem).1 (hcap label hmem).2
  · exact hbudget
  · exact typed_word_pairwise labels d c hshared

end Paper.F6TypedBridge
