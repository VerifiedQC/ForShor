import Foundations.PairedCharge.Defs

namespace PairedCharge

open Classical in
theorem points_def :
    (pointAt 0 = Pt.fin 0 ∧ pointAt 1 = Pt.inf ∧ pointAt 2 = Pt.fin (-1) ∧
      pointAt 3 = Pt.fin 1 ∧
      ∀ j : ℕ, 1 ≤ j →
        pointAt (4 * j) = Pt.fin (-(2 : ℚ) ^ (-(j : ℤ))) ∧
        pointAt (4 * j + 1) = Pt.fin ((2 : ℚ) ^ (-(j : ℤ))) ∧
        pointAt (4 * j + 2) = Pt.fin (-(2 : ℚ) ^ (j : ℤ)) ∧
        pointAt (4 * j + 3) = Pt.fin ((2 : ℚ) ^ (j : ℤ))) ∧
    ∀ k : ℕ, 2 ≤ k →
      fMinus k = ((Finset.range (2 * k - 1)).filter
        (fun i => ∃ j : ℕ, 1 ≤ j ∧ pointAt i = Pt.fin (-(2 : ℚ) ^ (-(j : ℤ))))).card := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [pointAt]
  · simp [pointAt]
  · simp [pointAt]
  · simp [pointAt]
  · intro j hj
    have h1 : (4 * j) % 4 = 0 := by omega
    have h2 : (4 * j + 1) % 4 = 1 := by omega
    have h3 : (4 * j + 2) % 4 = 2 := by omega
    have h4 : (4 * j + 3) % 4 = 3 := by omega
    have d1 : (4 * j) / 4 = j := by omega
    have d2 : (4 * j + 1) / 4 = j := by omega
    have d3 : (4 * j + 2) / 4 = j := by omega
    have d4 : (4 * j + 3) / 4 = j := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold pointAt
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [h1, d1]
    · unfold pointAt
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [h2, d2]
    · unfold pointAt
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [h3, d3]
    · unfold pointAt
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [h4, d4]
  · intro k _
    unfold fMinus IsNegFrac
    congr

end PairedCharge
