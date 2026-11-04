import Model.Defs

/-!
# The C11 table replay

Replays the eleven-charge C11 word through the scanner model. Proves that the run succeeds and restores the identity rows (`replay_success`, `replay_restores`), covers every target with no duplicate markers, has charge 11 (`replay_charge`), and states the peaks in `replay_peaks`; `complete_c11` bundles these facts.
-/

namespace Paper.C11

theorem rowMatches_iff (row : Row) (p : Target) :
    rowMatches row p = true ↔ ∀ j : Index, row j = targetRow p j := by
  simp [rowMatches, List.all_eq_true]

theorem run_append (first second : List Instruction) (s : State) :
    run (first ++ second) s = (run first s).bind (run second) := by
  induction first generalizing s with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, run]
      cases h : step s instruction with
      | none => simp
      | some next => simpa [h] using ih next

-- A successful run means every add had distinct indices, and every marker
-- matched its exact row and had not appeared earlier.
theorem replay_success : run word initial = some result := by rfl

theorem replay_restores : ∀ i j : Index, result.rows i j = identity i j := by decide

theorem replay_marks :
    result.acquired = [.zero, .infinity, .plusOne, .minusOne, .minusHalf] := by decide

theorem replay_coverage (p : Target) : p ∈ result.acquired := by
  rw [replay_marks]
  cases p <;> simp

theorem replay_no_duplicate_markers : result.acquired.Nodup := by
  rw [replay_marks]
  decide

theorem replay_charge : result.charge = 11 := by decide

theorem replay_scanners :
    result.widths0 0 = 4 ∧ result.widths0 1 = 6 ∧ result.widths0 2 = 5 ∧
    result.widths2 0 = 4 ∧ result.widths2 1 = 6 ∧ result.widths2 2 = 7 := by decide

theorem replay_peaks : result.peak0 = 6 ∧ result.peak2 = 7 := by decide

-- Exact complete-table certificate at k = 3, with profile (a,b) = (6,5).
theorem complete_c11 :
    ∃ s : State,
      run word initial = some s ∧
      (∀ i j : Index, s.rows i j = identity i j) ∧
      s.acquired = [.zero, .infinity, .plusOne, .minusOne, .minusHalf] ∧
      s.charge = 11 ∧
      (s.widths0 0 = 4 ∧ s.widths0 1 = 6 ∧ s.widths0 2 = 5) ∧
      (s.widths2 0 = 4 ∧ s.widths2 1 = 6 ∧ s.widths2 2 = 7) ∧
      s.peak0 = 6 ∧ s.peak2 - 2 = 5 := by
  refine ⟨result, replay_success, replay_restores, replay_marks, replay_charge,
    ?_, ?_, replay_peaks.1, ?_⟩
  · exact ⟨replay_scanners.1, replay_scanners.2.1, replay_scanners.2.2.1⟩
  · exact ⟨replay_scanners.2.2.2.1, replay_scanners.2.2.2.2.1,
      replay_scanners.2.2.2.2.2⟩
  · simp [replay_peaks.2]

end Paper.C11
