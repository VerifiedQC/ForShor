import Model.Interpreter.Interpreter
import Model.Scanner.ArrayScanner
import Model.Interpreter.Connection

/-!
# Source-to-scanner connection

Connects safe source words to the exact scanner. Proves that a successful safe word inherits the scanner guard (`original_safe_noUnderflow`), that the balanced array scan has the canonical profile (`original_legal_program_childWidth`), and records the C11 facts `original_c11_maps_to_full` and `original_c11_sourceProfile`.
-/

namespace Paper.SourceBridge

/-- A successful safe original word inherits the exact scanner guard from the
row interpreter, at every chosen initial width vector. -/
theorem original_safe_noUnderflow {k : Nat} (weights : Fin k → Nat)
    (ops : TableGeneration.Prog k) (final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true)
    (hsuccess : TableGeneration.run? ops TableGeneration.State.start_state = some final) :
    Scanner.noUnderflow (FullDSL.widthWord (mapToFull ops)) weights :=
  (original_success_noUnderflow weights ops final hsafe hsuccess).1

/-- The repository's balanced array scan has the canonical two-peak profile
when the original interpreter succeeds safely from the identity. -/
theorem original_legal_program_childWidth {k : Nat} (top : Fin k)
    (htop : top.val + 1 = k)
    (ops : TableGeneration.Prog k) (final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true)
    (hsuccess : TableGeneration.run? ops TableGeneration.State.start_state = some final)
    (w : Nat) :
    TableGeneration.RecursiveCost.nextBalancedSignedWidth w ops =
      Planner.childWidth k (sourceProfile top ops) w := by
  rw [ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord,
    ArrayBridge.literalSourceSplit_eq_explicit]
  exact FullDSL.legal_program_childWidth top htop (mapToFull ops) final
    (by rw [runRows_from_start_of_safe ops hsafe]; exact hsuccess) w

theorem original_c11_safe : TableGeneration.safeProg? originalC11Word = true := by
  decide

theorem original_c11_maps_to_full : mapToFull originalC11Word = FullDSL.c11Word := by
  exact mapToFull_mapToOriginal _

theorem original_c11_restores :
    TableGeneration.run? originalC11Word TableGeneration.State.start_state =
      some TableGeneration.State.start_state := by
  have h := runRows_from_start_of_safe originalC11Word original_c11_safe
  rw [original_c11_maps_to_full, FullDSL.c11_rows_restore] at h
  simpa [← source_start_eq_identity] using h.symm

theorem original_c11_returnsToStartCheck :
    TableGeneration.returnsToStartCheck originalC11Word
      TableGeneration.State.start_state = true := by
  exact (returnsToStartCheck_eq_true_iff_model originalC11Word _
    original_c11_safe).mpr (by
      rw [original_c11_maps_to_full, source_start_eq_identity]
      exact FullDSL.c11_rows_restore)

theorem original_c11_sourceProfile :
    sourceProfile (2 : Fin 3) originalC11Word = FullDSL.c11Profile := by
  simp only [sourceProfile, original_c11_maps_to_full]
  congr 1

theorem original_c11_nextBalancedSignedWidth (w : Nat) :
    TableGeneration.RecursiveCost.nextBalancedSignedWidth w originalC11Word =
      w / 3 + 1 + max 6 (5 + w % 3) := by
  rw [original_legal_program_childWidth (2 : Fin 3) (by decide)
    originalC11Word _ original_c11_safe original_c11_restores w,
    original_c11_sourceProfile, FullDSL.c11_childWidth]

end Paper.SourceBridge
