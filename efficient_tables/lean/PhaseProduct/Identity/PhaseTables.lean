import PhaseProduct.Identity.PhaseIdentity
import Model.Interpreter.ValueTrace

/-!
# Phase identities for the C11 and PTP2 tables

Connects the concrete C11 and PTP2 source words to their integer traces
(`c11_observation_eq`, `ptp2_observation_eq`, `ptp2_valueTrace`). It then
derives the phase identities from those actual traces
(`c11_trace_phase_product`, `ptp2_trace_phase_triple_product`).
-/

namespace Paper.PhaseIdentity

theorem c11_observation_eq (x : ValueSemantics.Values 3) (l : Fin 5) :
    ((observations SourceBridge.c11Points x).getD l.val 0 : ℚ) =
      linearForm (c11Rows l) (fun j => (x j : ℚ)) := by
  fin_cases l <;>
    simp [observations, SourceBridge.c11Points, TableGeneration.expectedRow,
      ValueSemantics.evalRow, linearForm, c11Rows, Fin.sum_univ_succ] <;>
    push_cast <;> ring

theorem ptp2_observation_eq (x : ValueSemantics.Values 2) (l : Fin 4) :
    ((observations ptp2Points x).getD l.val 0 : ℚ) =
      linearForm (ptp2Rows l) (fun j => (x j : ℚ)) := by
  fin_cases l <;>
    simp [observations, ptp2Points, TableGeneration.expectedRow,
      ValueSemantics.evalRow, linearForm, ptp2Rows, Fin.sum_univ_succ] <;>
    push_cast <;> ring

theorem ptp2_source_contract :
    TableGeneration.ProgConsumesPtsSafe (by decide : 2 > 0)
      TableGeneration.State.start_state ptp2Word ptp2Points := by
  constructor <;> decide

theorem ptp2_valueTrace (x : ValueSemantics.Values 2) :
    ValueSemantics.valueTrace (SourceBridge.mapToFull ptp2Word) x =
      some (x, observations ptp2Points x) := by
  exact ValueSemantics.source_contract_valueTrace (by decide : 2 > 0)
    ptp2Word ptp2Points x ptp2_source_contract

/-- The actual integer traces of the accepted C11 source word carry the PP
decomposition and restore both inputs, for every rational radix. -/
theorem c11_trace_phase_product (b : ℚ) (x z : ValueSemantics.Values 3) :
    ∃ xs zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull SourceBridge.originalC11Word) x = some (x, xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull SourceBridge.originalC11Word) z = some (z, zs) ∧
      xs.length = 5 ∧ zs.length = 5 ∧
      (∑ l : Fin 5, c11Weights b l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        ((x 0 : ℚ) + b*x 1 + b^2*x 2) * ((z 0 : ℚ) + b*z 1 + b^2*z 2) := by
  refine ⟨observations SourceBridge.c11Points x, observations SourceBridge.c11Points z,
    ValueSemantics.original_c11_valueTrace x, ValueSemantics.original_c11_valueTrace z,
    by simp [observations, SourceBridge.c11Points],
    by simp [observations, SourceBridge.c11Points], ?_⟩
  simp_rw [c11_observation_eq]
  exact c11_phase_product_identity b (fun j => (x j : ℚ)) (fun j => (z j : ℚ))

/-- The accepted two-limb source word supplies a PTP decomposition on its
four concrete marker values, restoring all three integer operands. -/
theorem ptp2_trace_phase_triple_product (b : ℚ) (x y z : ValueSemantics.Values 2) :
    ∃ xs ys zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull ptp2Word) x = some (x, xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ptp2Word) y = some (y, ys) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ptp2Word) z = some (z, zs) ∧
      xs.length = 4 ∧ ys.length = 4 ∧ zs.length = 4 ∧
      (∑ l : Fin 4, ptp2Weights b l * (xs.getD l.val 0 : ℚ) *
        (ys.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        ((x 0 : ℚ) + b*x 1) * ((y 0 : ℚ) + b*y 1) * ((z 0 : ℚ) + b*z 1) := by
  refine ⟨observations ptp2Points x, observations ptp2Points y, observations ptp2Points z,
    ptp2_valueTrace x, ptp2_valueTrace y, ptp2_valueTrace z,
    by simp [observations, ptp2Points], by simp [observations, ptp2Points],
    by simp [observations, ptp2Points], ?_⟩
  simp_rw [ptp2_observation_eq]
  exact ptp2_phase_triple_product_identity b (fun j => (x j : ℚ))
    (fun j => (y j : ℚ)) (fun j => (z j : ℚ))

end Paper.PhaseIdentity
