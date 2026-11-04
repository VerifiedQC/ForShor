import Model.Interpreter.Values
import Model.Interpreter.Consumption

/-!
# Value traces of marker executions

Relates symbolic marker traces to concrete integer value traces. Proves `markerTrace_refines_valueTrace`, that an accepted protected source contract records the advertised values (`source_contract_valueTrace`), and the explicit C11 instance `original_c11_valueTrace`.
-/

namespace Paper.ValueSemantics

/-- A successful symbolic marker trace has the corresponding concrete integer
trace for every initial value vector. This is intentionally one-way: symbolic
coefficient divisibility implies scalar divisibility, not conversely. -/
theorem markerTrace_refines_valueTrace {k : Nat}
    (word : List (FullDSL.Instruction k)) (rows : FullDSL.Rows k)
    (x : Values k) (final : FullDSL.Rows k)
    (marks : List (Fin k → Int))
    (h : SourceBridge.markerTrace word rows = some (final, marks)) :
    valueTrace word (evalRows rows x) =
      some (evalRows final x, marks.map (fun r => evalRow r x)) := by
  induction word generalizing rows final marks with
  | nil =>
      simp only [SourceBridge.markerTrace, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | cons op rest ih =>
      cases op with
      | phaseProduct i =>
          cases ht : SourceBridge.markerTrace rest rows with
          | none => simp [SourceBridge.markerTrace, ht] at h
          | some pair =>
              rcases pair with ⟨mid, ms⟩
              simp [SourceBridge.markerTrace, ht] at h
              rcases h with ⟨rfl, rfl⟩
              have hv := ih rows mid ms ht
              simpa [valueTrace, hv, evalRows]
      | shiftL i n =>
          cases hs : FullDSL.rowStep (.shiftL i n) rows with
          | none => simp [SourceBridge.markerTrace, hs] at h
          | some next =>
              have ht : SourceBridge.markerTrace rest next = some (final, marks) := by
                simpa [SourceBridge.markerTrace, hs] using h
              have hv := ih next final marks ht
              have step := rowStep_refines_values (.shiftL i n) rows next x hs
              simpa [valueTrace, step] using hv
      | shiftR i n =>
          cases hs : FullDSL.rowStep (.shiftR i n) rows with
          | none => simp [SourceBridge.markerTrace, hs] at h
          | some next =>
              have ht : SourceBridge.markerTrace rest next = some (final, marks) := by
                simpa [SourceBridge.markerTrace, hs] using h
              have hv := ih next final marks ht
              have step := rowStep_refines_values (.shiftR i n) rows next x hs
              simpa [valueTrace, step] using hv
      | negate i =>
          cases hs : FullDSL.rowStep (.negate i) rows with
          | none => simp [SourceBridge.markerTrace, hs] at h
          | some next =>
              have ht : SourceBridge.markerTrace rest next = some (final, marks) := by
                simpa [SourceBridge.markerTrace, hs] using h
              have hv := ih next final marks ht
              have step := rowStep_refines_values (.negate i) rows next x hs
              simpa [valueTrace, step] using hv
      | addScaled dst src negSrc shift =>
          cases hs : FullDSL.rowStep (.addScaled dst src negSrc shift) rows with
          | none => simp [SourceBridge.markerTrace, hs] at h
          | some next =>
              have ht : SourceBridge.markerTrace rest next = some (final, marks) := by
                simpa [SourceBridge.markerTrace, hs] using h
              have hv := ih next final marks ht
              have step := rowStep_refines_values
                (.addScaled dst src negSrc shift) rows next x hs
              simpa [valueTrace, step] using hv

/-- Any accepted protected source contract records the advertised source
points on concrete integers and restores the input vector. -/
theorem source_contract_valueTrace {k : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point) (x : Values k)
    (h : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops pts) :
    valueTrace (SourceBridge.mapToFull ops) x =
      some (x, pts.map (fun p => evalRow (TableGeneration.expectedRow p) x)) := by
  have ht := ((SourceBridge.source_contract_iff_trace hk
    TableGeneration.State.start_state ops pts).mp h).2
  have hv := markerTrace_refines_valueTrace (SourceBridge.mapToFull ops)
    TableGeneration.State.start_state x TableGeneration.State.start_state
    (pts.map TableGeneration.expectedRow) ht
  have hs : evalRows (TableGeneration.State.start_state (k := k)) x = x := by
    rw [SourceBridge.source_start_eq_identity]
    exact evalRows_identity x
  simpa [hs, List.map_map] using hv

/-- The protected eleven-charge word has an exact scalar marker trace for
every three-register integer input. -/
theorem original_c11_valueTrace (x : Values 3) :
    valueTrace (SourceBridge.mapToFull SourceBridge.originalC11Word) x =
      some (x, SourceBridge.c11Points.map
        (fun p => evalRow (TableGeneration.expectedRow p) x)) := by
  exact source_contract_valueTrace (by decide : 3 > 0)
    SourceBridge.originalC11Word SourceBridge.c11Points x
    SourceBridge.original_c11_contract

theorem original_c11_valueTrace_explicit (x : Values 3) :
    valueTrace (SourceBridge.mapToFull SourceBridge.originalC11Word) x =
      some (x, [x 0, x 2, x 0 + x 1 + x 2,
        x 0 - x 1 + x 2, 4 * x 0 - 2 * x 1 + x 2]) := by
  rw [original_c11_valueTrace]
  simp [SourceBridge.c11Points, TableGeneration.expectedRow, evalRow,
    Fin.sum_univ_succ]
  constructor
  · ring
  constructor <;> ring

end Paper.ValueSemantics
