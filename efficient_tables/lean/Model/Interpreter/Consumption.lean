import Model.Interpreter.Interpreter
import Model.Interpreter.SourceConnection

/-!
# Marker-trace characterization of point consumption

Characterizes when a source word consumes its target points in terms of the marker trace of the full-language model. Key results are `source_consumes_iff_markerTrace` and `source_contract_iff_trace`, which express the protected table contract through the trace, plus `original_c11_consumes_points` for the C11 word.
-/

namespace Paper.SourceBridge

theorem regEqExpected_eq_true_iff {k : Nat}
    (row : TableGeneration.Register k) (pt : TableGeneration.Operations.Point) :
    TableGeneration.regEqExpected row pt = true ↔
      row = TableGeneration.expectedRow pt := by
  constructor
  · intro h
    have hall : ∀ j : Fin k, row j = TableGeneration.expectedRow pt j := by
      simpa [TableGeneration.regEqExpected] using h
    funext j
    exact hall j
  · intro h
    subst row
    simp [TableGeneration.regEqExpected]

theorem matchesAt_eq_true_iff {k : Nat} (hk : k > 0)
    (rows : TableGeneration.State k) (i : Fin k)
    (pt : TableGeneration.Operations.Point) :
    TableGeneration.matchesAt_pointRow_state hk rows i pt = true ↔
      rows i = TableGeneration.expectedRow pt := by
  exact regEqExpected_eq_true_iff (rows i) pt

/-- The trace's final row state is exactly the ordinary model run, whether
the run succeeds or fails. -/
theorem markerTrace_fst {k : Nat} (word : List (FullDSL.Instruction k))
    (rows : FullDSL.Rows k) :
    (markerTrace word rows).map Prod.fst = FullDSL.runRows word rows := by
  induction word generalizing rows with
  | nil => rfl
  | cons op rest ih =>
      cases op with
      | phaseProduct i =>
          simp only [markerTrace, FullDSL.runRows, FullDSL.rowStep,
            Option.bind_some]
          cases ht : markerTrace rest rows with
          | none =>
              have hr : FullDSL.runRows rest rows = none := by
                rw [← ih]
                simp [ht]
              simp [ht, hr]
          | some pair =>
              obtain ⟨final, marks⟩ := pair
              have hr : FullDSL.runRows rest rows = some final := by
                rw [← ih]
                simp [ht]
              simp [ht, hr]
      | shiftL i n =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.shiftL i n) rows with
          | none => simp [hs]
          | some next => simpa [hs] using ih next
      | shiftR i n =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.shiftR i n) rows with
          | none => simp [hs]
          | some next => simpa [hs] using ih next
      | negate i =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.negate i) rows with
          | none => simp [hs]
          | some next => simpa [hs] using ih next
      | addScaled d s neg n =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.addScaled d s neg n) rows with
          | none => simp [hs]
          | some next => simpa [hs] using ih next

theorem markerTrace_phase_iff {k : Nat} (rest : List (FullDSL.Instruction k))
    (rows : FullDSL.Rows k) (i : Fin k) (head : Fin k → Int)
    (tail : List (Fin k → Int)) :
    (∃ final, markerTrace (.phaseProduct i :: rest) rows =
        some (final, head :: tail)) ↔
      rows i = head ∧ ∃ final, markerTrace rest rows = some (final, tail) := by
  constructor
  · rintro ⟨final, h⟩
    cases ht : markerTrace rest rows with
    | none => simp [markerTrace, ht] at h
    | some pair =>
        obtain ⟨next, marks⟩ := pair
        simp [markerTrace, ht] at h
        obtain ⟨hfinal, hrow, htail⟩ := h
        exact ⟨hrow, next, by simpa [ht, hfinal, htail]⟩
  · rintro ⟨hrow, final, hrest⟩
    exact ⟨final, by simp [markerTrace, hrest, hrow]⟩

theorem markerTrace_phase_ne_nil {k : Nat}
    (rest : List (FullDSL.Instruction k)) (rows : FullDSL.Rows k)
    (i : Fin k) (final : FullDSL.Rows k) :
    markerTrace (.phaseProduct i :: rest) rows ≠ some (final, []) := by
  intro h
  cases ht : markerTrace rest rows with
  | none => simp [markerTrace, ht] at h
  | some pair =>
      obtain ⟨next, marks⟩ := pair
      simp [markerTrace, ht] at h

theorem source_consumes_iff_markerTrace {k : Nat} (hk : k > 0)
    (rows : TableGeneration.State k) (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point)
    (hsafe : TableGeneration.safeProg? ops = true) :
    TableGeneration.progConsumesPts? hk rows ops pts = true ↔
      ∃ final, markerTrace (mapToFull ops) rows =
        some (final, pts.map TableGeneration.expectedRow) := by
  induction ops generalizing rows pts with
  | nil =>
      cases pts <;> simp [TableGeneration.progConsumesPts?, markerTrace,
        mapToFull]
  | cons op rest ih =>
      have hok : TableGeneration.Prog.OpOK op :=
        (safeProg_iff (op :: rest)).mp hsafe op (by simp)
      have hrest : TableGeneration.safeProg? rest = true := by
        exact (safeProg_iff rest).mpr (fun a ha =>
          (safeProg_iff (op :: rest)).mp hsafe a (by simp [ha]))
      cases op with
      | phaseProduct i =>
          cases pts with
          | nil =>
              constructor
              · intro h
                simp [TableGeneration.progConsumesPts?] at h
              · rintro ⟨final, h⟩
                exact False.elim ((markerTrace_phase_ne_nil (mapToFull rest) rows i final)
                  (by simpa [mapToFull, toFull] using h))
          | cons pt more =>
              simp only [TableGeneration.progConsumesPts?, mapToFull,
                List.map_cons, toFull]
              rw [Bool.and_eq_true, matchesAt_eq_true_iff,
                ih rows more hrest, markerTrace_phase_iff]
              simp [mapToFull]
      | shiftL i n =>
          simp only [TableGeneration.progConsumesPts?, mapToFull, List.map_cons,
            toFull, markerTrace]
          rw [← rowStep_eq_applyOp_of_ok (.shiftL i n) rows hok]
          simp only [toFull]
          cases hstep : FullDSL.rowStep (.shiftL i n) rows with
          | none => simp [hstep]
          | some next => simpa [hstep, mapToFull] using ih next pts hrest
      | shiftR i n =>
          simp only [TableGeneration.progConsumesPts?, mapToFull, List.map_cons,
            toFull, markerTrace]
          rw [← rowStep_eq_applyOp_of_ok (.shiftR i n) rows hok]
          simp only [toFull]
          cases hstep : FullDSL.rowStep (.shiftR i n) rows with
          | none => simp [hstep]
          | some next => simpa [hstep, mapToFull] using ih next pts hrest
      | negate i =>
          simp only [TableGeneration.progConsumesPts?, mapToFull, List.map_cons,
            toFull, markerTrace]
          rw [← rowStep_eq_applyOp_of_ok (.negate i) rows hok]
          simp only [toFull]
          cases hstep : FullDSL.rowStep (.negate i) rows with
          | none => simp [hstep]
          | some next => simpa [hstep, mapToFull] using ih next pts hrest
      | addScaled d s neg n =>
          simp only [TableGeneration.progConsumesPts?, mapToFull, List.map_cons,
            toFull, markerTrace]
          rw [← rowStep_eq_applyOp_of_ok (.addScaled d s neg n) rows hok]
          simp only [toFull]
          cases hstep : FullDSL.rowStep (.addScaled d s neg n) rows with
          | none => simp [hstep]
          | some next => simpa [hstep, mapToFull] using ih next pts hrest

theorem source_consumes_false_of_trace_none {k : Nat} (hk : k > 0)
    (rows : TableGeneration.State k) (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point)
    (hsafe : TableGeneration.safeProg? ops = true)
    (htrace : markerTrace (mapToFull ops) rows = none) :
    TableGeneration.progConsumesPts? hk rows ops pts = false := by
  cases hc : TableGeneration.progConsumesPts? hk rows ops pts with
  | false => rfl
  | true =>
      obtain ⟨final, hf⟩ :=
        (source_consumes_iff_markerTrace hk rows ops pts hsafe).mp hc
      simp [htrace] at hf

theorem source_consumes_false_of_marker_count_mismatch {k : Nat} (hk : k > 0)
    (rows : TableGeneration.State k) (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point)
    (hsafe : TableGeneration.safeProg? ops = true)
    (final : FullDSL.Rows k) (marks : List (Fin k → Int))
    (htrace : markerTrace (mapToFull ops) rows = some (final, marks))
    (hlen : marks.length ≠ pts.length) :
    TableGeneration.progConsumesPts? hk rows ops pts = false := by
  cases hc : TableGeneration.progConsumesPts? hk rows ops pts with
  | false => rfl
  | true =>
      obtain ⟨other, ht⟩ :=
        (source_consumes_iff_markerTrace hk rows ops pts hsafe).mp hc
      have hm : marks = pts.map TableGeneration.expectedRow :=
        congrArg Prod.snd (Option.some.inj (htrace.symm.trans ht))
      exact False.elim (hlen (by simpa [hm]))

/-- All three clauses of the protected table contract have a precise trace
form: the word is safe, consumes exactly the advertised target rows, and
returns its arithmetic state to its start. -/
theorem source_contract_iff_trace {k : Nat} (hk : k > 0)
    (rows : TableGeneration.State k) (ops : TableGeneration.Prog k)
    (pts : List TableGeneration.Operations.Point) :
    TableGeneration.ProgConsumesPtsSafe hk rows ops pts ↔
      TableGeneration.safeProg? ops = true ∧
        markerTrace (mapToFull ops) rows =
          some (rows, pts.map TableGeneration.expectedRow) := by
  constructor
  · intro h
    refine ⟨h.safe_add, ?_⟩
    obtain ⟨final, ht⟩ :=
      (source_consumes_iff_markerTrace hk rows ops pts h.safe_add).mp h.consumes
    have hr : FullDSL.runRows (mapToFull ops) rows = some rows :=
      (returnsToStartCheck_eq_true_iff_model ops rows h.safe_add).mp h.returns_start
    have hr' : FullDSL.runRows (mapToFull ops) rows = some final := by
      rw [← markerTrace_fst]
      simp [ht]
    have heq : final = rows := Option.some.inj (hr'.symm.trans hr)
    simpa [heq] using ht
  · rintro ⟨hsafe, ht⟩
    have hc : TableGeneration.progConsumesPts? hk rows ops pts = true :=
      (source_consumes_iff_markerTrace hk rows ops pts hsafe).mpr ⟨rows, ht⟩
    have hr : FullDSL.runRows (mapToFull ops) rows = some rows := by
      rw [← markerTrace_fst]
      simp [ht]
    exact TableGeneration.progConsumesPtsSafe_of_checks hc hsafe
      ((returnsToStartCheck_eq_true_iff_model ops rows hsafe).mpr hr)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem original_c11_consumes_points :
    TableGeneration.progConsumesPts? (by decide : 3 > 0)
      TableGeneration.State.start_state originalC11Word c11Points = true := by
  decide

theorem original_c11_contract :
    TableGeneration.ProgConsumesPtsSafe (by decide : 3 > 0)
      TableGeneration.State.start_state originalC11Word c11Points := by
  exact TableGeneration.progConsumesPtsSafe_of_checks
    original_c11_consumes_points original_c11_safe original_c11_returnsToStartCheck

theorem original_c11_markerTrace :
    markerTrace (mapToFull originalC11Word) TableGeneration.State.start_state =
      some (TableGeneration.State.start_state,
        c11Points.map TableGeneration.expectedRow) :=
  ((source_contract_iff_trace (by decide : 3 > 0)
    TableGeneration.State.start_state originalC11Word c11Points).mp original_c11_contract).2

end Paper.SourceBridge
