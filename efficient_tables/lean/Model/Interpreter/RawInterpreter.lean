import Model.Interpreter.Interpreter

/-!
# Raw source interpreter

Compares the full-language row execution with the raw (unguarded) source execution. Proves `runRows_eq_run` as a total optional-result equality without a program-safety premise, together with `returnsToStartCheck_eq_true_iff_raw`, and shows `same_row_subtraction_erases` (raw execution can erase a register).
-/

namespace Paper.RawInterpreter

theorem rowStep_eq_applyOp {k : Nat}
    (op : TableGeneration.Operations.valid_ops k) (rows : FullDSL.Rows k) :
    rowStep (SourceBridge.toFull op) rows = TableGeneration.applyOp? rows op := by
  cases op with
  | shiftL i n =>
      simp [SourceBridge.toFull, rowStep, TableGeneration.applyOp?,
        TableGeneration.State.shiftLReg, TableGeneration.Register.shiftL,
        SourceBridge.updateRow_eq_setReg]
      rfl
  | shiftR i n =>
      by_cases h : ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0
      · have hg := (SourceBridge.shiftR_guard_iff rows i n).mpr h
        simp [SourceBridge.toFull, rowStep, h, TableGeneration.applyOp?,
          TableGeneration.State.shiftRReg?, TableGeneration.Register.shiftR?,
          hg, SourceBridge.updateRow_eq_setReg]
      · have hg : ¬(List.finRange k).all
            (fun j => decide (rows i j % (2 : Int) ^ n = 0)) = true :=
          mt (SourceBridge.shiftR_guard_iff rows i n).mp h
        simp [SourceBridge.toFull, rowStep, h, TableGeneration.applyOp?,
          TableGeneration.State.shiftRReg?, TableGeneration.Register.shiftR?, hg]
  | negate i =>
      simp [SourceBridge.toFull, rowStep, TableGeneration.applyOp?,
        TableGeneration.State.negateReg, TableGeneration.Register.negate,
        SourceBridge.updateRow_eq_setReg]
      rfl
  | addScaled d s neg n =>
      simp [SourceBridge.toFull, rowStep, TableGeneration.applyOp?,
        TableGeneration.State.addScaledReg, TableGeneration.Register.addScaled,
        SourceBridge.updateRow_eq_setReg, mul_assoc, mul_comm, mul_left_comm]
  | phaseProduct i => rfl

/-- Total optional-result equality, without a program-safety premise. -/
theorem runRows_eq_run {k : Nat} (ops : TableGeneration.Prog k)
    (rows : FullDSL.Rows k) :
    runRows (SourceBridge.mapToFull ops) rows = TableGeneration.run? ops rows := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op rest ih =>
      simp only [SourceBridge.mapToFull, List.map_cons, runRows, TableGeneration.run?]
      rw [rowStep_eq_applyOp]
      cases happly : TableGeneration.applyOp? rows op with
      | none => simp
      | some next =>
          change runRows (SourceBridge.mapToFull rest) next =
            TableGeneration.run? rest next
          exact ih next

theorem rowStep_eq_guarded_of_ok {k : Nat}
    (op : TableGeneration.Operations.valid_ops k) (rows : FullDSL.Rows k)
    (hok : TableGeneration.Prog.OpOK op) :
    rowStep (SourceBridge.toFull op) rows =
      FullDSL.rowStep (SourceBridge.toFull op) rows := by
  rw [rowStep_eq_applyOp, SourceBridge.rowStep_eq_applyOp_of_ok op rows hok]

theorem runRows_eq_guarded_of_safe {k : Nat} (ops : TableGeneration.Prog k)
    (rows : FullDSL.Rows k) (hsafe : TableGeneration.safeProg? ops = true) :
    runRows (SourceBridge.mapToFull ops) rows =
      FullDSL.runRows (SourceBridge.mapToFull ops) rows := by
  rw [runRows_eq_run, SourceBridge.runRows_eq_run_of_safe ops rows hsafe]

theorem returnsToStartCheck_eq_true_iff_raw {k : Nat}
    (ops : TableGeneration.Prog k) (rows : TableGeneration.State k) :
    TableGeneration.returnsToStartCheck ops rows = true ↔
      runRows (SourceBridge.mapToFull ops) rows = some rows := by
  rw [runRows_eq_run]
  unfold TableGeneration.returnsToStartCheck
  cases h : TableGeneration.run? ops rows with
  | none => simp [h]
  | some next => simp [h, SourceBridge.statesEqual_eq_true_iff]

/-- Raw source execution can erase a register; no invertibility follows
without the guarded language's safety condition. -/
theorem same_row_subtraction_erases :
    rowStep (.addScaled (0 : Fin 1) 0 true 0) (FullDSL.identity 1) =
      some (0 : FullDSL.Rows 1) := by
  simp only [rowStep]
  congr 1
  ext i j
  fin_cases i
  fin_cases j
  simp [FullDSL.identity]

end Paper.RawInterpreter

