import Model.Interpreter.Mass

/-!
# Interpreter correspondence with the source language

Relates the source-level operations to the full-language instructions. Proves the translation is invertible (`toOriginal_toFull`, `toFull_toOriginal`), that guarded row execution agrees with the source run for safe programs (`runRows_eq_run_of_safe`), and exhibits `raw_same_row_counterexample` for the unguarded same-row addition.
-/

namespace Paper.SourceBridge

theorem toOriginal_toFull {k : Nat} (op : TableGeneration.Operations.valid_ops k) :
    toOriginal (toFull op) = op := by
  cases op <;> rfl

theorem toFull_toOriginal {k : Nat} (op : FullDSL.Instruction k) :
    toFull (toOriginal op) = op := by
  cases op <;> rfl

theorem mapToOriginal_mapToFull {k : Nat} (ops : TableGeneration.Prog k) :
    mapToOriginal (mapToFull ops) = ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih => simpa [mapToOriginal, mapToFull, toOriginal_toFull] using ih

theorem mapToFull_mapToOriginal {k : Nat} (ops : List (FullDSL.Instruction k)) :
    mapToFull (mapToOriginal ops) = ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih => simpa [mapToOriginal, mapToFull, toFull_toOriginal] using ih

theorem updateRow_eq_setReg {k : Nat} (rows : FullDSL.Rows k)
    (i : Fin k) (row : Fin k → Int) :
    rows.updateRow i row = TableGeneration.State.setReg rows i row := by
  funext j l
  by_cases h : j = i
  · subst j
    simp [Matrix.updateRow, TableGeneration.State.setReg, Function.update]
  · simp [Matrix.updateRow, TableGeneration.State.setReg, Function.update, h]

theorem shiftR_guard_iff {k : Nat} (rows : FullDSL.Rows k)
    (i : Fin k) (n : Nat) :
    (List.finRange k).all (fun j => decide (rows i j % (2 : Int) ^ n = 0)) = true ↔
      ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0 := by
  simp

/-- The original unguarded addition accepts a row as its own source. The
bridge therefore states step equivalence under the original safety predicate. -/
theorem rowStep_eq_applyOp_of_ok {k : Nat}
    (op : TableGeneration.Operations.valid_ops k) (rows : FullDSL.Rows k)
    (hok : TableGeneration.Prog.OpOK op) :
    FullDSL.rowStep (toFull op) rows = TableGeneration.applyOp? rows op := by
  cases op with
  | shiftL i n =>
      simp [toFull, FullDSL.rowStep, TableGeneration.applyOp?,
        TableGeneration.State.shiftLReg, TableGeneration.Register.shiftL,
        updateRow_eq_setReg]
      rfl
  | shiftR i n =>
      by_cases h : ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0
      · have hg := (shiftR_guard_iff rows i n).mpr h
        simp [toFull, FullDSL.rowStep, h, TableGeneration.applyOp?,
          TableGeneration.State.shiftRReg?, TableGeneration.Register.shiftR?,
          hg, updateRow_eq_setReg]
      · have hg : ¬(List.finRange k).all
            (fun j => decide (rows i j % (2 : Int) ^ n = 0)) = true :=
          mt (shiftR_guard_iff rows i n).mp h
        simp [toFull, FullDSL.rowStep, h, TableGeneration.applyOp?,
          TableGeneration.State.shiftRReg?, TableGeneration.Register.shiftR?, hg]
  | negate i =>
      simp [toFull, FullDSL.rowStep, TableGeneration.applyOp?,
        TableGeneration.State.negateReg, TableGeneration.Register.negate,
        updateRow_eq_setReg]
      rfl
  | addScaled d s neg n =>
      simp only [TableGeneration.Prog.OpOK] at hok
      simp [toFull, FullDSL.rowStep, hok, TableGeneration.applyOp?,
        TableGeneration.State.addScaledReg, TableGeneration.Register.addScaled,
        updateRow_eq_setReg, mul_assoc, mul_comm, mul_left_comm]
  | phaseProduct i =>
      rfl

theorem raw_same_row_counterexample :
    FullDSL.rowStep
        (toFull (TableGeneration.Operations.valid_ops.addScaled (0 : Fin 1) 0 false 0))
        (TableGeneration.State.start_state (k := 1)) ≠
      TableGeneration.applyOp? TableGeneration.State.start_state
        (.addScaled (0 : Fin 1) 0 false 0) := by
  simp [toFull, FullDSL.rowStep, TableGeneration.applyOp?]

theorem opOK_iff_bool {k : Nat} (op : TableGeneration.Operations.valid_ops k) :
    TableGeneration.Prog.OpOK? op = true ↔ TableGeneration.Prog.OpOK op := by
  cases op <;> simp [TableGeneration.Prog.OpOK?, TableGeneration.Prog.OpOK]

theorem safeProg_iff {k : Nat} (ops : TableGeneration.Prog k) :
    TableGeneration.safeProg? ops = true ↔
      ∀ op ∈ ops, TableGeneration.Prog.OpOK op := by
  induction ops with
  | nil => simp [TableGeneration.safeProg?, TableGeneration.Prog.wellFormed?]
  | cons op rest ih =>
      simp only [TableGeneration.safeProg?, TableGeneration.Prog.wellFormed?,
        Bool.and_eq_true, opOK_iff_bool]
      have ih' : TableGeneration.Prog.wellFormed? rest = true ↔
          ∀ a ∈ rest, TableGeneration.Prog.OpOK a := ih
      simp [ih', List.mem_cons, or_imp, forall_and]

theorem runRows_eq_run_of_safe {k : Nat} (ops : TableGeneration.Prog k)
    (rows : FullDSL.Rows k) (hsafe : TableGeneration.safeProg? ops = true) :
    FullDSL.runRows (mapToFull ops) rows = TableGeneration.run? ops rows := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op rest ih =>
      have h1 : TableGeneration.Prog.OpOK op := (safeProg_iff (op :: rest)).mp hsafe op (by simp)
      have h2 : TableGeneration.safeProg? rest = true := by
        exact (safeProg_iff rest).mpr (fun a ha =>
          (safeProg_iff (op :: rest)).mp hsafe a (by simp [ha]))
      simp only [mapToFull, List.map_cons, FullDSL.runRows, TableGeneration.run?]
      rw [rowStep_eq_applyOp_of_ok op rows h1]
      cases happly : TableGeneration.applyOp? rows op with
      | none => simp
      | some next =>
          change FullDSL.runRows (mapToFull rest) next = TableGeneration.run? rest next
          exact ih next h2

theorem source_start_eq_identity (k : Nat) :
    TableGeneration.State.start_state (k := k) = FullDSL.identity k := by
  funext i j
  simp [TableGeneration.State.start_state, FullDSL.identity, Matrix.one_apply,
    eq_comm]

theorem runRows_from_start_of_safe {k : Nat} (ops : TableGeneration.Prog k)
    (hsafe : TableGeneration.safeProg? ops = true) :
    FullDSL.runRows (mapToFull ops) (FullDSL.identity k) =
      TableGeneration.run? ops TableGeneration.State.start_state := by
  rw [← source_start_eq_identity]
  exact runRows_eq_run_of_safe ops _ hsafe

theorem statesEqual_eq_true_iff {k : Nat} (left right : TableGeneration.State k) :
    TableGeneration.statesEqual left right = true ↔ left = right := by
  constructor
  · intro h
    have hentries : ∀ i j : Fin k, left i j = right i j := by
      simpa [TableGeneration.statesEqual] using h
    funext i j
    exact hentries i j
  · intro h
    subst right
    simp [TableGeneration.statesEqual]

theorem returnsToStartCheck_eq_true_iff_model {k : Nat}
    (ops : TableGeneration.Prog k) (rows : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true) :
    TableGeneration.returnsToStartCheck ops rows = true ↔
      FullDSL.runRows (mapToFull ops) rows = some rows := by
  rw [runRows_eq_run_of_safe ops rows hsafe]
  unfold TableGeneration.returnsToStartCheck
  cases h : TableGeneration.run? ops rows with
  | none => simp [h]
  | some next => simp [h, statesEqual_eq_true_iff]

theorem original_success_noUnderflow {k : Nat} (weights : Fin k → Nat)
    (ops : TableGeneration.Prog k) (final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? ops = true)
    (hsuccess : TableGeneration.run? ops TableGeneration.State.start_state = some final) :
    Paper.Scanner.noUnderflow (FullDSL.widthWord (mapToFull ops)) weights ∧
      Paper.RowMass.Bounded weights final
        (Paper.Scanner.runWidths (FullDSL.widthWord (mapToFull ops)) weights) := by
  apply Paper.RowMass.runRows_mass_noUnderflow
  rw [runRows_from_start_of_safe ops hsafe]
  exact hsuccess

end Paper.SourceBridge
