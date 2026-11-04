import Model.Interpreter.ValueTrace

/-!
# Basis reflection of symbolic success

Relates symbolic row execution to the scalar interpreter run on basis inputs. Proves that one-step symbolic success is detected on all basis vectors (`rowStep_success_iff_all_basis`) and that marker-trace success is equivalent to concrete success on every basis (`markerTrace_success_iff_all_basis_valueTrace`); `one_input_does_not_detect_shiftR` shows a single scalar input can miss a failure.
-/

namespace Paper.BasisReflection

open Paper.ValueSemantics

theorem evalRow_basis {k : Nat} (row : Fin k → Int) (j : Fin k) :
    evalRow row (fun i => if i = j then (1 : Int) else 0) = row j := by
  simp [evalRow]

theorem evalRows_basis {k : Nat} (rows : Paper.FullDSL.Rows k)
    (j i : Fin k) :
    evalRows rows (fun a => if a = j then (1 : Int) else 0) i = rows i j := by
  exact evalRow_basis (rows i) j

/-- Symbolic one-step success is detected by the scalar interpreter on all
standard-basis inputs. A single arbitrary input does not suffice for SHR. -/
theorem rowStep_success_iff_all_basis {k : Nat}
    (op : Paper.FullDSL.Instruction k) (rows : Paper.FullDSL.Rows k) :
    (∃ next, Paper.FullDSL.rowStep op rows = some next) ↔
      ∀ j : Fin k, ∃ next,
        valueStep op (evalRows rows
          (fun i => if i = j then (1 : Int) else 0)) = some next := by
  constructor
  · rintro ⟨next, hstep⟩ j
    exact ⟨evalRows next (fun i => if i = j then (1 : Int) else 0),
      rowStep_refines_values op rows next _ hstep⟩
  · intro hall
    cases op with
    | shiftL i n => exact ⟨_, rfl⟩
    | shiftR i n =>
        have hd : ∀ j : Fin k, rows i j % (2 : Int) ^ n = 0 := by
          intro j
          by_contra hbad
          obtain ⟨next, hstep⟩ := hall j
          have hbad' :
              (evalRows rows (fun a => if a = j then (1 : Int) else 0)) i %
                  (2 : Int) ^ n ≠ 0 := by
            simpa only [evalRows_basis] using hbad
          simp [valueStep, hbad'] at hstep
        exact ⟨rows.updateRow i (fun j => rows i j / (2 : Int) ^ n),
          by simp [Paper.FullDSL.rowStep, hd]⟩
    | negate i => exact ⟨_, rfl⟩
    | addScaled dst src negSrc shift =>
        by_cases hsame : dst = src
        · obtain ⟨next, hstep⟩ := hall dst
          simp [valueStep, hsame] at hstep
        · exact ⟨rows.updateRow dst (fun j => rows dst j +
            ((if negSrc then -1 else 1) * (2 : Int) ^ shift) * rows src j),
            by simp [Paper.FullDSL.rowStep, hsame]⟩
    | phaseProduct i => exact ⟨_, rfl⟩

theorem valueTrace_cons_success {k : Nat}
    (op : Paper.FullDSL.Instruction k) (rest : List (Paper.FullDSL.Instruction k))
    (v : Values k) (out : Values k) (marks : List Int)
    (h : valueTrace (op :: rest) v = some (out, marks)) :
    ∃ mid, valueStep op v = some mid ∧
      ∃ tailOut tailMarks, valueTrace rest mid = some (tailOut, tailMarks) := by
  cases op with
  | phaseProduct i =>
      cases ht : valueTrace rest v with
      | none => simp [valueTrace, ht] at h
      | some pair =>
          rcases pair with ⟨tailOut, tailMarks⟩
          exact ⟨v, rfl, tailOut, tailMarks, ht⟩
  | shiftL i n =>
      cases hs : valueStep (.shiftL i n) v with
      | none => simp [valueTrace, hs] at h
      | some mid =>
          cases ht : valueTrace rest mid with
          | none => simp [valueTrace, hs, ht] at h
          | some pair =>
              rcases pair with ⟨tailOut, tailMarks⟩
              exact ⟨mid, rfl, tailOut, tailMarks, ht⟩
  | shiftR i n =>
      cases hs : valueStep (.shiftR i n) v with
      | none => simp [valueTrace, hs] at h
      | some mid =>
          cases ht : valueTrace rest mid with
          | none => simp [valueTrace, hs, ht] at h
          | some pair =>
              rcases pair with ⟨tailOut, tailMarks⟩
              exact ⟨mid, rfl, tailOut, tailMarks, ht⟩
  | negate i =>
      cases hs : valueStep (.negate i) v with
      | none => simp [valueTrace, hs] at h
      | some mid =>
          cases ht : valueTrace rest mid with
          | none => simp [valueTrace, hs, ht] at h
          | some pair =>
              rcases pair with ⟨tailOut, tailMarks⟩
              exact ⟨mid, rfl, tailOut, tailMarks, ht⟩
  | addScaled dst src negSrc shift =>
      cases hs : valueStep (.addScaled dst src negSrc shift) v with
      | none => simp [valueTrace, hs] at h
      | some mid =>
          cases ht : valueTrace rest mid with
          | none => simp [valueTrace, hs, ht] at h
          | some pair =>
              rcases pair with ⟨tailOut, tailMarks⟩
              exact ⟨mid, rfl, tailOut, tailMarks, ht⟩

/-- Symbolic marker-trace success is equivalent to concrete success on every
standard basis input, including the empty basis at `k = 0`. -/
theorem markerTrace_success_iff_all_basis_valueTrace {k : Nat}
    (word : List (Paper.FullDSL.Instruction k)) (rows : Paper.FullDSL.Rows k) :
    (∃ final marks, Paper.SourceBridge.markerTrace word rows = some (final, marks)) ↔
      ∀ j : Fin k, ∃ final marks,
        valueTrace word (evalRows rows
          (fun i => if i = j then (1 : Int) else 0)) = some (final, marks) := by
  induction word generalizing rows with
  | nil =>
      constructor
      · intro _ j
        exact ⟨_, _, rfl⟩
      · intro _
        exact ⟨rows, [], rfl⟩
  | cons op rest ih =>
      constructor
      · rintro ⟨final, marks, htrace⟩ j
        exact ⟨_, _, markerTrace_refines_valueTrace (op :: rest) rows
          (fun i => if i = j then (1 : Int) else 0) final marks htrace⟩
      · intro hall
        have hsteps : ∀ j : Fin k, ∃ mid,
            valueStep op (evalRows rows
              (fun i => if i = j then (1 : Int) else 0)) = some mid := by
          intro j
          obtain ⟨out, marks, hwhole⟩ := hall j
          obtain ⟨mid, hmid, _, _, _⟩ := valueTrace_cons_success
            op rest _ out marks hwhole
          exact ⟨mid, hmid⟩
        obtain ⟨next, hrow⟩ := (rowStep_success_iff_all_basis op rows).2 hsteps
        have htail : ∀ j : Fin k, ∃ final marks,
            valueTrace rest (evalRows next
              (fun i => if i = j then (1 : Int) else 0)) = some (final, marks) := by
          intro j
          obtain ⟨out, marks, hwhole⟩ := hall j
          obtain ⟨mid, hmid, tailOut, tailMarks, htailStep⟩ :=
            valueTrace_cons_success op rest _ out marks hwhole
          have href := rowStep_refines_values op rows next
            (fun i => if i = j then (1 : Int) else 0) hrow
          have heq : mid = evalRows next
              (fun i => if i = j then (1 : Int) else 0) := by
            exact Option.some.inj (hmid.symm.trans href)
          subst mid
          exact ⟨tailOut, tailMarks, htailStep⟩
        obtain ⟨final, marks, htrace⟩ := (ih next).2 htail
        cases op with
        | phaseProduct i =>
            simp only [Paper.FullDSL.rowStep, Option.some.injEq] at hrow
            subst next
            exact ⟨final, rows i :: marks, by
              simp [Paper.SourceBridge.markerTrace, htrace]⟩
        | shiftL i n =>
            exact ⟨final, marks, by
              simp [Paper.SourceBridge.markerTrace, hrow, htrace]⟩
        | shiftR i n =>
            exact ⟨final, marks, by
              simp [Paper.SourceBridge.markerTrace, hrow, htrace]⟩
        | negate i =>
            exact ⟨final, marks, by
              simp [Paper.SourceBridge.markerTrace, hrow, htrace]⟩
        | addScaled dst src negSrc shift =>
            exact ⟨final, marks, by
              simp [Paper.SourceBridge.markerTrace, hrow, htrace]⟩

/-- All-basis success recovers the actual final symbolic rows and the exact
ordered marker rows, hence works for every integer input after reflection. -/
theorem all_basis_valueTrace_yields_uniform_trace {k : Nat}
    (word : List (Paper.FullDSL.Instruction k)) (rows : Paper.FullDSL.Rows k)
    (hall : ∀ j : Fin k, ∃ final marks,
      valueTrace word (evalRows rows
        (fun i => if i = j then (1 : Int) else 0)) = some (final, marks)) :
    ∃ final marks,
      Paper.SourceBridge.markerTrace word rows = some (final, marks) ∧
      ∀ x : Values k,
        valueTrace word (evalRows rows x) =
          some (evalRows final x, marks.map (fun r => evalRow r x)) := by
  obtain ⟨final, marks, htrace⟩ :=
    (markerTrace_success_iff_all_basis_valueTrace word rows).2 hall
  exact ⟨final, marks, htrace,
    fun x => markerTrace_refines_valueTrace word rows x final marks htrace⟩

/-- A single scalar input can hide nondivisible row coefficients: `(1,1)`
turns `[1,1]` into the divisible value `2`, although symbolic SHR fails. -/
theorem one_input_does_not_detect_shiftR :
    (∃ v', valueStep (.shiftR (0 : Fin 2) 1)
      (evalRows (fun i _j : Fin 2 => if i = 0 then (1 : Int) else 0)
        (fun _ : Fin 2 => (1 : Int))) = some v') ∧
    Paper.FullDSL.rowStep (.shiftR (0 : Fin 2) 1)
      (fun i _j : Fin 2 => if i = 0 then (1 : Int) else 0) = none := by
  constructor
  · refine ⟨Function.update
      (evalRows (fun i _j : Fin 2 => if i = 0 then (1 : Int) else 0)
        (fun _ : Fin 2 => (1 : Int))) (0 : Fin 2) 1, ?_⟩
    norm_num [valueStep, evalRows, evalRow, Fin.sum_univ_two]
  · simp [Paper.FullDSL.rowStep]

end Paper.BasisReflection
