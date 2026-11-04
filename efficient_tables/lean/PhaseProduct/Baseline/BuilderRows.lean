import Model.Interpreter.Consumption
import PhaseProduct.Baseline.BaselineArithmetic

/-!
# Baseline builder rows

Row and marker-trace lemmas for the baseline builders: marker traces append and
vanish without markers (`markerTrace_append`, `markerTrace_without_markers`),
the local builders are add-only and safe (`computeLocal_addOnly`,
`computeLocal_safe`), and their runs reach the intended start rows
(`computeLocal_run_start`, `computeFracLocal_run_start`).
-/

namespace Paper.BaselineContract

open Paper.SourceBridge

theorem markerTrace_append {k : Nat} (first second : List (FullDSL.Instruction k))
    (rows : FullDSL.Rows k) :
    markerTrace (first ++ second) rows = (do
      let (middle, left) ← markerTrace first rows
      let (final, right) ← markerTrace second middle
      pure (final, left ++ right)) := by
  induction first generalizing rows with
  | nil => simp [markerTrace]
  | cons op rest ih =>
      cases op with
      | phaseProduct i =>
          simp only [List.cons_append, markerTrace]
          rw [ih]
          cases ht : markerTrace rest rows with
          | none => simp [ht]
          | some pair =>
              obtain ⟨middle, left⟩ := pair
              cases hs : markerTrace second middle with
              | none => simp [hs]
              | some pair =>
                  obtain ⟨final, right⟩ := pair
                  simp [hs]
      | shiftL i n =>
          simp only [List.cons_append, markerTrace]
          cases hs : FullDSL.rowStep (.shiftL i n) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle
      | shiftR i n =>
          simp only [List.cons_append, markerTrace]
          cases hs : FullDSL.rowStep (.shiftR i n) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle
      | negate i =>
          simp only [List.cons_append, markerTrace]
          cases hs : FullDSL.rowStep (.negate i) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle
      | addScaled d s neg sh =>
          simp only [List.cons_append, markerTrace]
          cases hs : FullDSL.rowStep (.addScaled d s neg sh) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle

theorem markerTrace_without_markers {k : Nat}
    (word : List (FullDSL.Instruction k)) (rows : FullDSL.Rows k)
    (hfree : ∀ op ∈ word, ∀ i, op ≠ .phaseProduct i) :
    markerTrace word rows = (FullDSL.runRows word rows).map (fun final => (final, [])) := by
  induction word generalizing rows with
  | nil => rfl
  | cons op rest ih =>
      have hrest : ∀ a ∈ rest, ∀ i, a ≠ .phaseProduct i := by
        intro a ha i
        exact hfree a (by simp [ha]) i
      cases op with
      | phaseProduct i =>
          exact False.elim (hfree (.phaseProduct i) (by simp) i rfl)
      | shiftL i n =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.shiftL i n) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle hrest
      | shiftR i n =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.shiftR i n) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle hrest
      | negate i =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.negate i) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle hrest
      | addScaled d s neg sh =>
          simp only [markerTrace, FullDSL.runRows]
          cases hs : FullDSL.rowStep (.addScaled d s neg sh) rows with
          | none => simp [hs]
          | some middle => simpa [hs] using ih middle hrest

theorem source_markerTrace_without_markers {k : Nat}
    (word : TableGeneration.Prog k) (rows final : TableGeneration.State k)
    (hsafe : TableGeneration.safeProg? word = true)
    (hfree : ∀ op ∈ word, ∀ i, op ≠ .phaseProduct i)
    (hrun : TableGeneration.run? word rows = some final) :
    markerTrace (mapToFull word) rows = some (final, []) := by
  have hfree' : ∀ op ∈ mapToFull word, ∀ i, op ≠ .phaseProduct i := by
    intro op hop i
    obtain ⟨src, hsrc, rfl⟩ : ∃ src ∈ word, toFull src = op := by
      simpa [mapToFull] using (List.mem_map.mp hop)
    have hneq := hfree src hsrc i
    cases src <;> simpa [toFull] using hneq
  rw [markerTrace_without_markers (mapToFull word) rows hfree']
  rw [runRows_eq_run_of_safe word rows hsafe, hrun]
  rfl

theorem list_sum_basis {k : Nat} (js : List (Fin k)) (coeff : Fin k → Int)
    (hnd : js.Nodup) (j : Fin k) :
    (@List.sum Int Int.instAdd (@MulZeroClass.toZero Int (@NonUnitalNonAssocSemiring.toMulZeroClass Int (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Int (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Int (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Int (@CommRing.toNonUnitalCommRing Int Int.instCommRing)))))) (js.map (fun i => if j = i then coeff i else 0))) =
      if j ∈ js then coeff j else 0 := by
  induction js with
  | nil => simp
  | cons i rest ih =>
      have hni : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hnr : rest.Nodup := (List.nodup_cons.mp hnd).2
      by_cases hji : j = i
      · subst j
        simp [hni, ih hnr]
      · simpa [hji, List.mem_cons] using ih hnr

theorem mem_nonzeroFins {k : Nat} (hk : 0 < k) (j : Fin k) :
    j ∈ TableGeneration.nonzeroFins hk ↔ j ≠ TableGeneration.finZero hk := by
  simp [TableGeneration.nonzeroFins]

theorem nonzeroFins_nodup {k : Nat} (hk : 0 < k) :
    (TableGeneration.nonzeroFins hk).Nodup := by
  unfold TableGeneration.nonzeroFins
  exact List.Nodup.filter _ (List.nodup_finRange k)

theorem mem_nonlastFins {k : Nat} (hk : 0 < k) (j : Fin k) :
    j ∈ TableGeneration.nonlastFins hk ↔ j ≠ TableGeneration.finLast hk := by
  simp [TableGeneration.nonlastFins]

theorem nonlastFins_nodup {k : Nat} (hk : 0 < k) :
    (TableGeneration.nonlastFins hk).Nodup := by
  unfold TableGeneration.nonlastFins
  exact List.Nodup.filter _ (List.nodup_finRange k)

theorem computeLocalAux_eq_flatMap {k : Nat} (hk : 0 < k) (z : Int)
    (js : List (Fin k)) :
    TableGeneration.computeLocalAux hk z js =
      js.flatMap (fun j => TableGeneration.addConstFrom (TableGeneration.finZero hk)
        j (z ^ j.val)) := by
  induction js with
  | nil => rfl
  | cons j rest ih =>
      simp [TableGeneration.computeLocalAux, List.flatMap_cons, ih]

theorem computeFracLocalAux_eq_flatMap {k : Nat} (hk : 0 < k) (c : Int)
    (js : List (Fin k)) :
    TableGeneration.computeFracLocalAux hk c js =
      js.flatMap (fun j => TableGeneration.addConstFrom (TableGeneration.finLast hk)
        j (TableGeneration.fracCoeff c j)) := by
  induction js with
  | nil => rfl
  | cons j rest ih =>
      simp [TableGeneration.computeFracLocalAux, List.flatMap_cons, ih]

theorem run_addConst_flatMap {k : Nat} (dst : Fin k) (coeff : Fin k → Int)
    (js : List (Fin k)) (sigma : TableGeneration.State k)
    (hsep : ∀ i ∈ js, dst ≠ i) :
    TableGeneration.run? (js.flatMap (fun i => TableGeneration.addConstFrom dst i (coeff i))) sigma =
      some (TableGeneration.State.setReg sigma dst
        (fun j => sigma dst j + (@List.sum Int Int.instAdd (@MulZeroClass.toZero Int (@NonUnitalNonAssocSemiring.toMulZeroClass Int (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Int (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Int (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Int (@CommRing.toNonUnitalCommRing Int Int.instCommRing)))))) (js.map (fun i => coeff i * sigma i j))))) := by
  induction js generalizing sigma with
  | nil =>
      simpa [TableGeneration.run?, BaselineArithmetic.setReg_same]
  | cons i rest ih =>
      have hi : dst ≠ i := hsep i (by simp)
      have hrest : ∀ x ∈ rest, dst ≠ x := by
        intro x hx
        exact hsep x (by simp [hx])
      simp only [List.flatMap_cons, BaselineArithmetic.run_append]
      rw [BaselineArithmetic.addConstFrom_run dst i (coeff i) sigma hi]
      simp only [Option.bind_some]
      rw [ih _ hrest]
      congr 1
      funext x j
      by_cases hx : x = dst
      · subst x
        have hmap :
            (rest.map (fun s => coeff s *
              (TableGeneration.State.setReg sigma dst
                (fun t => sigma dst t + coeff i * sigma i t)) s j)).sum =
            (rest.map (fun s => coeff s * sigma s j)).sum := by
          congr 1
          apply List.map_congr_left
          intro s hs
          have hne : s ≠ dst := Ne.symm (hrest s hs)
          simp [TableGeneration.State.setReg, hne]
        simp only [TableGeneration.State.setReg, ↓reduceIte] at hmap ⊢
        rw [hmap]
        simp only [List.map_cons, List.sum_cons]
        ring
      · simp [TableGeneration.State.setReg, hx]

theorem flatMap_addConst_addOnly {k : Nat} (dst : Fin k) (coeff : Fin k → Int)
    (js : List (Fin k)) (hsep : ∀ i ∈ js, dst ≠ i) :
    ∀ op ∈ js.flatMap (fun i => TableGeneration.addConstFrom dst i (coeff i)),
      ∃ (d s : Fin k) (b : Bool) (sh : Nat),
        op = .addScaled d s b sh ∧ d ≠ s := by
  intro op hop
  obtain ⟨i, hi, hop'⟩ := List.mem_flatMap.mp hop
  exact BaselineArithmetic.addConstFrom_addOnly dst i (coeff i) (hsep i hi) op hop'

theorem flatMap_addConst_safe {k : Nat} (dst : Fin k) (coeff : Fin k → Int)
    (js : List (Fin k)) (hsep : ∀ i ∈ js, dst ≠ i) :
    TableGeneration.safeProg?
      (js.flatMap (fun i => TableGeneration.addConstFrom dst i (coeff i))) = true :=
  BaselineArithmetic.addOnly_safe _ (flatMap_addConst_addOnly dst coeff js hsep)

theorem computeLocal_addOnly {k : Nat} (hk : 0 < k) (z : Int) :
    ∀ op ∈ TableGeneration.computeLocal hk z,
      ∃ (d s : Fin k) (b : Bool) (sh : Nat),
        op = .addScaled d s b sh ∧ d ≠ s := by
  rw [TableGeneration.computeLocal, computeLocalAux_eq_flatMap]
  exact flatMap_addConst_addOnly _ _ _ (fun i hi => Ne.symm ((mem_nonzeroFins hk i).mp hi))

theorem computeFracLocal_addOnly {k : Nat} (hk : 0 < k) (c : Int) :
    ∀ op ∈ TableGeneration.computeFracLocal hk c,
      ∃ (d s : Fin k) (b : Bool) (sh : Nat),
        op = .addScaled d s b sh ∧ d ≠ s := by
  rw [TableGeneration.computeFracLocal, computeFracLocalAux_eq_flatMap]
  exact flatMap_addConst_addOnly _ _ _ (fun i hi => Ne.symm ((mem_nonlastFins hk i).mp hi))

theorem computeLocal_safe {k : Nat} (hk : 0 < k) (z : Int) :
    TableGeneration.safeProg? (TableGeneration.computeLocal hk z) = true :=
  BaselineArithmetic.addOnly_safe _ (computeLocal_addOnly hk z)

theorem computeFracLocal_safe {k : Nat} (hk : 0 < k) (c : Int) :
    TableGeneration.safeProg? (TableGeneration.computeFracLocal hk c) = true :=
  BaselineArithmetic.addOnly_safe _ (computeFracLocal_addOnly hk c)

theorem sum_nonzero_basis {k : Nat} (hk : 0 < k) (z : Int) (j : Fin k) :
    (@List.sum Int Int.instAdd (@MulZeroClass.toZero Int (@NonUnitalNonAssocSemiring.toMulZeroClass Int (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Int (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Int (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Int (@CommRing.toNonUnitalCommRing Int Int.instCommRing)))))) ((TableGeneration.nonzeroFins hk).map
      (fun i => z ^ i.val * TableGeneration.State.start_state i j))) =
      if j = TableGeneration.finZero hk then 0 else z ^ j.val := by
  have hmap :
      ((TableGeneration.nonzeroFins hk).map
        (fun i => z ^ i.val * TableGeneration.State.start_state i j)).sum =
      ((TableGeneration.nonzeroFins hk).map
        (fun i => if j = i then z ^ i.val else 0)).sum := by
    congr 1
    apply List.map_congr_left
    intro i _
    simp [TableGeneration.State.start_state]
  rw [hmap, list_sum_basis _ _ (nonzeroFins_nodup hk) j]
  by_cases hj : j = TableGeneration.finZero hk <;>
    simp [mem_nonzeroFins, hj]

theorem sum_nonlast_basis {k : Nat} (hk : 0 < k) (c : Int) (j : Fin k) :
    (@List.sum Int Int.instAdd (@MulZeroClass.toZero Int (@NonUnitalNonAssocSemiring.toMulZeroClass Int (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Int (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Int (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Int (@CommRing.toNonUnitalCommRing Int Int.instCommRing)))))) ((TableGeneration.nonlastFins hk).map
      (fun i => TableGeneration.fracCoeff c i * TableGeneration.State.start_state i j))) =
      if j = TableGeneration.finLast hk then 0 else TableGeneration.fracCoeff c j := by
  have hmap :
      ((TableGeneration.nonlastFins hk).map
        (fun i => TableGeneration.fracCoeff c i * TableGeneration.State.start_state i j)).sum =
      ((TableGeneration.nonlastFins hk).map
        (fun i => if j = i then TableGeneration.fracCoeff c i else 0)).sum := by
    congr 1
    apply List.map_congr_left
    intro i _
    simp [TableGeneration.State.start_state]
  rw [hmap, list_sum_basis _ _ (nonlastFins_nodup hk) j]
  by_cases hj : j = TableGeneration.finLast hk <;>
    simp [mem_nonlastFins, hj]

theorem computeLocal_run_start {k : Nat} (hk : 0 < k) (z : Int) :
    TableGeneration.run? (TableGeneration.computeLocal hk z)
      TableGeneration.State.start_state =
      some (TableGeneration.State.setReg TableGeneration.State.start_state
        (TableGeneration.finZero hk) (TableGeneration.expectedRow (.int z))) := by
  rw [TableGeneration.computeLocal, computeLocalAux_eq_flatMap]
  rw [run_addConst_flatMap (TableGeneration.finZero hk) (fun i => z ^ i.val)
    (TableGeneration.nonzeroFins hk) TableGeneration.State.start_state
    (fun i hi => Ne.symm ((mem_nonzeroFins hk i).mp hi))]
  congr 1
  congr 1
  funext j
  rw [sum_nonzero_basis hk z j]
  by_cases hj : j = TableGeneration.finZero hk
  · subst j
    simp [TableGeneration.State.start_state, TableGeneration.expectedRow,
      TableGeneration.finZero]
  · simp [TableGeneration.State.start_state, TableGeneration.expectedRow, hj]

theorem computeFracLocal_run_start {k : Nat} (hk : 0 < k) (c : Int) :
    TableGeneration.run? (TableGeneration.computeFracLocal hk c)
      TableGeneration.State.start_state =
      some (TableGeneration.State.setReg TableGeneration.State.start_state
        (TableGeneration.finLast hk) (TableGeneration.expectedRow (.frac c))) := by
  rw [TableGeneration.computeFracLocal, computeFracLocalAux_eq_flatMap]
  rw [run_addConst_flatMap (TableGeneration.finLast hk) (TableGeneration.fracCoeff c)
    (TableGeneration.nonlastFins hk) TableGeneration.State.start_state
    (fun i hi => Ne.symm ((mem_nonlastFins hk i).mp hi))]
  congr 1
  congr 1
  funext j
  rw [sum_nonlast_basis hk c j]
  by_cases hj : j = TableGeneration.finLast hk
  · subst j
    simp [TableGeneration.State.start_state, TableGeneration.expectedRow,
      TableGeneration.fracCoeff, TableGeneration.finLast]
  · simp [TableGeneration.State.start_state, TableGeneration.expectedRow,
      TableGeneration.fracCoeff, hj]

end Paper.BaselineContract
