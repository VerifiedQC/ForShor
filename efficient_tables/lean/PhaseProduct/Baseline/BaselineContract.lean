import PhaseProduct.Baseline.BuilderRows

/-!
# Baseline generator contract

Contract for the schoolbook-style baseline generator: add-only words are
marker-free (`addOnly_markerFree`), the reset block meets its contract
(`addOnly_reset_block_contract`), and the contract lifts through per-point
operations (`opsForPointWithProduct_contract`, `genOpsWithProduct_contract`) to
the whole generator (`baselineGenerate_contract`).
-/

namespace Paper.BaselineContract

open Paper.SourceBridge

theorem addOnly_markerFree {k : Nat} (word : TableGeneration.Prog k)
    (hadd : ∀ op ∈ word, ∃ (d s : Fin k) (b : Bool) (sh : Nat),
      op = .addScaled d s b sh ∧ d ≠ s) :
    ∀ op ∈ word, ∀ i, op ≠ .phaseProduct i := by
  intro op hop i
  obtain ⟨d, s, b, sh, rfl, _⟩ := hadd op hop
  simp

theorem safe_append {k : Nat} (first second : TableGeneration.Prog k)
    (hfirst : TableGeneration.safeProg? first = true)
    (hsecond : TableGeneration.safeProg? second = true) :
    TableGeneration.safeProg? (first ++ second) = true := by
  apply (SourceBridge.safeProg_iff (first ++ second)).mpr
  intro op hop
  rcases List.mem_append.mp hop with h | h
  · exact (SourceBridge.safeProg_iff first).mp hfirst op h
  · exact (SourceBridge.safeProg_iff second).mp hsecond op h

theorem addOnly_reset_block_contract {k : Nat} (hk : 0 < k)
    (pt : TableGeneration.Operations.Point) (dst : Fin k)
    (build : TableGeneration.Prog k) (middle : TableGeneration.State k)
    (hadd : ∀ op ∈ build, ∃ (d s : Fin k) (b : Bool) (sh : Nat),
      op = .addScaled d s b sh ∧ d ≠ s)
    (hrun : TableGeneration.run? build TableGeneration.State.start_state = some middle)
    (hrow : middle dst = TableGeneration.expectedRow pt) :
    TableGeneration.ProgConsumesPtsSafe hk TableGeneration.State.start_state
      (build ++ [.phaseProduct dst] ++ TableGeneration.apply_Op_inverse build) [pt] := by
  have hsafeBuild := BaselineArithmetic.addOnly_safe build hadd
  have haddInv := BaselineArithmetic.inverse_addOnly build hadd
  have hsafeInv := BaselineArithmetic.inverse_addOnly_safe build hadd
  have hrunInv := BaselineArithmetic.run_inverse_addOnly build
    TableGeneration.State.start_state middle hadd hrun
  have htraceBuild := source_markerTrace_without_markers build
    TableGeneration.State.start_state middle hsafeBuild
    (addOnly_markerFree build hadd) hrun
  have htraceInv := source_markerTrace_without_markers
    (TableGeneration.apply_Op_inverse build) middle
    TableGeneration.State.start_state hsafeInv
    (addOnly_markerFree _ haddInv) hrunInv
  have hsafeMarker : TableGeneration.safeProg? ([.phaseProduct dst] : TableGeneration.Prog k) = true := by
    rfl
  have hsafe : TableGeneration.safeProg?
      (build ++ [.phaseProduct dst] ++ TableGeneration.apply_Op_inverse build) = true :=
    safe_append _ _ (safe_append _ _ hsafeBuild hsafeMarker) hsafeInv
  apply (SourceBridge.source_contract_iff_trace hk _ _ _).mpr
  refine ⟨hsafe, ?_⟩
  simp only [mapToFull, List.map_append]
  rw [markerTrace_append]
  simp only [mapToFull] at htraceBuild htraceInv
  rw [markerTrace_append]
  rw [htraceBuild]
  simp [toFull, markerTrace, htraceInv, hrow]

theorem frac_zero_start_row {k : Nat} (hk : 0 < k) :
    TableGeneration.State.start_state (TableGeneration.finLast hk) =
      TableGeneration.expectedRow (.frac 0) := by
  funext j
  by_cases hj : j = TableGeneration.finLast hk
  · subst j
    simp [TableGeneration.State.start_state, TableGeneration.expectedRow,
      TableGeneration.finLast]
  · have hlt : j.val < k - 1 := by
      have hne : j.val ≠ k - 1 := by
        intro he
        exact hj (Fin.ext he)
      omega
    have hpos : 0 < k - 1 - j.val := by omega
    have hn : k - 1 - j.val ≠ 0 := Nat.ne_of_gt hpos
    simp [TableGeneration.State.start_state, TableGeneration.expectedRow, hj,
      hn]

theorem opsForPointWithProduct_contract {k : Nat} (hk : 0 < k)
    (pt : TableGeneration.Operations.Point) :
    TableGeneration.ProgConsumesPtsSafe hk TableGeneration.State.start_state
      (TableGeneration.opsForPointWithProduct hk pt) [pt] := by
  cases pt with
  | int z =>
      let middle := TableGeneration.State.setReg TableGeneration.State.start_state
        (TableGeneration.finZero hk) (TableGeneration.expectedRow (.int z))
      have hrow : middle (TableGeneration.finZero hk) =
          TableGeneration.expectedRow (.int z) := by
        simp [middle, TableGeneration.State.setReg]
      have h := addOnly_reset_block_contract hk (.int z) (TableGeneration.finZero hk)
        (TableGeneration.computeLocal hk z) middle
        (computeLocal_addOnly hk z) (computeLocal_run_start hk z) hrow
      simpa [TableGeneration.opsForPointWithProduct] using h
  | frac c =>
      by_cases hc : c = 0
      · subst c
        have h := addOnly_reset_block_contract hk (.frac 0) (TableGeneration.finLast hk)
          [] TableGeneration.State.start_state (by simp) (by rfl) (frac_zero_start_row hk)
        simpa [TableGeneration.opsForPointWithProduct] using h
      · let middle := TableGeneration.State.setReg TableGeneration.State.start_state
          (TableGeneration.finLast hk) (TableGeneration.expectedRow (.frac c))
        have hrow : middle (TableGeneration.finLast hk) =
            TableGeneration.expectedRow (.frac c) := by
          simp [middle, TableGeneration.State.setReg]
        have h := addOnly_reset_block_contract hk (.frac c) (TableGeneration.finLast hk)
          (TableGeneration.computeFracLocal hk c) middle
          (computeFracLocal_addOnly hk c) (computeFracLocal_run_start hk c) hrow
        simpa [TableGeneration.opsForPointWithProduct, hc] using h

theorem genOpsWithProduct_contract {k : Nat} (hk : 0 < k)
    (pts : List TableGeneration.Operations.Point) :
    TableGeneration.ProgConsumesPtsSafe hk TableGeneration.State.start_state
      (TableGeneration.genOpsWithProduct hk pts) pts := by
  induction pts with
  | nil =>
      apply (SourceBridge.source_contract_iff_trace hk _ _ _).mpr
      simp [TableGeneration.genOpsWithProduct, mapToFull, markerTrace,
        TableGeneration.safeProg?, TableGeneration.Prog.wellFormed?]
  | cons pt rest ih =>
      have hb := opsForPointWithProduct_contract hk pt
      obtain ⟨hsafeB, htraceB⟩ :=
        (SourceBridge.source_contract_iff_trace hk _ _ _).mp hb
      obtain ⟨hsafeR, htraceR⟩ :=
        (SourceBridge.source_contract_iff_trace hk _ _ _).mp ih
      apply (SourceBridge.source_contract_iff_trace hk _ _ _).mpr
      constructor
      · simpa [TableGeneration.genOpsWithProduct] using
          safe_append _ _ hsafeB hsafeR
      · simp only [TableGeneration.genOpsWithProduct, mapToFull, List.map_append]
        rw [markerTrace_append]
        simp only [mapToFull] at htraceB htraceR
        simp [htraceB, htraceR]

theorem baselineGenerate_contract (mode : TableGeneration.ProductMode)
    (k : Nat) (hk : k ≥ 2) :
    TableGeneration.ProgConsumesPtsSafe (TableGeneration.positive_of_ge_two hk)
      TableGeneration.State.start_state (TableGeneration.baselineGenerate mode k hk)
      (TableGeneration.baselineGeneratePointsInOrder mode k hk) := by
  simpa [TableGeneration.baselineGenerate] using
    genOpsWithProduct_contract (TableGeneration.positive_of_ge_two hk)
      (TableGeneration.baselineGeneratePointsInOrder mode k hk)

end Paper.BaselineContract
