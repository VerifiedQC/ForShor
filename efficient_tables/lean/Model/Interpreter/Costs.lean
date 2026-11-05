import Model.Interpreter.SourceConnection

/-!
# Cost bridge between source metrics and the full model

Shows the source-level metrics (operation count, PhaseProduct count, layer count) agree with the counts of the independent full-language model, for example `wordCharge_eq_counts` and `phaseProgramOverhead_eq_counts`. Concludes with `analyzeBalancedProgram_eq_model` and the concrete C11 values `original_c11_counts` and `original_c11_charge`.
-/

namespace Paper.CostBridge

theorem arithmeticOperationCount_eq_counts {k : Nat}
    (ops : TableGeneration.Prog k) :
    TableGeneration.arithmeticOperationCount ops =
      (wordCounts (SourceBridge.mapToFull ops)).shiftL +
      (wordCounts (SourceBridge.mapToFull ops)).shiftR +
      (wordCounts (SourceBridge.mapToFull ops)).negate +
      (wordCounts (SourceBridge.mapToFull ops)).plusAdd +
      (wordCounts (SourceBridge.mapToFull ops)).minusAdd := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      cases op with
      | shiftL i n =>
          simp [TableGeneration.arithmeticOperationCount, SourceBridge.mapToFull,
            SourceBridge.toFull, wordCounts] at ih ⊢
          omega
      | shiftR i n =>
          simp [TableGeneration.arithmeticOperationCount, SourceBridge.mapToFull,
            SourceBridge.toFull, wordCounts] at ih ⊢
          omega
      | negate i =>
          simp [TableGeneration.arithmeticOperationCount, SourceBridge.mapToFull,
            SourceBridge.toFull, wordCounts] at ih ⊢
          omega
      | addScaled d s b n =>
          cases b <;>
            simp [TableGeneration.arithmeticOperationCount, SourceBridge.mapToFull,
              SourceBridge.toFull, wordCounts] at ih ⊢ <;>
            omega
      | phaseProduct i =>
          simp [TableGeneration.arithmeticOperationCount, SourceBridge.mapToFull,
            SourceBridge.toFull, wordCounts] at ih ⊢
          omega

theorem phaseProductCount_eq_markers {k : Nat}
    (ops : TableGeneration.Prog k) :
    TableGeneration.phaseProductCount ops =
      (wordCounts (SourceBridge.mapToFull ops)).markers := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      cases op with
      | addScaled d s b n =>
          cases b <;> simp [TableGeneration.phaseProductCount,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts, ih]
      | shiftL i n =>
          simp [TableGeneration.phaseProductCount,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts, ih]
      | shiftR i n =>
          simp [TableGeneration.phaseProductCount,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts, ih]
      | negate i =>
          simp [TableGeneration.phaseProductCount,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts, ih]
      | phaseProduct i =>
          simp [TableGeneration.phaseProductCount,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts, ih]

theorem parallelPhaseProductLayerCountAux_eq {k : Nat}
    (inLayer : Bool) (ops : TableGeneration.Prog k) :
    TableGeneration.parallelPhaseProductLayerCountAux inLayer ops =
      markerLayerCountAux inLayer (SourceBridge.mapToFull ops) := by
  induction ops generalizing inLayer with
  | nil => cases inLayer <;> rfl
  | cons op rest ih =>
      cases op with
      | addScaled d s b n =>
          cases b <;> simp [TableGeneration.parallelPhaseProductLayerCountAux,
            SourceBridge.mapToFull, SourceBridge.toFull, markerLayerCountAux, ih]
      | shiftL i n =>
          simp [TableGeneration.parallelPhaseProductLayerCountAux,
            SourceBridge.mapToFull, SourceBridge.toFull, markerLayerCountAux, ih]
      | shiftR i n =>
          simp [TableGeneration.parallelPhaseProductLayerCountAux,
            SourceBridge.mapToFull, SourceBridge.toFull, markerLayerCountAux, ih]
      | negate i =>
          simp [TableGeneration.parallelPhaseProductLayerCountAux,
            SourceBridge.mapToFull, SourceBridge.toFull, markerLayerCountAux, ih]
      | phaseProduct i =>
          cases inLayer <;>
            simp [TableGeneration.parallelPhaseProductLayerCountAux,
              SourceBridge.mapToFull, SourceBridge.toFull, markerLayerCountAux, ih]

theorem parallelPhaseProductLayerCount_eq {k : Nat}
    (ops : TableGeneration.Prog k) :
    TableGeneration.parallelPhaseProductLayerCount ops =
      markerLayerCount (SourceBridge.mapToFull ops) := by
  exact parallelPhaseProductLayerCountAux_eq false ops

theorem wordCharge_eq_counts {k : Nat} (word : List (FullDSL.Instruction k)) :
    FullDSL.wordCharge word =
      (wordCounts word).plusAdd + 3 * (wordCounts word).minusAdd +
      (wordCounts word).negate := by
  induction word with
  | nil => rfl
  | cons op rest ih =>
      cases op with
      | addScaled d s b n =>
          cases b <;> simp [FullDSL.wordCharge, FullDSL.charge, wordCounts] at ih ⊢ <;> omega
      | shiftL i n =>
          simp [FullDSL.wordCharge, FullDSL.charge, wordCounts] at ih ⊢
          omega
      | shiftR i n =>
          simp [FullDSL.wordCharge, FullDSL.charge, wordCounts] at ih ⊢
          omega
      | negate i =>
          simp [FullDSL.wordCharge, FullDSL.charge, wordCounts] at ih ⊢
          omega
      | phaseProduct i =>
          simp [FullDSL.wordCharge, FullDSL.charge, wordCounts] at ih ⊢
          omega

theorem phaseProgramOverhead_eq_counts {k : Nat}
    (workingWidth : Nat) (ops : TableGeneration.Prog k) :
    TableGeneration.RecursiveCost.phaseProgramOverhead workingWidth ops =
      2 * TableGeneration.RecursiveCost.rippleAdderGateBound workingWidth *
        ((wordCounts (SourceBridge.mapToFull ops)).plusAdd +
         (wordCounts (SourceBridge.mapToFull ops)).minusAdd) +
      2 * TableGeneration.RecursiveCost.negateGateBound workingWidth *
        (wordCounts (SourceBridge.mapToFull ops)).negate := by
  induction ops with
  | nil => simp [TableGeneration.RecursiveCost.phaseProgramOverhead,
      SourceBridge.mapToFull, wordCounts]
  | cons op rest ih =>
      cases op with
      | addScaled d s b n =>
          cases b <;> simp [TableGeneration.RecursiveCost.phaseProgramOverhead,
            TableGeneration.RecursiveCost.phaseArithmeticOpCost,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts] at ih ⊢ <;>
            rw [ih] <;> ring
      | shiftL i n =>
          simp [TableGeneration.RecursiveCost.phaseProgramOverhead,
            TableGeneration.RecursiveCost.phaseArithmeticOpCost,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts] at ih ⊢ <;>
            rw [ih] <;> ring
      | shiftR i n =>
          simp [TableGeneration.RecursiveCost.phaseProgramOverhead,
            TableGeneration.RecursiveCost.phaseArithmeticOpCost,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts] at ih ⊢ <;>
            rw [ih] <;> ring
      | negate i =>
          simp [TableGeneration.RecursiveCost.phaseProgramOverhead,
            TableGeneration.RecursiveCost.phaseArithmeticOpCost,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts] at ih ⊢ <;>
            rw [ih] <;> ring
      | phaseProduct i =>
          simp [TableGeneration.RecursiveCost.phaseProgramOverhead,
            TableGeneration.RecursiveCost.phaseArithmeticOpCost,
            SourceBridge.mapToFull, SourceBridge.toFull, wordCounts] at ih ⊢ <;>
            rw [ih] <;> ring

theorem analyzeBalancedProgram_eq_counts {k : Nat}
    (width : Nat) (ops : TableGeneration.Prog k) :
    TableGeneration.RecursiveCost.analyzeBalancedProgram width ops =
      { childWidth := 1 + (Scanner.scan
          (FullDSL.widthWord (SourceBridge.mapToFull ops))
          (Scanner.fresh (ArrayBridge.literalSourceSplit width k))).peak
        arithmeticGateCount :=
          2 * TableGeneration.RecursiveCost.rippleAdderGateBound
            (TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops) *
            ((wordCounts (SourceBridge.mapToFull ops)).plusAdd +
             (wordCounts (SourceBridge.mapToFull ops)).minusAdd) +
          2 * TableGeneration.RecursiveCost.negateGateBound
            (TableGeneration.RecursiveCost.nextBalancedSignedWidth width ops) *
            (wordCounts (SourceBridge.mapToFull ops)).negate
        arithmeticOperationCount :=
          (wordCounts (SourceBridge.mapToFull ops)).shiftL +
          (wordCounts (SourceBridge.mapToFull ops)).shiftR +
          (wordCounts (SourceBridge.mapToFull ops)).negate +
          (wordCounts (SourceBridge.mapToFull ops)).plusAdd +
          (wordCounts (SourceBridge.mapToFull ops)).minusAdd
        recursiveCallCount := (wordCounts (SourceBridge.mapToFull ops)).markers } := by
  simp only [TableGeneration.RecursiveCost.analyzeBalancedProgram]
  rw [ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord,
    phaseProgramOverhead_eq_counts, arithmeticOperationCount_eq_counts,
    phaseProductCount_eq_markers]

theorem analyzeBalancedProgram_eq_model {k : Nat}
    (width : Nat) (ops : TableGeneration.Prog k) :
    TableGeneration.RecursiveCost.analyzeBalancedProgram width ops =
      balancedAnalysis width (SourceBridge.mapToFull ops) := by
  simpa [balancedAnalysis, ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord]
    using analyzeBalancedProgram_eq_counts width ops

theorem original_c11_counts :
    wordCounts (SourceBridge.mapToFull SourceBridge.originalC11Word) =
      ⟨0, 0, 2, 9, 0, 5⟩ := by decide

theorem original_c11_layers :
    TableGeneration.parallelPhaseProductLayerCount SourceBridge.originalC11Word = 4 := by
  decide

theorem original_c11_charge :
    FullDSL.wordCharge (SourceBridge.mapToFull SourceBridge.originalC11Word) = 11 := by
  decide

theorem original_c11_overhead :
    TableGeneration.RecursiveCost.phaseProgramOverhead 8 SourceBridge.originalC11Word =
      1660 := by decide

theorem original_c11_analysis :
    TableGeneration.RecursiveCost.analyzeBalancedProgram 2 SourceBridge.originalC11Word =
      ⟨8, 1660, 11, 5⟩ := by decide

end Paper.CostBridge
