import Provider.Compression.Program
import PhaseProduct.Baseline.BuilderRows

/-!
# Trace preservation under compression

Shows that compressing shift blocks preserves the marker trace: for a single
block (`shiftBlock_trace`), through the accumulator pass (`compressAux_trace`)
and for the whole word (`compressWhole_trace`). `trace_cons_transfer` is the
one-instruction step used along the way.
-/

namespace Paper.CompressionTrace

open Paper.FullDSL Paper.ShiftCompression Paper.WholeCompression Paper.SourceBridge

theorem shiftBlock_trace {k : Nat} (block : List (Instruction k))
    (rows final : Rows k) (hb : ShiftBlock block)
    (hrun : runRows block rows = some final) :
    markerTrace block rows = some (final, []) := by
  have hfree : ∀ op ∈ block, ∀ i, op ≠ .phaseProduct i := by
    intro op hop i he
    subst op
    have hh := hb (.phaseProduct i) hop
    simpa [ShiftOnly] using hh
  rw [Paper.BaselineContract.markerTrace_without_markers block rows hfree, hrun]
  rfl

theorem trace_cons_transfer {k : Nat} (op : Instruction k)
    (rest rest' : List (Instruction k)) (rows final : Rows k)
    (marks : List (Fin k → Int))
    (htrace : markerTrace (op :: rest) rows = some (final, marks))
    (hrest : ∀ (r f : Rows k) (m : List (Fin k → Int)),
      markerTrace rest r = some (f, m) →
      markerTrace rest' r = some (f, m)) :
    markerTrace (op :: rest') rows = some (final, marks) := by
  cases op with
  | phaseProduct i =>
      cases ht : markerTrace rest rows with
      | none => simp [markerTrace, ht] at htrace
      | some pair =>
          obtain ⟨f, m⟩ := pair
          have he : f = final ∧ rows i :: m = marks := by
            simpa [markerTrace, ht] using htrace
          rcases he with ⟨rfl, rfl⟩
          have ht' := hrest rows f m ht
          simpa [markerTrace, ht']
  | shiftL i n =>
      cases hs : rowStep (.shiftL i n) rows with
      | none => simp [markerTrace, hs] at htrace
      | some next =>
          have ht : markerTrace rest next = some (final, marks) := by
            simpa [markerTrace, hs] using htrace
          simpa [markerTrace, hs] using hrest next final marks ht
  | shiftR i n =>
      cases hs : rowStep (.shiftR i n) rows with
      | none => simp [markerTrace, hs] at htrace
      | some next =>
          have ht : markerTrace rest next = some (final, marks) := by
            simpa [markerTrace, hs] using htrace
          simpa [markerTrace, hs] using hrest next final marks ht
  | negate i =>
      cases hs : rowStep (.negate i) rows with
      | none => simp [markerTrace, hs] at htrace
      | some next =>
          have ht : markerTrace rest next = some (final, marks) := by
            simpa [markerTrace, hs] using htrace
          simpa [markerTrace, hs] using hrest next final marks ht
  | addScaled d s b n =>
      cases hs : rowStep (.addScaled d s b n) rows with
      | none => simp [markerTrace, hs] at htrace
      | some next =>
          have ht : markerTrace rest next = some (final, marks) := by
            simpa [markerTrace, hs] using htrace
          simpa [markerTrace, hs] using hrest next final marks ht

theorem compressAux_trace {k : Nat} (block rest : List (Instruction k))
    (rows final : Rows k) (marks : List (Fin k → Int))
    (hb : ShiftBlock block)
    (htrace : markerTrace (block ++ rest) rows = some (final, marks)) :
    markerTrace (compressAux block rest) rows = some (final, marks) := by
  induction rest generalizing block rows final marks with
  | nil =>
      have hr : runRows block rows = some final := by
        have hf := markerTrace_fst block rows
        have ht : markerTrace block rows = some (final, marks) := by
          simpa using htrace
        rw [ht] at hf
        simpa using hf.symm
      have hc := runRows_compressed block rows final hb hr
      have hblock := shiftBlock_trace block rows final hb hr
      have hcomp := shiftBlock_trace (compressed block) rows final
        (compressed_shift_only block) hc
      have hm : marks = [] := by
        simpa [hblock] using htrace
      subst marks
      simpa [compressAux] using hcomp
  | cons op rest ih =>
      by_cases h : isShift op = true
      · have hb' := shiftBlock_append_shift block op hb h
        have ht' : markerTrace ((block ++ [op]) ++ rest) rows =
            some (final, marks) := by
          simpa [List.append_assoc] using htrace
        simpa [compressAux, h] using ih (block ++ [op]) rows final marks hb' ht'
      · have hr : runRows (block ++ op :: rest) rows = some final := by
          have hf := markerTrace_fst (block ++ op :: rest) rows
          rw [htrace] at hf
          simpa using hf.symm
        obtain ⟨mid, hblockRun⟩ :=
          runRows_append_prefix_success block (op :: rest) hr
        have hblockTrace := shiftBlock_trace block rows mid hb hblockRun
        have hcompRun := runRows_compressed block rows mid hb hblockRun
        have hcompTrace := shiftBlock_trace (compressed block) rows mid
          (compressed_shift_only block) hcompRun
        have htail : markerTrace (op :: rest) mid = some (final, marks) := by
          rw [Paper.BaselineContract.markerTrace_append, hblockTrace] at htrace
          simpa using htrace
        have htail' : markerTrace (op :: compressAux [] rest) mid =
            some (final, marks) := by
          apply trace_cons_transfer op rest (compressAux [] rest) mid final marks htail
          intro r f m ht
          apply ih [] r f m
          · intro x hx
            simp at hx
          · simpa using ht
        simp only [compressAux, if_neg h]
        rw [Paper.BaselineContract.markerTrace_append, hcompTrace]
        simpa using htail'

theorem compressWhole_trace {k : Nat} (word : List (Instruction k))
    (rows final : Rows k) (marks : List (Fin k → Int))
    (htrace : markerTrace word rows = some (final, marks)) :
    markerTrace (compressWhole word) rows = some (final, marks) := by
  apply compressAux_trace [] word rows final marks
  · intro x hx
    simp at hx
  · simpa using htrace

end Paper.CompressionTrace
