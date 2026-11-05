import Model.Interpreter.ValueBounds

/-!
# Value bounds for executed prefixes

Extends the value bounds to every successfully executed prefix of a word. Proves `successful_prefix_below_full_peak` for registers and markers, and `source_successful_prefix_signed_bound`, the same statement for the original balanced source scanner.
-/

namespace Paper.ValueBounds

/-- Every register reached by a successfully executed pre, and every marker
observed in that pre, fits below the scanner peak of the *whole* word.
Success is required only for the pre; the suffix need not execute. -/
theorem successful_prefix_below_full_peak {k : Nat}
    (pre suffix : List (Paper.FullDSL.Instruction k))
    (w : Paper.Scanner.Widths k)
    (v mid : Paper.ValueSemantics.Values k) (marks : List Int)
    (hinit : Fits w v)
    (hprefix : Paper.ValueSemantics.valueTrace pre v = some (mid, marks)) :
    (∀ i, (mid i).natAbs <
      2 ^ (Paper.Scanner.scan (Paper.FullDSL.widthWord (pre ++ suffix))
        (Paper.Scanner.fresh w)).peak) ∧
    (∀ z ∈ marks, z.natAbs <
      2 ^ (Paper.Scanner.scan (Paper.FullDSL.widthWord (pre ++ suffix))
        (Paper.Scanner.fresh w)).peak) := by
  let s := Paper.Scanner.scan (Paper.FullDSL.widthWord pre) (Paper.Scanner.fresh w)
  have hb := valueTrace_fits pre w v mid marks hinit hprefix
  have hcurrent : ∀ i, s.widths i ≤ s.peak :=
    scan_width_le_peak (Paper.FullDSL.widthWord pre) (Paper.Scanner.fresh w)
      (fun i => width_le_maximum w i)
  have hle : s.peak ≤
      (Paper.Scanner.scan (Paper.FullDSL.widthWord (pre ++ suffix))
        (Paper.Scanner.fresh w)).peak := by
    simp only [Paper.FullDSL.widthWord, List.map_append,
      Paper.Scanner.scan_append]
    exact Paper.Scanner.incoming_peak_le_scan _ s
  have hpow : 2 ^ s.peak ≤
      2 ^ (Paper.Scanner.scan (Paper.FullDSL.widthWord (pre ++ suffix))
        (Paper.Scanner.fresh w)).peak :=
    Nat.pow_le_pow_right (by decide) hle
  constructor
  · intro i
    have hlocal : (mid i).natAbs < 2 ^ s.peak :=
      lt_of_lt_of_le (hb.1 i)
        (Nat.pow_le_pow_right (by decide) (hcurrent i))
    exact lt_of_lt_of_le hlocal hpow
  · intro z hz
    exact lt_of_lt_of_le (hb.2 z hz) hpow

/-- The original balanced source scanner supplies the same whole-word peak.
The starting limb bounds are an explicit hypothesis. -/
theorem source_successful_prefix_signed_bound {k : Nat} (width : Nat)
    (pre suffix : TableGeneration.Prog k)
    (x mid : Paper.ValueSemantics.Values k) (marks : List Int)
    (hinit : Fits (Paper.ArrayBridge.literalSourceSplit width k) x)
    (hprefix : Paper.ValueSemantics.valueTrace
      (Paper.SourceBridge.mapToFull pre) x = some (mid, marks)) :
    (∀ i, (mid i).natAbs <
      2 ^ (TableGeneration.RecursiveCost.nextBalancedSignedWidth
        width (pre ++ suffix) - 1)) ∧
    (∀ z ∈ marks, z.natAbs <
      2 ^ (TableGeneration.RecursiveCost.nextBalancedSignedWidth
        width (pre ++ suffix) - 1)) := by
  have hb := successful_prefix_below_full_peak
    (Paper.SourceBridge.mapToFull pre)
    (Paper.SourceBridge.mapToFull suffix)
    (Paper.ArrayBridge.literalSourceSplit width k) x mid marks hinit hprefix
  have he : Paper.SourceBridge.mapToFull (pre ++ suffix) =
      Paper.SourceBridge.mapToFull pre ++ Paper.SourceBridge.mapToFull suffix := by
    simp [Paper.SourceBridge.mapToFull]
  rw [Paper.ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord, he]
  simpa using hb

end Paper.ValueBounds
