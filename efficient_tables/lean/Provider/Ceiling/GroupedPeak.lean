import Provider.Ceiling.GroupScanPeak

/-! # Grouped Program Peaks
Proves `grouped_program_peak`, a peak bound for the grouped program at arity `k` at least two. Transfers it to the source as `groupedLiteralBaseline_peaks`.
-/

namespace Paper.F3ChargeCeiling

open Paper.Scanner Paper.SourceBridge Paper.FullDSL TableGeneration Paper.F4ChargeIntervals

theorem grouped_program_peak {k : Nat} (hk : 2 ≤ k)
    (top : Fin k) (r : Nat) :
    (Scanner.scan
      (widthWord (mapToFull
        (genOpsWithProduct (positive_of_ge_two hk) (groupedF2Points k))))
      (Scanner.fresh (Scanner.balanced top 0 r))).peak ≤
      r + 2*(k*(k-1)) + (2*k-1)*(2*k+1) := by
  let hk' := positive_of_ge_two hk
  let E := k*(k-1)
  let sourceInt := genOpsWithProduct hk' (integerPoints k)
  let sourceFrac := genOpsWithProduct hk' (fractionalPoints k)
  let wi := widthWord (mapToFull sourceInt)
  let wf := widthWord (mapToFull sourceFrac)
  have hg := grouped_words_fixed_length hk (le_refl E)
  have hwi : FixedWord (finZero hk') E wi :=
    sourceFixed_widthWord hg.1
  have hwf : FixedWord (finLast hk') E wf :=
    sourceFixed_widthWord hg.2.1
  have hscan := scan_two_fixed_peak top (finZero hk') (finLast hk')
    r E wi wf hwi hwf
  have hword : widthWord (mapToFull
      (genOpsWithProduct hk' (groupedF2Points k))) = wi ++ wf := by
    have hg' := genOpsWithProduct_append hk' (integerPoints k) (fractionalPoints k)
    change genOpsWithProduct hk' (groupedF2Points k) = sourceInt ++ sourceFrac at hg'
    rw [hg']
    simp [wi, wf, mapToFull, widthWord, List.map_append]
  rw [hword]
  have hlen : wi.length + wf.length ≤ (2*k-1)*(2*k+1) := by
    have htotal := hg.2.2
    have hh := congrArg List.length hword
    simp only [widthWord, mapToFull, List.length_map, List.length_append] at hh
    omega
  exact hscan.trans (by omega)

theorem groupedLiteralBaseline_peaks {K k : Nat}
    (hk : 2 ≤ k) (hK : k ≤ K) :
    (rawProfile (groupedLiteralBaseline k hk hK)).peakA ≤ 8*k*k ∧
    (rawProfile (groupedLiteralBaseline k hk hK)).peakB ≤ 8*k*k := by
  let t := groupedLiteralBaseline k hk hK
  have hA := grouped_program_peak hk (finLast (positive_of_ge_two hk)) 0
  have hB := grouped_program_peak hk (finLast (positive_of_ge_two hk)) (k-1)
  have hE : k*(k-1) ≤ k*k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
  have hL : (2*k-1)*(2*k+1) ≤ (2*k)*(2*k+1) :=
    Nat.mul_le_mul_right (2*k+1) (Nat.sub_le (2*k) 1)
  have hbound : 2*(k*(k-1)) + (2*k-1)*(2*k+1) ≤ 8*k*k := by
    nlinarith
  constructor
  · change (Scanner.scan
        (widthWord (mapToFull (genOpsWithProduct (positive_of_ge_two hk) (groupedF2Points k))))
        (Scanner.fresh (Scanner.balanced (finLast (positive_of_ge_two hk)) 0 0))).peak ≤
        8*k*k
    omega
  · change (Scanner.scan
        (widthWord (mapToFull (genOpsWithProduct (positive_of_ge_two hk) (groupedF2Points k))))
        (Scanner.fresh (Scanner.balanced (finLast (positive_of_ge_two hk)) 0 (k-1)))).peak -
        (k-1) ≤ 8*k*k
    omega

end Paper.F3ChargeCeiling
