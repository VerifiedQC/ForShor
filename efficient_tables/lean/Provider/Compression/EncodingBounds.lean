import Provider.Compression.F2Witness

/-!
# Exponent and coefficient bounds after compression

Defines `exponentWithin` and shows scanning a word keeps exponents within a
bound (`scan_exponents`), specialized to the F2 source and its padded version
(`f2_exponents_within_peakA`, `paddedF2_exponents_within_A`). It also bounds
prefix coefficients (`prefix_coefficient_bound`,
`paddedF2_every_prefix_coefficients`).
-/

namespace Paper.CompressionEncoding

open Paper.Scanner Paper.FullDSL Paper.SourceBridge
open Paper.F2CatalogTransfer Paper.PrefixPaddingStage Paper.CompressionF2

def exponentWithin {k : Nat} : Op k → Nat → Prop
  | .shiftL _ n, a => n ≤ a
  | .shiftR _ n, a => n ≤ a
  | .addScaled _ _ n, a => n < a
  | _, _ => True

theorem exponentWithin_mono {k : Nat} (op : Op k) {a b : Nat}
    (h : a ≤ b) (ha : exponentWithin op a) : exponentWithin op b := by
  cases op <;> simp_all [exponentWithin] <;> omega

theorem step_exponentWithin {k : Nat} (op : Op k) (s : State k)
    (hvalid : ∀ i, s.widths i ≤ s.peak)
    (hno : stepNoUnderflow op s.widths) :
    exponentWithin op (advance op s).peak := by
  cases op with
  | shiftL i n =>
      have hw : (step (.shiftL i n) s.widths) i ≤
          (advance (.shiftL i n) s).peak := by
        exact le_trans (Finset.le_sup (f := step (.shiftL i n) s.widths)
          (Finset.mem_univ i)) (le_max_right _ _)
      simp [step] at hw
      simp [exponentWithin]
      omega
  | shiftR i n =>
      have hn : n ≤ s.widths i := hno
      exact le_trans hn (le_trans (hvalid i) (le_max_left _ _))
  | addScaled d src n =>
      have hw : (step (.addScaled d src n) s.widths) d ≤
          (advance (.addScaled d src n) s).peak := by
        exact le_trans (Finset.le_sup (f := step (.addScaled d src n) s.widths)
          (Finset.mem_univ d)) (le_max_right _ _)
      simp [step] at hw
      simp [exponentWithin]
      omega
  | negate i => trivial
  | marker => trivial

theorem scan_exponents {k : Nat} (word : List (Op k)) (s : State k)
    (hvalid : ∀ i, s.widths i ≤ s.peak)
    (hno : noUnderflow word s.widths) :
    ∀ op ∈ word, exponentWithin op (scan word s).peak := by
  induction word generalizing s with
  | nil => simp
  | cons head tail ih =>
      intro op hop
      have hstep : exponentWithin head (advance head s).peak :=
        step_exponentWithin head s hvalid hno.1
      have hvalid' : ∀ i, (advance head s).widths i ≤ (advance head s).peak := by
        intro i
        exact le_trans (Finset.le_sup (f := step head s.widths) (Finset.mem_univ i))
          (le_max_right _ _)
      have htail := ih (advance head s) hvalid' hno.2
      rcases List.mem_cons.mp hop with rfl | hrest
      · exact exponentWithin_mono op (incoming_peak_le_scan tail (advance op s)) hstep
      · exact htail op hrest

private theorem f2_run_success {K : Nat} (t : F2Source K) :
    TableGeneration.run? t.source.program TableGeneration.State.start_state =
      some TableGeneration.State.start_state := by
  have h := (source_contract_iff_trace
    (TableGeneration.positive_of_ge_two t.source.hk)
    TableGeneration.State.start_state t.source.program (List.ofFn t.points)).1 t.safe
  have hr : runRows (mapToFull t.source.program)
      TableGeneration.State.start_state = some TableGeneration.State.start_state := by
    rw [← markerTrace_fst]
    simp [h.2]
  simpa [runRows_eq_run_of_safe t.source.program _ h.1] using hr

theorem f2_exponents_within_peakA {K : Nat} (t : F2Source K) :
    ∀ op ∈ t.source.program,
      exponentWithin (widthOp (toFull op)) (sourceProfileRaw t).peakA := by
  let top := TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk)
  let s := fresh (balanced top 0 0)
  have hvalid : ∀ i, s.widths i ≤ s.peak := by
    intro i
    exact Finset.le_sup (f := balanced top 0 0) (Finset.mem_univ i)
  have hno := original_safe_noUnderflow s.widths t.source.program
    TableGeneration.State.start_state t.safe.safe_add (f2_run_success t)
  have hall := scan_exponents (widthWord (mapToFull t.source.program))
    s hvalid hno
  intro op hop
  have hh := hall (widthOp (toFull op)) (by
    simp [widthWord, mapToFull, List.mem_map]
    exact ⟨op, hop, rfl⟩)
  simpa [sourceProfileRaw, sourceProfile, top, s] using hh

theorem paddedF2_exponents_within_A {K : Nat} (t : F2Source K) (A B : Nat)
    (hBA : B ≤ A) (hcanon : A ≤ B + (t.source.k - 1))
    (hA : (sourceProfileRaw t).peakA ≤ A)
    (hB : (sourceProfileRaw t).peakB ≤ B) :
    ∀ op ∈ (paddedCompressedF2 t A B).source.program,
      exponentWithin (widthOp (toFull op)) A := by
  have hpeak := (paddedCompressedF2_exactPeaks t A B hBA hcanon hA hB).1
  intro op hop
  simpa [hpeak] using f2_exponents_within_peakA (paddedCompressedF2 t A B) op hop

theorem prefix_coefficient_bound {k : Nat} (pre : List (Instruction k))
    (rows : Rows k) (A : Nat)
    (hrun : runRows pre (identity k) = some rows)
    (hpeak : (scan (widthWord pre) (fresh (fun _ => 0))).peak ≤ A) :
    ∀ i j, (rows i j).natAbs ≤ 2 ^ A := by
  have hb := (Paper.RowMass.runRows_mass_noUnderflow (fun _ : Fin k => 0)
    pre rows hrun).2
  intro i j
  have helem : (rows i j).natAbs ≤
      Paper.RowMass.weightedMass (fun _ : Fin k => 0) (rows i) := by
    have hs := Finset.single_le_sum
      (f := fun x : Fin k => (rows i x).natAbs * 2 ^ (0 : Nat))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simpa [Paper.RowMass.weightedMass] using hs
  have hwidth : (Paper.Scanner.runWidths (widthWord pre) (fun _ => 0)) i ≤
      (scan (widthWord pre) (fresh (fun _ => 0))).peak := by
    have h := Paper.ScannerPotential.fresh_width_le_peak
      (widthWord pre) (fun _ : Fin k => 0) i
    simpa [scan_widths_eq_runWidths] using h
  calc
    (rows i j).natAbs ≤ Paper.RowMass.weightedMass (fun _ : Fin k => 0) (rows i) := helem
    _ ≤ 2 ^ (Paper.Scanner.runWidths (widthWord pre) (fun _ => 0)) i := hb i
    _ ≤ 2 ^ (scan (widthWord pre) (fresh (fun _ => 0))).peak :=
      Nat.pow_le_pow_right (by decide) hwidth
    _ ≤ 2 ^ A := Nat.pow_le_pow_right (by decide) hpeak

theorem paddedF2_prefix_coefficient_bound {K : Nat} (t : F2Source K)
    (A B : Nat) (hBA : B ≤ A) (hcanon : A ≤ B + (t.source.k - 1))
    (hA : (sourceProfileRaw t).peakA ≤ A)
    (hB : (sourceProfileRaw t).peakB ≤ B)
    (pre suffix : List (Instruction t.source.k))
    (rows : Rows t.source.k)
    (hsplit : pre ++ suffix = mapToFull (paddedCompressedF2 t A B).source.program)
    (hrun : runRows pre (identity t.source.k) = some rows) :
    ∀ i j, (rows i j).natAbs ≤ 2 ^ A := by
  have hfull := (paddedCompressedF2_exactPeaks t A B hBA hcanon hA hB).1
  let top := TableGeneration.finLast
    (TableGeneration.positive_of_ge_two (paddedCompressedF2 t A B).source.hk)
  have hzero : balanced top 0 0 = (fun _ : Fin t.source.k => 0) := by
    funext i
    simp [balanced]
  have hfull' : (scan (widthWord (mapToFull
      (paddedCompressedF2 t A B).source.program)) (fresh (fun _ => 0))).peak = A := by
    change (scan (widthWord (mapToFull
      (paddedCompressedF2 t A B).source.program))
      (fresh (balanced top 0 0))).peak = A at hfull
    simpa only [hzero] using hfull
  have hprefix : (scan (widthWord pre) (fresh (fun _ => 0))).peak ≤ A := by
    have hmono := incoming_peak_le_scan (widthWord suffix)
      (scan (widthWord pre) (fresh (fun _ => 0)))
    have hjoin : scan (widthWord (pre ++ suffix)) (fresh (fun _ => 0)) =
        scan (widthWord suffix) (scan (widthWord pre) (fresh (fun _ => 0))) := by
      simpa [widthWord, List.map_append] using
        scan_append (widthWord pre) (widthWord suffix) (fresh (fun _ => 0))
    rw [← hjoin, hsplit] at hmono
    exact le_trans hmono hfull'.le
  exact prefix_coefficient_bound pre rows A hrun hprefix

theorem paddedF2_every_prefix_coefficients {K : Nat} (t : F2Source K)
    (A B : Nat) (hBA : B ≤ A) (hcanon : A ≤ B + (t.source.k - 1))
    (hA : (sourceProfileRaw t).peakA ≤ A)
    (hB : (sourceProfileRaw t).peakB ≤ B)
    (pre suffix : List (Instruction t.source.k))
    (hsplit : pre ++ suffix = mapToFull (paddedCompressedF2 t A B).source.program) :
    ∃ rows : Rows t.source.k,
      runRows pre (identity t.source.k) = some rows ∧
        ∀ i j, (rows i j).natAbs ≤ 2 ^ A := by
  let u := paddedCompressedF2 t A B
  have hfull : runRows (mapToFull u.source.program) (identity u.source.k) =
      some TableGeneration.State.start_state := by
    rw [runRows_from_start_of_safe u.source.program u.safe.safe_add]
    exact f2_run_success u
  have hs : runRows (pre ++ suffix) (identity t.source.k) =
      some TableGeneration.State.start_state := by
    simpa [hsplit, u] using hfull
  obtain ⟨rows, hr⟩ := runRows_append_prefix_success pre suffix hs
  exact ⟨rows, hr, paddedF2_prefix_coefficient_bound t A B hBA hcanon hA hB
    pre suffix rows hsplit hr⟩

end Paper.CompressionEncoding
