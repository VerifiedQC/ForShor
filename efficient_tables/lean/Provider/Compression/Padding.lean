import Provider.Ladders.CatalogTransfer

/-!
# Padding prefixes

Defines the padding prefix `paddingPrefix` that raises scanner peaks, and the
padded F2 source `paddedF2Source t A B`. It proves the prefix leaves the
rows unchanged (`paddingPrefix_runRows`) and determines the padded source's
peaks and charge (`paddedF2Source_peakA`, `paddedF2Source_peakB`,
`paddedF2Source_charge`).
-/

namespace Paper.PrefixPaddingStage

open Paper.FullDSL
open Paper.SourceBridge
open Paper.F2CatalogTransfer
open TableGeneration

def paddingPrefix {k : Nat} (zero top : Fin k) (A B : Nat) : Prog k :=
  [.shiftL zero A, .shiftR zero A, .shiftL top B, .shiftR top B]

lemma shiftL_then_shiftR {k : Nat} (rows : Rows k) (i : Fin k) (n : Nat) :
    ∃ mid, rowStep (.shiftL i n) rows = some mid ∧
      rowStep (.shiftR i n) mid = some rows := by
  let mid := rows.updateRow i (fun j => rows i j * (2 : Int)^n)
  have hdiv : ∀ j : Fin k, mid i j % (2 : Int)^n = 0 := by
    intro j
    simp [mid, Matrix.updateRow_self]
  have hp : (2 : Int)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq : mid.updateRow i (fun j => mid i j / (2 : Int)^n) = rows := by
    apply Matrix.ext
    intro r c
    by_cases hr : r = i
    · subst r
      simp only [Matrix.updateRow_self]
      simp [mid, Int.mul_ediv_cancel_left _ hp]
    · simp [mid, Matrix.updateRow, hr]
  refine ⟨mid, ?_, ?_⟩
  · simp [mid, rowStep]
  · simp [rowStep, hdiv, heq]

lemma paddingPrefix_runRows {k : Nat} (rows : Rows k) (zero top : Fin k) (A B : Nat) :
    runRows (mapToFull (paddingPrefix zero top A B)) rows = some rows := by
  obtain ⟨mid0, hL0, hR0⟩ := shiftL_then_shiftR rows zero A
  obtain ⟨midT, hLT, hRT⟩ := shiftL_then_shiftR rows top B
  simp [paddingPrefix, mapToFull, toFull, runRows, hL0, hR0, hLT, hRT]

lemma markerTrace_append_noPhase {k : Nat}
    (pre suffix : List (Instruction k)) (rows final : Rows k)
    (hnomark : ∀ op ∈ pre, ∀ i : Fin k, op ≠ .phaseProduct i)
    (hrun : runRows pre rows = some final) :
    markerTrace (pre ++ suffix) rows = markerTrace suffix final := by
  induction pre generalizing rows with
  | nil =>
      cases hrun
      rfl
  | cons op pre ih =>
      obtain ⟨mid, hop, hrest⟩ := runRows_cons_success hrun
      have hnomark' : ∀ op ∈ pre, ∀ i : Fin k, op ≠ .phaseProduct i := by
        intro x hx i
        exact hnomark x (by simp [hx]) i
      cases op with
      | phaseProduct i =>
          have hfalse := hnomark (.phaseProduct i) (by simp) i
          exact False.elim (hfalse rfl)
      | shiftL i n =>
          simp only [List.cons_append, markerTrace]
          rw [hop]
          exact ih mid hnomark' hrest
      | shiftR i n =>
          simp only [List.cons_append, markerTrace]
          rw [hop]
          exact ih mid hnomark' hrest
      | negate i =>
          simp only [List.cons_append, markerTrace]
          rw [hop]
          exact ih mid hnomark' hrest
      | addScaled d s neg n =>
          simp only [List.cons_append, markerTrace]
          rw [hop]
          exact ih mid hnomark' hrest

def sourceProfileRaw {K : Nat} (t : F2Source K) : Planner.Profile :=
  SourceBridge.sourceProfile
    (TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk))
    t.source.program

def paddedF2Source {K : Nat} (t : F2Source K) (A B : Nat) : F2Source K := by
  let zero := TableGeneration.finZero (TableGeneration.positive_of_ge_two t.source.hk)
  let top := TableGeneration.finLast (TableGeneration.positive_of_ge_two t.source.hk)
  have hsafe : safeProg? (paddingPrefix zero top A B ++ t.source.program) = true := by
    apply (Paper.SourceBridge.safeProg_iff _).2
    intro op hop
    rcases List.mem_append.mp hop with hpref | htail
    · simp [paddingPrefix] at hpref
      rcases hpref with rfl | rfl | rfl | rfl <;> simp [TableGeneration.Prog.OpOK]
    · exact (Paper.SourceBridge.safeProg_iff _).1 t.safe.safe_add op htail
  have htraceOrig :=
    (Paper.SourceBridge.source_contract_iff_trace
      (TableGeneration.positive_of_ge_two t.source.hk)
      TableGeneration.State.start_state t.source.program (List.ofFn t.points)).mp t.safe
  have hident : Paper.FullDSL.identity t.source.k = TableGeneration.State.start_state := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Paper.FullDSL.identity, TableGeneration.State.start_state, Matrix.one_apply]
    · have h' : j ≠ i := fun hji => h (hji.symm)
      simp [Paper.FullDSL.identity, TableGeneration.State.start_state, Matrix.one_apply, h, h']
  have hrun := paddingPrefix_runRows
    (Paper.FullDSL.identity t.source.k) zero top A B
  have hrunStart : runRows (mapToFull (paddingPrefix zero top A B)) State.start_state = some State.start_state := by
    rw [← hident]
    exact hrun
  have hnomark :
      ∀ op ∈ SourceBridge.mapToFull (paddingPrefix zero top A B),
        ∀ i : Fin t.source.k, op ≠ Paper.FullDSL.Instruction.phaseProduct i := by
    intro op hop i
    simp [paddingPrefix, SourceBridge.mapToFull, SourceBridge.toFull] at hop
    rcases hop with rfl | rfl | rfl | rfl <;> simp
  have htracePad :
      SourceBridge.markerTrace
        (SourceBridge.mapToFull (paddingPrefix zero top A B ++ t.source.program))
        TableGeneration.State.start_state =
      some (TableGeneration.State.start_state,
        (List.ofFn t.points).map TableGeneration.expectedRow) := by
    have happend := markerTrace_append_noPhase
      (SourceBridge.mapToFull (paddingPrefix zero top A B))
      (SourceBridge.mapToFull t.source.program)
      TableGeneration.State.start_state TableGeneration.State.start_state hnomark hrunStart
    exact happend.trans htraceOrig.2
  have hsafePadded :
      ProgConsumesPtsSafe (positive_of_ge_two t.source.hk)
        State.start_state (paddingPrefix zero top A B ++ t.source.program)
        (List.ofFn t.points) :=
    (Paper.SourceBridge.source_contract_iff_trace
      (positive_of_ge_two t.source.hk) State.start_state
      (paddingPrefix zero top A B ++ t.source.program) (List.ofFn t.points)).mpr
        ⟨hsafe, htracePad⟩
  exact ⟨{ t.source with program := paddingPrefix zero top A B ++ t.source.program }, t.cap, t.points, hsafePadded, t.literalF2⟩

lemma maximum_twoRows {k : Nat} (zero top : Fin k) (A C : Nat) (hzt : zero ≠ top) :
    Scanner.maximum (fun i => if i = zero then A else if i = top then C else 0) =
      max A C := by
  unfold Scanner.maximum
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    by_cases h0 : i = zero
    · subst i
      simp
    · by_cases ht : i = top
      · subst i
        simp [hzt.symm]
      · simp [h0, ht]
  · apply max_le
    · have h := (Finset.le_sup (s := Finset.univ) (f := fun i => if i = zero then A else if i = top then C else 0) (Finset.mem_univ zero) :
          (if zero = zero then A else if zero = top then C else 0) ≤
            Finset.univ.sup (fun i => if i = zero then A else if i = top then C else 0))
      simpa [hzt] using h
    · have h := (Finset.le_sup (s := Finset.univ) (f := fun i => if i = zero then A else if i = top then C else 0) (Finset.mem_univ top) :
          (if top = zero then A else if top = top then C else 0) ≤
            Finset.univ.sup (fun i => if i = zero then A else if i = top then C else 0))
      simpa [hzt.symm] using h

lemma scan_paddingPrefix {k : Nat} (top zero : Fin k) (A B r : Nat)
    (hzt : zero ≠ top) :
    Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull (paddingPrefix zero top A B)))
      (Scanner.fresh (Scanner.balanced top 0 r)) =
      ⟨Scanner.balanced top 0 r, max A (r + B)⟩ := by
  let w0 := Scanner.balanced top 0 r
  let w1 : Scanner.Widths k := fun i => if i = zero then A else w0 i
  let w3 := Scanner.balanced top 0 (r+B)
  have hmax0 : Scanner.maximum w0 = r := by
    simpa [w0] using Paper.Profile.maximum_balanced top 0 r
  have hmax1 : Scanner.maximum w1 = max A r := by
    have hw : w1 = (fun i => if i = zero then A else if i = top then r else 0) := by
      funext i
      by_cases h0 : i = zero
      · subst i
        simp [w1]
      · by_cases ht : i = top
        · subst i
          simp [w1, w0, Scanner.balanced, hzt]
        · simp [w1, w0, Scanner.balanced, h0, ht]
    rw [hw]
    exact maximum_twoRows zero top A r hzt
  have hmax3 : Scanner.maximum w3 = r+B := by
    simpa [w3] using Paper.Profile.maximum_balanced top 0 (r+B)
  have hz0 : w0 zero = 0 := by simp [w0, Scanner.balanced, hzt]
  have ht0 : w0 top = r := by simp [w0, Scanner.balanced]
  have hstep1 : Scanner.step (.shiftL zero A) w0 = w1 := by
    funext i
    by_cases h0 : i = zero
    · subst i
      simp [Scanner.step, w1, hz0]
    · simp [Scanner.step, w1, h0]
  have hstep2 : Scanner.step (.shiftR zero A) w1 = w0 := by
    funext i
    by_cases h0 : i = zero
    · subst i
      simp [Scanner.step, w1, hz0]
    · simp [Scanner.step, w1, w0, h0]
  have hstep3 : Scanner.step (.shiftL top B) w0 = w3 := by
    funext i
    by_cases ht : i = top
    · subst i
      simp [Scanner.step, w0, w3, Scanner.balanced]
    · simp [Scanner.step, w0, w3, Scanner.balanced, ht]
  have hstep4 : Scanner.step (.shiftR top B) w3 = w0 := by
    funext i
    by_cases ht : i = top
    · subst i
      simp [Scanner.step, w0, w3, Scanner.balanced]
    · simp [Scanner.step, w0, w3, Scanner.balanced, ht]
  let s1 : Scanner.State k := ⟨w1, max r (max A r)⟩
  let s2 : Scanner.State k := ⟨w0, max s1.peak r⟩
  let s3 : Scanner.State k := ⟨w3, max s2.peak (r+B)⟩
  let s4 : Scanner.State k := ⟨w0, max s3.peak r⟩
  have hadv1 : Scanner.advance (.shiftL zero A) (Scanner.fresh w0) = s1 := by
    simp [Scanner.advance, Scanner.fresh, s1, hstep1, hmax0, hmax1]
  have hadv2 : Scanner.advance (.shiftR zero A) s1 = s2 := by
    simp [Scanner.advance, s1, s2, hstep2, hmax0]
  have hadv3 : Scanner.advance (.shiftL top B) s2 = s3 := by
    simp [Scanner.advance, s2, s3, hstep3, hmax3]
  have hadv4 : Scanner.advance (.shiftR top B) s3 = s4 := by
    simp [Scanner.advance, s3, s4, hstep4, hmax0]
  have hword :
      FullDSL.widthWord (SourceBridge.mapToFull (paddingPrefix zero top A B)) =
        [.shiftL zero A, .shiftR zero A, .shiftL top B, .shiftR top B] := by
    rfl
  rw [hword]
  simp only [Scanner.scan]
  rw [hadv1, hadv2, hadv3, hadv4]
  apply congrArg (fun p : Nat => (⟨w0, p⟩ : Scanner.State k))
  dsimp [s1, s2, s3, s4]
  omega

lemma scan_peak_raise {k : Nat} (word : List (Scanner.Op k))
    (w : Scanner.Widths k) (low high : Nat) (hle : low ≤ high) :
    (Scanner.scan word ⟨w, high⟩).peak =
      max high (Scanner.scan word ⟨w, low⟩).peak := by
  induction word generalizing w low high with
  | nil => simp [Scanner.scan, hle]
  | cons op rest ih =>
      simp only [Scanner.scan]
      simp only [Scanner.advance]
      rw [ih (Scanner.step op w)
        (max low (Scanner.maximum (Scanner.step op w)))
        (max high (Scanner.maximum (Scanner.step op w)))
        (max_le_max_right _ hle)]
      have hbound : Scanner.maximum (Scanner.step op w) ≤
          (Scanner.scan rest ⟨Scanner.step op w,
            max low (Scanner.maximum (Scanner.step op w))⟩).peak :=
        le_trans (le_max_right low _) (Scanner.incoming_peak_le_scan rest
          ⟨Scanner.step op w, max low (Scanner.maximum (Scanner.step op w))⟩)
      simp only [max_assoc, Nat.max_eq_right hbound]

lemma scan_append_peak_from_prefix {k : Nat}
    (pre tail : List (Scanner.Op k)) (w : Scanner.Widths k)
    (incoming prefixPeak : Nat) (hpeak : incoming ≤ prefixPeak)
    (hpre : Scanner.scan pre ⟨w, incoming⟩ = ⟨w, prefixPeak⟩) :
    (Scanner.scan (pre ++ tail) ⟨w, incoming⟩).peak =
      max prefixPeak (Scanner.scan tail ⟨w, incoming⟩).peak := by
  rw [Scanner.scan_append, hpre]
  exact scan_peak_raise tail w incoming prefixPeak hpeak

lemma paddingPrefix_peakA_suffix {k : Nat} (top zero : Fin k)
    (A B : Nat) (tail : List (Scanner.Op k)) (hzt : zero ≠ top)
    (hBA : B ≤ A)
    (hold : (Scanner.scan tail (Scanner.fresh (Scanner.balanced top 0 0))).peak ≤ A) :
    (Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull (paddingPrefix zero top A B)) ++ tail)
      (Scanner.fresh (Scanner.balanced top 0 0))).peak = A := by
  let w := Scanner.balanced top 0 0
  have hfresh : Scanner.fresh w = ⟨w, 0⟩ := by
    simp [w, Scanner.fresh, Paper.Profile.maximum_balanced]
  have hpref : Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull (paddingPrefix zero top A B)))
      ⟨w, 0⟩ = ⟨w, A⟩ := by
    rw [← hfresh]
    simpa [w, hBA] using scan_paddingPrefix top zero A B 0 hzt
  have htail : (Scanner.scan tail ⟨w, 0⟩).peak ≤ A := by
    simpa [w, hfresh] using hold
  rw [hfresh]
  rw [scan_append_peak_from_prefix _ _ w 0 A (Nat.zero_le A) hpref]
  exact Nat.max_eq_left htail

lemma paddingPrefix_peak_suffix {k : Nat} (top zero : Fin k)
    (r A B : Nat) (tail : List (Scanner.Op k)) (hzt : zero ≠ top)
    (hcanon : A ≤ r + B)
    (hold : (Scanner.scan tail (Scanner.fresh (Scanner.balanced top 0 r))).peak ≤ r + B) :
    (Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull (paddingPrefix zero top A B)) ++ tail)
      (Scanner.fresh (Scanner.balanced top 0 r))).peak = r + B := by
  let w := Scanner.balanced top 0 r
  have hfresh : Scanner.fresh w = ⟨w, r⟩ := by
    simp [w, Scanner.fresh, Paper.Profile.maximum_balanced]
  have hpref : Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull (paddingPrefix zero top A B)))
      ⟨w, r⟩ = ⟨w, r + B⟩ := by
    rw [← hfresh]
    simpa [w, hcanon] using scan_paddingPrefix top zero A B r hzt
  have htail : (Scanner.scan tail ⟨w, r⟩).peak ≤ r + B := by
    simpa [w, hfresh] using hold
  rw [hfresh]
  rw [scan_append_peak_from_prefix _ _ w r (r+B) (Nat.le_add_right r B) hpref]
  exact Nat.max_eq_left htail

lemma paddedF2Source_peakA {K : Nat} (t : F2Source K) (A B : Nat)
    (hBA : B ≤ A) (hcap : (sourceProfileRaw t).peakA ≤ A) :
    (sourceProfileRaw (paddedF2Source t A B)).peakA = A := by
  let hkpos := TableGeneration.positive_of_ge_two t.source.hk
  let top := TableGeneration.finLast hkpos
  let zero := TableGeneration.finZero hkpos
  have hzt : zero ≠ top := by
    intro h
    have hv := congrArg Fin.val h
    have hk := t.source.hk
    simp [zero, top, TableGeneration.finZero, TableGeneration.finLast] at hv
    omega
  have hcap' : (Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull t.source.program))
      (Scanner.fresh (Scanner.balanced top 0 0))).peak ≤ A := by
    change (Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull t.source.program))
      (Scanner.fresh (Scanner.balanced top 0 0))).peak ≤ A at hcap
    exact hcap
  unfold sourceProfileRaw
  change (Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull
        (paddingPrefix zero top A B ++ t.source.program)))
      (Scanner.fresh (Scanner.balanced top 0 0))).peak = A
  exact paddingPrefix_peakA_suffix top zero A B
    (FullDSL.widthWord (SourceBridge.mapToFull t.source.program)) hzt hBA hcap'

lemma paddedF2Source_peakB {K : Nat} (t : F2Source K) (A B : Nat)
    (hcanon : A ≤ B + (t.source.k - 1)) (hcap : (sourceProfileRaw t).peakB ≤ B) :
    (sourceProfileRaw (paddedF2Source t A B)).peakB = B := by
  let hkpos := TableGeneration.positive_of_ge_two t.source.hk
  let top := TableGeneration.finLast hkpos
  let zero := TableGeneration.finZero hkpos
  let r := t.source.k - 1
  have hzt : zero ≠ top := by
    intro h
    have hv := congrArg Fin.val h
    have hk := t.source.hk
    simp [zero, top, TableGeneration.finZero, TableGeneration.finLast] at hv
    omega
  have hcap' :
      (Scanner.scan
        (FullDSL.widthWord (SourceBridge.mapToFull t.source.program))
        (Scanner.fresh (Scanner.balanced top 0 r))).peak - r ≤ B := by
    unfold sourceProfileRaw SourceBridge.sourceProfile at hcap
    change (Scanner.scan
        (FullDSL.widthWord (SourceBridge.mapToFull t.source.program))
        (Scanner.fresh (Scanner.balanced top 0 (t.source.k - 1)))).peak -
          (t.source.k - 1) ≤ B at hcap
    simpa [r] using hcap
  have hold :
      (Scanner.scan
        (FullDSL.widthWord (SourceBridge.mapToFull t.source.program))
        (Scanner.fresh (Scanner.balanced top 0 r))).peak ≤ r + B := by
    omega
  have htotal :
      (Scanner.scan
        (FullDSL.widthWord (SourceBridge.mapToFull
          (paddingPrefix zero top A B ++ t.source.program)))
        (Scanner.fresh (Scanner.balanced top 0 r))).peak = r + B := by
    exact paddingPrefix_peak_suffix top zero r A B
      (FullDSL.widthWord (SourceBridge.mapToFull t.source.program)) hzt
      (by simpa [r, Nat.add_comm] using hcanon) hold
  unfold sourceProfileRaw SourceBridge.sourceProfile
  change (Scanner.scan
      (FullDSL.widthWord (SourceBridge.mapToFull
        (paddingPrefix zero top A B ++ t.source.program)))
      (Scanner.fresh (Scanner.balanced top 0 (t.source.k - 1)))).peak -
        (t.source.k - 1) = B
  simpa [r] using congrArg (fun n : Nat => n - r) htotal

lemma paddedF2Source_charge {K : Nat} (t : F2Source K) (A B : Nat) :
    (sourceProfileRaw (paddedF2Source t A B)).charge = (sourceProfileRaw t).charge := by
  unfold sourceProfileRaw SourceBridge.sourceProfile
  simp [paddedF2Source, paddingPrefix, FullDSL.wordCharge, FullDSL.charge,
    SourceBridge.mapToFull, SourceBridge.toFull, List.map_append, List.sum_append]

lemma paddedF2Source_arity {K : Nat} (t : F2Source K) (A B : Nat) :
    (paddedF2Source t A B).source.k = t.source.k := rfl

lemma paddedF2Source_exactPeaks {K : Nat} (t : F2Source K) (A B : Nat)
    (hBA : B ≤ A) (hcanon : A ≤ B + (t.source.k - 1))
    (hcapA : (sourceProfileRaw t).peakA ≤ A)
    (hcapB : (sourceProfileRaw t).peakB ≤ B) :
    (sourceProfileRaw (paddedF2Source t A B)).peakA = A ∧
      (sourceProfileRaw (paddedF2Source t A B)).peakB = B := by
  exact ⟨paddedF2Source_peakA t A B hBA hcapA,
    paddedF2Source_peakB t A B hcanon hcapB⟩

lemma paddedF2Source_childWidth {K : Nat} (t : F2Source K) (A B w : Nat)
    (hBA : B ≤ A) (hcanon : A ≤ B + (t.source.k - 1))
    (hcapA : (sourceProfileRaw t).peakA ≤ A)
    (hcapB : (sourceProfileRaw t).peakB ≤ B) :
    Planner.childWidth t.source.k (sourceProfileRaw (paddedF2Source t A B)) w =
      w / t.source.k + 1 + max A (B + w % t.source.k) := by
  obtain ⟨hA, hB⟩ := paddedF2Source_exactPeaks t A B hBA hcanon hcapA hcapB
  simp [Planner.childWidth, hA, hB]
end Paper.PrefixPaddingStage
