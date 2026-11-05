import Provider.Compression.Block

/-!
# Whole-program compression

Compresses an entire instruction word by flushing the accumulated shift block
at every paid operation or marker: `compressAux` and `compressWhole`. It
proves the length and charge of the result (`compressWhole_length`,
`compressWhole_charge`) and that the compressed word runs to the same rows
(`compressAux_runRows`), together with supporting no-underflow and peak lemmas.
-/

namespace Paper.WholeCompression

open Paper.FullDSL Paper.Scanner Paper.ShiftCompression

def isShift {k : Nat} : Instruction k → Bool
  | .shiftL _ _ => true
  | .shiftR _ _ => true
  | _ => false

theorem shiftOnly_iff_isShift {k : Nat} (op : Instruction k) :
    ShiftOnly op ↔ isShift op = true := by
  cases op <;> simp [ShiftOnly, isShift]

def separatorCount {k : Nat} : List (Instruction k) → Nat
  | [] => 0
  | op :: rest => (if isShift op then 0 else 1) + separatorCount rest

/-- Flush the accumulated shift block at every paid operation or marker. -/
def compressAux {k : Nat} (block : List (Instruction k)) :
    List (Instruction k) → List (Instruction k)
  | [] => compressed block
  | op :: rest =>
      if isShift op then compressAux (block ++ [op]) rest
      else compressed block ++ op :: compressAux [] rest

def compressWhole {k : Nat} (word : List (Instruction k)) :
    List (Instruction k) := compressAux [] word

theorem compressAux_length {k : Nat} (block rest : List (Instruction k)) :
    (compressAux block rest).length =
      (k + 1) * separatorCount rest + k := by
  induction rest generalizing block with
  | nil => simp [compressAux, separatorCount, compressed_length]
  | cons op rest ih =>
      by_cases h : isShift op = true
      · simp [compressAux, separatorCount, h, ih]
      · simp [compressAux, separatorCount, h, ih, compressed_length, mul_add]
        omega

theorem compressWhole_length {k : Nat} (word : List (Instruction k)) :
    (compressWhole word).length =
      (k + 1) * separatorCount word + k := by
  exact compressAux_length [] word

theorem compressAux_charge {k : Nat} (block rest : List (Instruction k)) :
    wordCharge (compressAux block rest) = wordCharge rest := by
  induction rest generalizing block with
  | nil => simpa [compressAux, wordCharge] using compressed_charge_zero block
  | cons op rest ih =>
      by_cases h : isShift op = true
      · have hc : charge op = 0 := by
          cases op <;> simp_all [isShift, charge]
        simp only [compressAux, if_pos h]
        rw [ih]
        simp [wordCharge, hc]
      · simp only [compressAux, if_neg h]
        rw [wordCharge_append, compressed_charge_zero]
        simp only [zero_add]
        change charge op + wordCharge (compressAux [] rest) =
          charge op + wordCharge rest
        rw [ih]
theorem compressWhole_charge {k : Nat} (word : List (Instruction k)) :
    wordCharge (compressWhole word) = wordCharge word := by
  exact compressAux_charge [] word

theorem noUnderflow_append {k : Nat} (first second : List (Op k))
    (w : Widths k) :
    noUnderflow (first ++ second) w ↔
      noUnderflow first w ∧ noUnderflow second (runWidths first w) := by
  induction first generalizing w with
  | nil => simp [noUnderflow, runWidths]
  | cons op rest ih =>
      simp [noUnderflow, runWidths, ih, and_assoc]

theorem widthWord_append {k : Nat} (first second : List (Instruction k)) :
    widthWord (first ++ second) = widthWord first ++ widthWord second := by
  simp [widthWord]

theorem scan_same_width_peak_mono {k : Nat} (word : List (Op k))
    (s t : State k) (hw : s.widths = t.widths) (hp : s.peak ≤ t.peak) :
    (scan word s).widths = (scan word t).widths ∧
      (scan word s).peak ≤ (scan word t).peak := by
  constructor
  · rw [scan_widths_eq_runWidths, scan_widths_eq_runWidths, hw]
  · exact continuation_upper_bound word hp (by intro i; rw [hw])

theorem shiftBlock_append_shift {k : Nat} (block : List (Instruction k))
    (op : Instruction k) (hb : ShiftBlock block) (hop : isShift op = true) :
    ShiftBlock (block ++ [op]) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hb x hx
  · have he : x = op := by simpa using hx
    subst x
    exact (shiftOnly_iff_isShift op).2 hop

theorem compressAux_runRows {k : Nat} (block rest : List (Instruction k))
    (rows final : Rows k)
    (hb : ShiftBlock block)
    (hrun : runRows (block ++ rest) rows = some final) :
    runRows (compressAux block rest) rows = some final := by
  induction rest generalizing block rows with
  | nil =>
      simpa [compressAux] using runRows_compressed block rows final hb
        (by simpa using hrun)
  | cons op rest ih =>
      by_cases h : isShift op = true
      · have hb' := shiftBlock_append_shift block op hb h
        have hrun' : runRows ((block ++ [op]) ++ rest) rows = some final := by
          simpa [List.append_assoc] using hrun
        simpa [compressAux, h] using ih (block ++ [op]) rows hb' hrun'
      · obtain ⟨mid, hblock⟩ :=
          runRows_append_prefix_success block (op :: rest) hrun
        have htail : runRows (op :: rest) mid = some final := by
          rw [runRows_append, hblock] at hrun
          exact hrun
        obtain ⟨next, hstep, hrest⟩ := runRows_cons_success htail
        have hcompblock := runRows_compressed block rows mid hb hblock
        have hrec : runRows (compressAux [] rest) next = some final := by
          apply ih [] next
          · intro x hx
            simp at hx
          · simpa using hrest
        simp only [compressAux, if_neg h]
        rw [runRows_append, hcompblock]
        simp only [Option.bind_some, runRows, hstep, Option.bind_some]
        exact hrec

theorem compressWhole_runRows {k : Nat} (word : List (Instruction k))
    (rows final : Rows k) (hrun : runRows word rows = some final) :
    runRows (compressWhole word) rows = some final := by
  apply compressAux_runRows [] word rows final
  · intro x hx
    simp at hx
  · simpa using hrun

theorem compressAux_scanner {k : Nat} (block rest : List (Instruction k))
    (s : State k) (hb : ShiftBlock block)
    (hn : noUnderflow (widthWord (block ++ rest)) s.widths)
    (hvalid : ∀ i, s.widths i ≤ s.peak) :
    noUnderflow (widthWord (compressAux block rest)) s.widths ∧
    (scan (widthWord (compressAux block rest)) s).widths =
      (scan (widthWord (block ++ rest)) s).widths ∧
    (scan (widthWord (compressAux block rest)) s).peak ≤
      (scan (widthWord (block ++ rest)) s).peak := by
  induction rest generalizing block s with
  | nil =>
      simpa [compressAux] using compressed_scanner block s hb
        (by simpa using hn) hvalid
  | cons op rest ih =>
      by_cases h : isShift op = true
      · have hb' := shiftBlock_append_shift block op hb h
        have hn' : noUnderflow (widthWord ((block ++ [op]) ++ rest)) s.widths := by
          simpa [List.append_assoc] using hn
        simpa [compressAux, h, List.append_assoc] using
          ih (block ++ [op]) s hb' hn' hvalid
      · have hsplit : noUnderflow (widthWord block) s.widths ∧
            noUnderflow (widthWord (op :: rest))
              (runWidths (widthWord block) s.widths) := by
          exact (noUnderflow_append (widthWord block)
            (widthWord (op :: rest)) s.widths).mp
            (by simpa [widthWord_append] using hn)
        let sB := scan (widthWord block) s
        let sC := scan (widthWord (compressed block)) s
        obtain ⟨hnoBlock, hwBC, hpBC⟩ :=
          compressed_scanner block s hb hsplit.1 hvalid
        have htailB : noUnderflow (widthWord (op :: rest)) sB.widths := by
          simpa [sB, scan_widths_eq_runWidths] using hsplit.2
        have hguardB : stepNoUnderflow (widthOp op) sB.widths := htailB.1
        have hguardC : stepNoUnderflow (widthOp op) sC.widths := by
          rw [hwBC]
          exact hguardB
        have hrestB : noUnderflow (widthWord rest)
            (advance (widthOp op) sB).widths := htailB.2
        have hwStep : (advance (widthOp op) sC).widths =
            (advance (widthOp op) sB).widths := by
          simpa [advance] using congrArg (step (widthOp op)) hwBC
        have hpStep : (advance (widthOp op) sC).peak ≤
            (advance (widthOp op) sB).peak := by
          exact (advance_mono (widthOp op)
            ⟨hpBC, by intro i; rw [hwBC]⟩).1
        have hrestC : noUnderflow (widthWord rest)
            (advance (widthOp op) sC).widths := by
          rw [hwStep]
          exact hrestB
        have hvalidC : ∀ i, sC.widths i ≤ sC.peak := by
          exact Paper.ScannerPotential.scan_width_le_peak _ _ hvalid
        have hvalidStep : ∀ i, (advance (widthOp op) sC).widths i ≤
            (advance (widthOp op) sC).peak := by
          intro i
          exact le_trans (Finset.le_sup (f := step (widthOp op) sC.widths)
            (Finset.mem_univ i)) (le_max_right _ _)
        have hrec := ih [] (advance (widthOp op) sC)
          (by intro x hx; simp at hx) (by simpa using hrestC) hvalidStep
        have hmono := scan_same_width_peak_mono (widthWord rest)
          (advance (widthOp op) sC) (advance (widthOp op) sB) hwStep hpStep
        have hcompScan :
            scan (widthWord (compressAux block (op :: rest))) s =
              scan (widthWord (compressAux [] rest)) (advance (widthOp op) sC) := by
          simp [compressAux, h, widthWord_append, scan_append, sC]
          rfl
        have horigScan :
            scan (widthWord (block ++ op :: rest)) s =
              scan (widthWord rest) (advance (widthOp op) sB) := by
          simp [widthWord_append, scan_append, sB]
          rfl
        have hcompNo : noUnderflow (widthWord (compressAux block (op :: rest)))
            s.widths := by
          have hcTail : noUnderflow
              (widthWord (op :: compressAux [] rest)) sC.widths := by
            exact ⟨hguardC, hrec.1⟩
          have hc := (noUnderflow_append (widthWord (compressed block))
            (widthWord (op :: compressAux [] rest)) s.widths).2
            ⟨hnoBlock, by simpa [sC, scan_widths_eq_runWidths] using hcTail⟩
          simpa [compressAux, h, widthWord_append] using hc
        refine ⟨hcompNo, ?_, ?_⟩
        · rw [hcompScan, horigScan]
          exact hrec.2.1.trans hmono.1
        · rw [hcompScan, horigScan]
          exact hrec.2.2.trans hmono.2

theorem compressWhole_scanner {k : Nat} (word : List (Instruction k))
    (s : State k) (hn : noUnderflow (widthWord word) s.widths)
    (hvalid : ∀ i, s.widths i ≤ s.peak) :
    noUnderflow (widthWord (compressWhole word)) s.widths ∧
    (scan (widthWord (compressWhole word)) s).widths =
      (scan (widthWord word) s).widths ∧
    (scan (widthWord (compressWhole word)) s).peak ≤
      (scan (widthWord word) s).peak := by
  apply compressAux_scanner [] word s
  · intro x hx
    simp at hx
  · simpa using hn
  · exact hvalid

def markerOps {k : Nat} : Instruction k → Nat
  | .phaseProduct _ => 1
  | _ => 0

def totalMarkers {k : Nat} (word : List (Instruction k)) : Nat :=
  (word.map markerOps).sum

theorem separatorCount_eq_paid_markers {k : Nat}
    (word : List (Instruction k)) :
    separatorCount word = Paper.ScannerPotential.totalPaid word + totalMarkers word := by
  induction word with
  | nil => rfl
  | cons op rest ih =>
      cases op <;> simp [separatorCount, isShift,
        Paper.ScannerPotential.totalPaid, Paper.ScannerPotential.paidOps,
        totalMarkers, markerOps, ih] <;> omega

theorem totalMarkers_eq_wordCounts {k : Nat} (word : List (Instruction k)) :
    totalMarkers word = (Paper.CostBridge.wordCounts word).markers := by
  induction word with
  | nil => rfl
  | cons op rest ih =>
      have ih' : (rest.map markerOps).sum =
          (Paper.CostBridge.wordCounts rest).markers := ih
      cases op with
      | shiftL i n => simpa [totalMarkers, markerOps, Paper.CostBridge.wordCounts] using ih'
      | shiftR i n => simpa [totalMarkers, markerOps, Paper.CostBridge.wordCounts] using ih'
      | negate i => simpa [totalMarkers, markerOps, Paper.CostBridge.wordCounts] using ih'
      | addScaled d s neg n =>
          cases neg <;> simpa [totalMarkers, markerOps, Paper.CostBridge.wordCounts] using ih'
      | phaseProduct i =>
          simp [totalMarkers, markerOps, Paper.CostBridge.wordCounts, ih']
          omega
theorem compressWhole_length_bound {k : Nat} (word : List (Instruction k))
    (q : Nat) (hq : totalMarkers word ≤ q) :
    (compressWhole word).length ≤
      (k + 1) * (Paper.ScannerPotential.totalPaid word + q) + k := by
  rw [compressWhole_length, separatorCount_eq_paid_markers]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left hq _)) _

def markerOf {k : Nat} : Instruction k → Option (Fin k)
  | .phaseProduct i => some i
  | _ => none

def markerRows {k : Nat} (word : List (Instruction k)) : List (Fin k) :=
  word.filterMap markerOf

theorem markerRows_shiftBlock {k : Nat} (block : List (Instruction k))
    (hb : ShiftBlock block) : markerRows block = [] := by
  induction block with
  | nil => rfl
  | cons op rest ih =>
      have hop := hb op (List.mem_cons_self)
      have hrest : ShiftBlock rest := by
        intro x hx
        exact hb x (List.mem_cons_of_mem _ hx)
      have hr := ih hrest
      cases op <;> simp_all [ShiftOnly, markerRows, markerOf]

theorem markerRows_compressed {k : Nat} (block : List (Instruction k)) :
    markerRows (compressed block) = [] :=
  markerRows_shiftBlock _ (compressed_shift_only block)

theorem markerRows_append {k : Nat} (first second : List (Instruction k)) :
    markerRows (first ++ second) = markerRows first ++ markerRows second := by
  simp [markerRows]

theorem compressAux_markerRows {k : Nat} (block rest : List (Instruction k)) :
    markerRows (compressAux block rest) = markerRows rest := by
  induction rest generalizing block with
  | nil => exact markerRows_compressed block
  | cons op rest ih =>
      by_cases h : isShift op = true
      · have hm : markerOf op = none := by
          cases op <;> simp_all [isShift, markerOf]
        simp only [compressAux, if_pos h]
        rw [ih]
        simp [markerRows, hm]
      · simp only [compressAux, if_neg h]
        rw [markerRows_append, markerRows_compressed]
        simp only [List.nil_append]
        simp only [markerRows, List.filterMap_cons]
        have hh := ih []
        change List.filterMap markerOf (compressAux [] rest) =
          List.filterMap markerOf rest at hh
        rw [hh]
theorem compressWhole_markerRows {k : Nat} (word : List (Instruction k)) :
    markerRows (compressWhole word) = markerRows word := by
  exact compressAux_markerRows [] word

end Paper.WholeCompression
