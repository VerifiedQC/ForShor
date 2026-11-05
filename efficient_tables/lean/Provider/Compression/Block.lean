import Model.Interpreter.Mass
import Provider.Compression.Potential

/-!
# Shift-block compression

Defines shift-only instruction blocks (`ShiftOnly`, `ShiftBlock`) and the
single net shift per row `netShift`, giving the compressed block `compressed`.
It proves per-row accounting for scanner blocks (`scanner_block_row_account`),
the length of the compressed block (`compressed_length`), and no-underflow and
width-target facts for the net shift (`netShift_noUnderflow`,
`netShift_width_target`).
-/

namespace Paper.ShiftCompression

open Paper.FullDSL Paper.Scanner

def ShiftOnly {k : Nat} : Instruction k → Prop
  | .shiftL _ _ => True
  | .shiftR _ _ => True
  | _ => False

def ShiftBlock {k : Nat} (word : List (Instruction k)) : Prop :=
  ∀ op ∈ word, ShiftOnly op

def leftAt {k : Nat} (i : Fin k) : Instruction k → Nat
  | .shiftL j n => if i = j then n else 0
  | _ => 0

def rightAt {k : Nat} (i : Fin k) : Instruction k → Nat
  | .shiftR j n => if i = j then n else 0
  | _ => 0

def totalLeftAt {k : Nat} (i : Fin k) (word : List (Instruction k)) : Nat :=
  (word.map (leftAt i)).sum

def totalRightAt {k : Nat} (i : Fin k) (word : List (Instruction k)) : Nat :=
  (word.map (rightAt i)).sum

theorem scanner_step_row_account {k : Nat} (i : Fin k)
    (op : Instruction k) (w : Widths k)
    (hs : ShiftOnly op) (hn : stepNoUnderflow (widthOp op) w) :
    w i + leftAt i op = step (widthOp op) w i + rightAt i op := by
  cases op with
  | shiftL j n =>
      by_cases h : i = j
      · subst i; simp [widthOp, step, leftAt, rightAt]
      · simp [widthOp, step, leftAt, rightAt, h]
  | shiftR j n =>
      by_cases h : i = j
      · subst i
        have hn' : n ≤ w j := by simpa [stepNoUnderflow, widthOp] using hn
        simp [widthOp, step, leftAt, rightAt]
        omega
      · simp [widthOp, step, leftAt, rightAt, h]
  | negate j => simp [ShiftOnly] at hs
  | addScaled d s neg n => simp [ShiftOnly] at hs
  | phaseProduct j => simp [ShiftOnly] at hs

theorem scanner_block_row_account {k : Nat} (i : Fin k)
    (word : List (Instruction k)) (w : Widths k)
    (hs : ShiftBlock word) (hn : noUnderflow (widthWord word) w) :
    w i + totalLeftAt i word =
      runWidths (widthWord word) w i + totalRightAt i word := by
  induction word generalizing w with
  | nil => simp [totalLeftAt, totalRightAt, widthWord, runWidths]
  | cons op rest ih =>
      obtain ⟨hop, hrest⟩ := hn
      have hso : ShiftOnly op := hs op (List.mem_cons_self)
      have hsr : ShiftBlock rest := by
        intro x hx
        exact hs x (List.mem_cons_of_mem _ hx)
      have hstep := scanner_step_row_account i op w hso hop
      have htail := ih (step (widthOp op) w) hsr hrest
      simp only [totalLeftAt, totalRightAt, List.map_cons, List.sum_cons,
        widthWord, runWidths] at *
      omega


/-- One free net shift for one row. A zero shift is retained, so the
compressed block has exactly one free instruction per row. -/
def netShift {k : Nat} (i : Fin k) (word : List (Instruction k)) : Instruction k :=
  if totalRightAt i word ≤ totalLeftAt i word then
    .shiftL i (totalLeftAt i word - totalRightAt i word)
  else
    .shiftR i (totalRightAt i word - totalLeftAt i word)

def compressed {k : Nat} (word : List (Instruction k)) : List (Instruction k) :=
  (List.finRange k).map (fun i => netShift i word)

theorem compressed_length {k : Nat} (word : List (Instruction k)) :
    (compressed word).length = k := by
  simp [compressed]

theorem netShift_only {k : Nat} (i : Fin k) (word : List (Instruction k)) :
    ShiftOnly (netShift i word) := by
  unfold netShift
  split <;> trivial

theorem netShift_noUnderflow {k : Nat} (i : Fin k)
    (word : List (Instruction k)) (w : Widths k)
    (hs : ShiftBlock word) (hn : noUnderflow (widthWord word) w) :
    stepNoUnderflow (widthOp (netShift i word)) w := by
  have ha := scanner_block_row_account i word w hs hn
  unfold netShift
  split_ifs with h
  · trivial
  · have hlt : totalLeftAt i word < totalRightAt i word := by omega
    simpa [widthOp, stepNoUnderflow] using
      (show totalRightAt i word - totalLeftAt i word ≤ w i by omega)

theorem netShift_width_target {k : Nat} (i : Fin k)
    (word : List (Instruction k)) (w : Widths k)
    (hs : ShiftBlock word) (hn : noUnderflow (widthWord word) w) :
    step (widthOp (netShift i word)) w i =
      runWidths (widthWord word) w i := by
  have ha := scanner_block_row_account i word w hs hn
  unfold netShift
  split_ifs with h
  · simp [widthOp, step]
    omega
  · simp [widthOp, step]
    omega

theorem netShift_width_other {k : Nat} (i j : Fin k)
    (word : List (Instruction k)) (w : Widths k) (h : j ≠ i) :
    step (widthOp (netShift i word)) w j = w j := by
  unfold netShift
  split_ifs <;> simp [widthOp, step, h]

theorem rowStep_row_account {k : Nat} (i j : Fin k)
    (op : Instruction k) (rows next : Rows k)
    (hs : ShiftOnly op) (hstep : rowStep op rows = some next) :
    (2 : Int) ^ rightAt i op * next i j =
      (2 : Int) ^ leftAt i op * rows i j := by
  cases op with
  | shiftL r n =>
      simp only [rowStep, Option.some.injEq] at hstep
      subst next
      by_cases hir : i = r
      · subst i
        simp [leftAt, rightAt, Matrix.updateRow_self]
        ring
      · simp [leftAt, rightAt, Matrix.updateRow_ne hir, hir]
  | shiftR r n =>
      by_cases hir : i = r
      · subst i
        have he := shiftR_success_exact rows next r n hstep j
        simpa [leftAt, rightAt] using he.symm
      · have hup : next = rows.updateRow r
            (fun j => rows r j / (2 : Int) ^ n) := by
          by_cases hd : ∀ j : Fin k, rows r j % (2 : Int) ^ n = 0
          · simpa [rowStep, hd] using hstep.symm
          · simp [rowStep, hd] at hstep
        simp [leftAt, rightAt, hup, Matrix.updateRow_ne hir, hir]
  | negate r => simp [ShiftOnly] at hs
  | addScaled d s neg n => simp [ShiftOnly] at hs
  | phaseProduct r => simp [ShiftOnly] at hs

theorem runRows_block_row_account {k : Nat} (i j : Fin k)
    (word : List (Instruction k)) (rows final : Rows k)
    (hs : ShiftBlock word)
    (hrun : runRows word rows = some final) :
    (2 : Int) ^ totalRightAt i word * final i j =
      (2 : Int) ^ totalLeftAt i word * rows i j := by
  induction word generalizing rows with
  | nil =>
      simp only [runRows, Option.some.injEq] at hrun
      subst final
      simp [totalLeftAt, totalRightAt]
  | cons op rest ih =>
      obtain ⟨mid, hstep, hrest⟩ := runRows_cons_success hrun
      have hso : ShiftOnly op := hs op (List.mem_cons_self)
      have hsr : ShiftBlock rest := by
        intro x hx
        exact hs x (List.mem_cons_of_mem _ hx)
      have hhead := rowStep_row_account i j op rows mid hso hstep
      have htail := ih mid hsr hrest
      simp only [totalLeftAt, totalRightAt, List.map_cons, List.sum_cons]
      simp only [totalLeftAt, totalRightAt] at htail
      calc
        (2 : Int) ^ (rightAt i op + (rest.map (rightAt i)).sum) * final i j =
            (2 : Int) ^ rightAt i op *
              ((2 : Int) ^ (rest.map (rightAt i)).sum * final i j) := by
                rw [pow_add]; ring
        _ = (2 : Int) ^ rightAt i op *
              ((2 : Int) ^ (rest.map (leftAt i)).sum * mid i j) := by rw [htail]
        _ = (2 : Int) ^ (rest.map (leftAt i)).sum *
              ((2 : Int) ^ rightAt i op * mid i j) := by ring
        _ = (2 : Int) ^ (rest.map (leftAt i)).sum *
              ((2 : Int) ^ leftAt i op * rows i j) := by rw [hhead]
        _ = (2 : Int) ^ (leftAt i op + (rest.map (leftAt i)).sum) * rows i j := by
              rw [pow_add]; ring

theorem netLeft_exact {k : Nat} (i j : Fin k)
    (word : List (Instruction k)) (rows final : Rows k)
    (hs : ShiftBlock word) (hrun : runRows word rows = some final)
    (h : totalRightAt i word ≤ totalLeftAt i word) :
    final i j = rows i j *
      (2 : Int) ^ (totalLeftAt i word - totalRightAt i word) := by
  have ha := runRows_block_row_account i j word rows final hs hrun
  have hd : totalLeftAt i word =
      totalRightAt i word + (totalLeftAt i word - totalRightAt i word) := by omega
  have hp : (2 : Int) ^ totalLeftAt i word =
      (2 : Int) ^ totalRightAt i word *
        (2 : Int) ^ (totalLeftAt i word - totalRightAt i word) := by
    conv_lhs => rw [hd]
    rw [pow_add]
  have heq :
      (2 : Int) ^ totalRightAt i word * final i j =
      (2 : Int) ^ totalRightAt i word *
        (rows i j * (2 : Int) ^ (totalLeftAt i word - totalRightAt i word)) := by
    calc
      _ = (2 : Int) ^ totalLeftAt i word * rows i j := ha
      _ = (2 : Int) ^ totalRightAt i word *
          (rows i j * (2 : Int) ^ (totalLeftAt i word - totalRightAt i word)) := by
            rw [hp]
            ring
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : Int) ≠ 0)) heq

theorem netRight_exact {k : Nat} (i j : Fin k)
    (word : List (Instruction k)) (rows final : Rows k)
    (hs : ShiftBlock word) (hrun : runRows word rows = some final)
    (h : totalLeftAt i word < totalRightAt i word) :
    rows i j = (2 : Int) ^ (totalRightAt i word - totalLeftAt i word) *
      final i j := by
  have ha := runRows_block_row_account i j word rows final hs hrun
  have hd : totalRightAt i word =
      totalLeftAt i word + (totalRightAt i word - totalLeftAt i word) := by omega
  have hp : (2 : Int) ^ totalRightAt i word =
      (2 : Int) ^ totalLeftAt i word *
        (2 : Int) ^ (totalRightAt i word - totalLeftAt i word) := by
    conv_lhs => rw [hd]
    rw [pow_add]
  have heq :
      (2 : Int) ^ totalLeftAt i word *
        ((2 : Int) ^ (totalRightAt i word - totalLeftAt i word) * final i j) =
      (2 : Int) ^ totalLeftAt i word * rows i j := by
    calc
      _ = (2 : Int) ^ totalRightAt i word * final i j := by
            rw [hp]
            ring
      _ = (2 : Int) ^ totalLeftAt i word * rows i j := ha
  exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : Int) ≠ 0)) heq).symm

theorem netShift_rowStep {k : Nat} (i : Fin k)
    (word : List (Instruction k)) (rows final : Rows k)
    (hs : ShiftBlock word) (hrun : runRows word rows = some final) :
    rowStep (netShift i word) rows =
      some (rows.updateRow i (final i)) := by
  unfold netShift
  split_ifs with h
  · have he : (fun j => rows i j *
        (2 : Int) ^ (totalLeftAt i word - totalRightAt i word)) = final i := by
      funext j
      exact (netLeft_exact i j word rows final hs hrun h).symm
    simp only [rowStep, he]
  · have hlt : totalLeftAt i word < totalRightAt i word := by omega
    let d := totalRightAt i word - totalLeftAt i word
    have he : ∀ j, rows i j = (2 : Int) ^ d * final i j := by
      intro j
      exact netRight_exact i j word rows final hs hrun hlt
    have hdiv : ∀ j, rows i j % (2 : Int) ^ d = 0 := by
      intro j
      apply Int.dvd_iff_emod_eq_zero.mp
      exact ⟨final i j, by rw [he j]⟩
    have hq : (fun j => rows i j / (2 : Int) ^ d) = final i := by
      funext j
      rw [he j]
      exact Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num : (2 : Int) ≠ 0))
    change (if _ : ∀ j, rows i j % (2 : Int) ^ d = 0 then
      some (rows.updateRow i (fun j => rows i j / (2 : Int) ^ d)) else none) =
      some (rows.updateRow i (final i))
    simp [hdiv, hq]

theorem netShift_step_congr {k : Nat} (i : Fin k)
    (word : List (Instruction k)) (rows current final : Rows k)
    (hs : ShiftBlock word) (hrun : runRows word rows = some final)
    (hi : current i = rows i) :
    rowStep (netShift i word) current =
      some (current.updateRow i (final i)) := by
  unfold netShift
  split_ifs with h
  · have he : (fun j => current i j *
        (2 : Int) ^ (totalLeftAt i word - totalRightAt i word)) = final i := by
      funext j
      rw [hi]
      exact (netLeft_exact i j word rows final hs hrun h).symm
    simp only [rowStep, he]
  · have hlt : totalLeftAt i word < totalRightAt i word := by omega
    let d := totalRightAt i word - totalLeftAt i word
    have he : ∀ j, current i j = (2 : Int) ^ d * final i j := by
      intro j
      rw [hi]
      exact netRight_exact i j word rows final hs hrun hlt
    have hdiv : ∀ j, current i j % (2 : Int) ^ d = 0 := by
      intro j
      apply Int.dvd_iff_emod_eq_zero.mp
      exact ⟨final i j, by rw [he j]⟩
    have hq : (fun j => current i j / (2 : Int) ^ d) = final i := by
      funext j
      rw [he j]
      exact Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num : (2 : Int) ≠ 0))
    change (if _ : ∀ j, current i j % (2 : Int) ^ d = 0 then
      some (current.updateRow i (fun j => current i j / (2 : Int) ^ d)) else none) =
      some (current.updateRow i (final i))
    simp [hdiv, hq]

def overwriteRows {k : Nat} (ls : List (Fin k))
    (current final : Rows k) : Rows k :=
  fun i j => if i ∈ ls then final i j else current i j

theorem overwriteRows_cons {k : Nat} (i : Fin k) (ls : List (Fin k))
    (current final : Rows k) (h : i ∉ ls) :
    overwriteRows ls (current.updateRow i (final i)) final =
      overwriteRows (i :: ls) current final := by
  funext r c
  by_cases hr : r ∈ ls
  · simp [overwriteRows, hr, List.mem_cons_of_mem i hr]
  · by_cases hi : r = i
    · subst r
      simp [overwriteRows, hr, Matrix.updateRow_self]
    · simp [overwriteRows, hr, hi, Matrix.updateRow_ne hi]

theorem runRows_netList {k : Nat} (ls : List (Fin k))
    (word : List (Instruction k)) (rows current final : Rows k)
    (hs : ShiftBlock word) (hrun : runRows word rows = some final)
    (hnd : ls.Nodup) (hremain : ∀ i ∈ ls, current i = rows i) :
    runRows (ls.map (fun i => netShift i word)) current =
      some (overwriteRows ls current final) := by
  induction ls generalizing current with
  | nil =>
      simp only [List.map_nil, runRows, Option.some.injEq]
      funext i j
      simp [overwriteRows]
  | cons i rest ih =>
      have hnot : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hi : current i = rows i := hremain i (List.mem_cons_self)
      have hstep := netShift_step_congr i word rows current final hs hrun hi
      have hremain' : ∀ j ∈ rest,
          (current.updateRow i (final i)) j = rows j := by
        intro j hj
        have hji : j ≠ i := by
          intro he
          subst j
          exact hnot hj
        rw [Matrix.updateRow_ne hji]
        exact hremain j (List.mem_cons_of_mem _ hj)
      have htail := ih (current.updateRow i (final i)) hnd' hremain'
      simp only [List.map_cons, runRows]
      rw [hstep]
      simpa only [Option.bind_some, overwriteRows_cons i rest current final hnot] using htail

theorem runRows_compressed {k : Nat}
    (word : List (Instruction k)) (rows final : Rows k)
    (hs : ShiftBlock word) (hrun : runRows word rows = some final) :
    runRows (compressed word) rows = some final := by
  have h := runRows_netList (List.finRange k) word rows rows final hs hrun
    (List.nodup_finRange k) (by intro i _; rfl)
  have he : overwriteRows (List.finRange k) rows final = final := by
    funext i j
    simp [overwriteRows, List.mem_finRange]
  simpa [compressed, he] using h

theorem netShift_width_congr {k : Nat} (i : Fin k)
    (word : List (Instruction k)) (w current : Widths k)
    (hs : ShiftBlock word) (hn : noUnderflow (widthWord word) w)
    (hi : current i = w i) :
    stepNoUnderflow (widthOp (netShift i word)) current ∧
    step (widthOp (netShift i word)) current =
      Function.update current i (runWidths (widthWord word) w i) := by
  have hg := netShift_noUnderflow i word w hs hn
  have ht := netShift_width_target i word w hs hn
  constructor
  · unfold netShift
    split_ifs with h
    · trivial
    · have ha := scanner_block_row_account i word w hs hn
      change totalRightAt i word - totalLeftAt i word ≤ current i
      omega
  · funext j
    by_cases hji : j = i
    · subst j
      have hcur : step (widthOp (netShift i word)) current i =
          step (widthOp (netShift i word)) w i := by
        unfold netShift
        split_ifs <;> simp [widthOp, step, hi]
      simpa using hcur.trans ht
    · rw [netShift_width_other i j word current hji]
      simp [Function.update, hji]

def overwriteWidths {k : Nat} (ls : List (Fin k))
    (current final : Widths k) : Widths k :=
  fun i => if i ∈ ls then final i else current i

theorem overwriteWidths_cons {k : Nat} (i : Fin k) (ls : List (Fin k))
    (current final : Widths k) (h : i ∉ ls) :
    overwriteWidths ls (Function.update current i (final i)) final =
      overwriteWidths (i :: ls) current final := by
  funext r
  by_cases hr : r ∈ ls
  · simp [overwriteWidths, hr, List.mem_cons_of_mem i hr]
  · by_cases hi : r = i
    · subst r
      simp [overwriteWidths, hr]
    · simp [overwriteWidths, hr, hi]

theorem scan_netList {k : Nat} (ls : List (Fin k))
    (word : List (Instruction k)) (w finalW : Widths k)
    (s : State k) (bound : Nat)
    (hs : ShiftBlock word) (hn : noUnderflow (widthWord word) w)
    (hnd : ls.Nodup) (hremain : ∀ i ∈ ls, s.widths i = w i)
    (hpeak : s.peak ≤ bound)
    (hcurBound : ∀ i, s.widths i ≤ bound)
    (hfinalBound : ∀ i, finalW i ≤ bound)
    (hfinal : finalW = runWidths (widthWord word) w) :
    noUnderflow (widthWord (ls.map (fun i => netShift i word))) s.widths ∧
    (scan (widthWord (ls.map (fun i => netShift i word))) s).widths =
      overwriteWidths ls s.widths finalW ∧
    (scan (widthWord (ls.map (fun i => netShift i word))) s).peak ≤ bound := by
  induction ls generalizing s with
  | nil =>
      constructor
      · trivial
      constructor
      · funext i
        simp [widthWord, scan, overwriteWidths]
      · simpa [widthWord, scan] using hpeak
  | cons i rest ih =>
      have hnot : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hi : s.widths i = w i := hremain i (List.mem_cons_self)
      obtain ⟨hg, hstep⟩ := netShift_width_congr i word w s.widths hs hn hi
      have hstep' : (advance (widthOp (netShift i word)) s).widths =
          Function.update s.widths i (finalW i) := by
        simpa [advance, hfinal] using hstep
      have hcurBound' : ∀ j,
          (advance (widthOp (netShift i word)) s).widths j ≤ bound := by
        intro j
        rw [hstep']
        by_cases hj : j = i
        · subst j
          simpa using hfinalBound i
        · simpa [Function.update, hj] using hcurBound j
      have hpeak' : (advance (widthOp (netShift i word)) s).peak ≤ bound := by
        change max s.peak
          (maximum (step (widthOp (netShift i word)) s.widths)) ≤ bound
        apply max_le hpeak
        apply Finset.sup_le
        intro j _
        simpa [advance] using hcurBound' j
      have hremain' : ∀ j ∈ rest,
          (advance (widthOp (netShift i word)) s).widths j = w j := by
        intro j hj
        rw [hstep']
        have hji : j ≠ i := by
          intro he
          subst j
          exact hnot hj
        simpa [Function.update, hji] using hremain j (List.mem_cons_of_mem _ hj)
      obtain ⟨htailNo, htailWidths, htailPeak⟩ :=
        ih (advance (widthOp (netShift i word)) s)
          hnd' hremain' hpeak' hcurBound'
      constructor
      · simpa only [List.map_cons, widthWord, noUnderflow] using
          (show stepNoUnderflow (widthOp (netShift i word)) s.widths ∧
            noUnderflow (widthWord (rest.map (fun j => netShift j word)))
              (step (widthOp (netShift i word)) s.widths) from ⟨hg, htailNo⟩)
      constructor
      · change (scan (widthWord (rest.map (fun j => netShift j word)))
            (advance (widthOp (netShift i word)) s)).widths =
          overwriteWidths (i :: rest) s.widths finalW
        rw [htailWidths, hstep', overwriteWidths_cons i rest s.widths finalW hnot]
      · simpa only [List.map_cons, widthWord, scan] using htailPeak

theorem compressed_scanner {k : Nat}
    (word : List (Instruction k)) (s : State k)
    (hs : ShiftBlock word)
    (hn : noUnderflow (widthWord word) s.widths)
    (hvalid : ∀ i, s.widths i ≤ s.peak) :
    noUnderflow (widthWord (compressed word)) s.widths ∧
    (scan (widthWord (compressed word)) s).widths =
      (scan (widthWord word) s).widths ∧
    (scan (widthWord (compressed word)) s).peak ≤
      (scan (widthWord word) s).peak := by
  let finalW := (scan (widthWord word) s).widths
  let bound := (scan (widthWord word) s).peak
  have hbound : s.peak ≤ bound := incoming_peak_le_scan _ _
  have hcur : ∀ i, s.widths i ≤ bound := by
    intro i
    exact (hvalid i).trans hbound
  have hfin : ∀ i, finalW i ≤ bound :=
    Paper.ScannerPotential.scan_width_le_peak _ _ hvalid
  have hfinal : finalW = runWidths (widthWord word) s.widths :=
    scan_widths_eq_runWidths _ _
  obtain ⟨hno, heq, hpeak⟩ :=
    scan_netList (List.finRange k) word s.widths finalW s bound
      hs hn (List.nodup_finRange k) (by intro i _; rfl)
      hbound hcur hfin hfinal
  have hall : overwriteWidths (List.finRange k) s.widths finalW = finalW := by
    funext i
    simp [overwriteWidths, List.mem_finRange]
  simpa [compressed, hall, finalW, bound] using
    (show noUnderflow (widthWord (compressed word)) s.widths ∧
        (scan (widthWord (compressed word)) s).widths = finalW ∧
        (scan (widthWord (compressed word)) s).peak ≤ bound by
      simpa [compressed, hall] using (And.intro hno (And.intro heq hpeak)))

theorem compressed_scanner_endpoint {k : Nat}
    (word : List (Instruction k)) (s : State k)
    (hs : ShiftBlock word)
    (hn : noUnderflow (widthWord word) s.widths) :
    noUnderflow (widthWord (compressed word)) s.widths ∧
    (scan (widthWord (compressed word)) s).widths =
      (scan (widthWord word) s).widths := by
  let finalW := (scan (widthWord word) s).widths
  let bound := max s.peak (max (maximum s.widths) (maximum finalW))
  have hbound : s.peak ≤ bound := le_max_left _ _
  have hcur : ∀ i, s.widths i ≤ bound := by
    intro i
    exact (Finset.le_sup (f := s.widths) (Finset.mem_univ i)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  have hfin : ∀ i, finalW i ≤ bound := by
    intro i
    exact (Finset.le_sup (f := finalW) (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hfinal : finalW = runWidths (widthWord word) s.widths :=
    scan_widths_eq_runWidths _ _
  obtain ⟨hno, heq, _⟩ :=
    scan_netList (List.finRange k) word s.widths finalW s bound
      hs hn (List.nodup_finRange k) (by intro i _; rfl)
      hbound hcur hfin hfinal
  have hall : overwriteWidths (List.finRange k) s.widths finalW = finalW := by
    funext i
    simp [overwriteWidths, List.mem_finRange]
  simpa [compressed, hall, finalW] using (And.intro hno heq)

theorem compressed_shift_only {k : Nat} (word : List (Instruction k)) :
    ShiftBlock (compressed word) := by
  intro op hop
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hop
  exact netShift_only i word

theorem compressed_charge_zero {k : Nat} (word : List (Instruction k)) :
    wordCharge (compressed word) = 0 := by
  unfold wordCharge compressed
  simp only [List.map_map]
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hn
  by_cases h : totalRightAt i word ≤ totalLeftAt i word
  · simp [netShift, h, charge]
  · simp [netShift, h, charge]


/-- A compressed shift block contains no phase-product marker. -/
theorem compressed_no_markers {k : Nat} (word : List (Instruction k))
    (i : Fin k) : .phaseProduct i ∉ compressed word := by
  intro h
  have hshift := compressed_shift_only word (.phaseProduct i) h
  simpa [ShiftOnly] using hshift
end Paper.ShiftCompression