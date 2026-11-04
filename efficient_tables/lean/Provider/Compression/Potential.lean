import Model.Interpreter.Mass
import Model.Interpreter.SourceConnection
import PhaseProduct.Catalog.EndToEnd
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Scanner potential bounds

Defines the width sum `widthSum` and the per-word totals `totalLeft`,
`totalRight` and `totalPaid` for the scanner. It proves step and word
accounting identities (`scanner_step_account`, `scanner_word_account`,
`word_det_account`), a balance for closed shift words (`closed_shift_balance`),
and that widths stay within the scanner peak (`scan_width_le_peak`).
-/

namespace Paper.ScannerPotential

open Paper.FullDSL Paper.Scanner

def widthSum {k : Nat} (w : Widths k) : Nat := ∑ i : Fin k, w i

def leftAmount {k : Nat} : Instruction k → Nat
  | .shiftL _ n => n
  | _ => 0

def rightAmount {k : Nat} : Instruction k → Nat
  | .shiftR _ n => n
  | _ => 0

def paidOps {k : Nat} : Instruction k → Nat
  | .negate _ => 1
  | .addScaled _ _ _ _ => 1
  | _ => 0

def totalLeft {k : Nat} (word : List (Instruction k)) : Nat := (word.map leftAmount).sum
def totalRight {k : Nat} (word : List (Instruction k)) : Nat := (word.map rightAmount).sum
def totalPaid {k : Nat} (word : List (Instruction k)) : Nat := (word.map paidOps).sum

theorem widthSum_update {k : Nat} (w : Widths k) (i : Fin k) (x : Nat) :
    widthSum (Function.update w i x) + w i = widthSum w + x := by
  simp only [widthSum]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hh := Finset.sum_erase_add Finset.univ w (Finset.mem_univ i)
  rw [← Finset.sdiff_singleton_eq_erase] at hh
  omega

theorem scanner_step_account {k : Nat} (op : Instruction k) (w : Widths k)
    (h : stepNoUnderflow (widthOp op) w) :
    widthSum w + leftAmount op + paidOps op ≤
      widthSum (step (widthOp op) w) + rightAmount op := by
  cases op with
  | shiftL i n =>
      simp only [widthOp, step, leftAmount, paidOps, rightAmount, Nat.add_zero]
      have he := widthSum_update w i (w i + n)
      omega
  | shiftR i n =>
      simp only [widthOp, step, leftAmount, paidOps, rightAmount, Nat.add_zero]
      have he := widthSum_update w i (w i - n)
      have hn : n ≤ w i := by simpa [widthOp, stepNoUnderflow] using h
      omega
  | negate i =>
      simp only [widthOp, step, leftAmount, paidOps, rightAmount, Nat.add_zero]
      have he := widthSum_update w i (w i + 1)
      omega
  | addScaled d s neg n =>
      simp only [widthOp, step, leftAmount, paidOps, rightAmount, Nat.add_zero]
      have he := widthSum_update w d (1 + max (w d) (w s + n))
      omega
  | phaseProduct i => simp [widthOp, step, leftAmount, paidOps, rightAmount]

theorem scanner_word_account {k : Nat} (word : List (Instruction k)) (w : Widths k)
    (h : noUnderflow (widthWord word) w) :
    widthSum w + totalLeft word + totalPaid word ≤
      widthSum (runWidths (widthWord word) w) + totalRight word := by
  induction word generalizing w with
  | nil => simp [totalLeft, totalPaid, totalRight, widthWord, runWidths]
  | cons op rest ih =>
      obtain ⟨hop, hrest⟩ := h
      have hstep := scanner_step_account op w hop
      have htail := ih (step (widthOp op) w) hrest
      simp only [totalLeft, totalRight, totalPaid, widthWord, List.map_cons,
        List.sum_cons, runWidths] at *
      omega


theorem step_det_account {k : Nat} (op : Instruction k)
    (rows next : Rows k) (h : rowStep op rows = some next) :
    2 ^ rightAmount op * next.det.natAbs =
      2 ^ leftAmount op * rows.det.natAbs := by
  cases op with
  | shiftL i n =>
      simp only [rowStep, Option.some.injEq] at h
      subst next
      have hrow : (fun j => rows i j * (2 : Int) ^ n) =
          (2 : Int) ^ n • rows i := by
        funext j
        simp [mul_comm]
      rw [hrow, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
      simp [leftAmount, rightAmount, Int.natAbs_mul]
  | shiftR i n =>
      simp only [rowStep] at h
      split_ifs at h with hdiv
      · have hn := Option.some.inj h
        subst next
        let q : Fin k → Int := fun j => rows i j / (2 : Int) ^ n
        have hrow : rows i = (2 : Int) ^ n • q := by
          funext j
          have hj : (2 : Int) ^ n ∣ rows i j :=
            Int.dvd_iff_emod_eq_zero.mpr (hdiv j)
          simpa [q, smul_eq_mul, mul_comm] using
            (Int.ediv_mul_cancel hj).symm
        have hfactor :
            rows.det = (2 : Int) ^ n *
              (rows.updateRow i q).det := by
          calc
            rows.det = (rows.updateRow i (rows i)).det := by
              rw [Matrix.updateRow_eq_self]
            _ = (rows.updateRow i ((2 : Int) ^ n • q)).det := by rw [← hrow]
            _ = (2 : Int) ^ n * (rows.updateRow i q).det :=
              Matrix.det_updateRow_smul rows i ((2 : Int) ^ n) q
        simp only [leftAmount, rightAmount, pow_zero, one_mul]
        rw [hfactor, Int.natAbs_mul]
        simp [q]
  | negate i =>
      simp only [rowStep, Option.some.injEq] at h
      subst next
      have hrow : (fun j => -rows i j) = (-1 : Int) • rows i := by
        funext j
        simp
      rw [hrow, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
      simp [leftAmount, rightAmount]
  | addScaled dst src negSrc shift =>
      by_cases heq : dst = src
      · simp [rowStep, heq] at h
      · cases negSrc with
        | false =>
            simp [rowStep, heq] at h
            subst next
            have hrow : (fun j => rows dst j + (2 : Int) ^ shift * rows src j) =
                rows dst + ((2 : Int) ^ shift) • rows src := by
              funext j
              simp
            rw [hrow, Matrix.det_updateRow_add_smul_self rows heq]
            simp [leftAmount, rightAmount]
        | true =>
            simp [rowStep, heq] at h
            subst next
            have hrow : (fun j => rows dst j + -((2 : Int) ^ shift * rows src j)) =
                rows dst + (-(2 : Int) ^ shift) • rows src := by
              funext j
              simp
            rw [hrow, Matrix.det_updateRow_add_smul_self rows heq]
            simp [leftAmount, rightAmount]
  | phaseProduct i =>
      simp [rowStep] at h
      subst next
      simp [leftAmount, rightAmount]

theorem word_det_account {k : Nat} (word : List (Instruction k))
    {rows final : Rows k} (h : runRows word rows = some final) :
    2 ^ totalRight word * final.det.natAbs =
      2 ^ totalLeft word * rows.det.natAbs := by
  induction word generalizing rows with
  | nil =>
      simp only [runRows, Option.some.injEq] at h
      subst final
      simp [totalLeft, totalRight]
  | cons op rest ih =>
      obtain ⟨mid, hs, hr⟩ := runRows_cons_success h
      have hstep := step_det_account op rows mid hs
      have hrest := ih hr
      simp only [totalLeft, totalRight] at hrest
      simp only [totalLeft, totalRight, List.map_cons, List.sum_cons]
      calc
        2 ^ (rightAmount op + (rest.map rightAmount).sum) * final.det.natAbs =
            2 ^ rightAmount op * (2 ^ (rest.map rightAmount).sum * final.det.natAbs) := by
              rw [pow_add]; ac_rfl
        _ = 2 ^ rightAmount op * (2 ^ (rest.map leftAmount).sum * mid.det.natAbs) := by
              rw [hrest]
        _ = 2 ^ (rest.map leftAmount).sum * (2 ^ rightAmount op * mid.det.natAbs) := by
              ac_rfl
        _ = 2 ^ (rest.map leftAmount).sum * (2 ^ leftAmount op * rows.det.natAbs) := by
              rw [hstep]
        _ = 2 ^ (leftAmount op + (rest.map leftAmount).sum) * rows.det.natAbs := by
              rw [pow_add]; ac_rfl

theorem closed_shift_balance {k : Nat} (word : List (Instruction k))
    (h : runRows word (identity k) = some (identity k)) :
    totalLeft word = totalRight word := by
  have hh := word_det_account word h
  have hid : (identity k).det.natAbs = 1 := by simp [identity]
  simp only [hid, mul_one] at hh
  exact Nat.le_antisymm
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh.symm.le)
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh.le)

theorem scan_width_le_peak {k : Nat} (word : List (Op k)) (s : State k)
    (h : ∀ i, s.widths i ≤ s.peak) :
    ∀ i, (scan word s).widths i ≤ (scan word s).peak := by
  induction word generalizing s with
  | nil => exact h
  | cons op rest ih =>
      apply ih
      intro i
      exact le_trans (Finset.le_sup (f := step op s.widths) (Finset.mem_univ i))
        (le_max_right s.peak (maximum (step op s.widths)))

theorem fresh_width_le_peak {k : Nat} (word : List (Op k)) (w : Widths k) :
    ∀ i, (scan word (fresh w)).widths i ≤ (scan word (fresh w)).peak := by
  apply scan_width_le_peak
  intro i
  exact Finset.le_sup (f := w) (Finset.mem_univ i)

theorem fresh_sum_le_peak {k : Nat} (word : List (Op k)) (w : Widths k) :
    widthSum (runWidths word w) ≤
      k * (scan word (fresh w)).peak := by
  have h := fresh_width_le_peak word w
  have he := scan_widths_eq_runWidths word (fresh w)
  change (scan word (fresh w)).widths = runWidths word w at he
  rw [← he] 
  calc
    widthSum (scan word (fresh w)).widths ≤
        ∑ _i : Fin k, (scan word (fresh w)).peak := by
          apply Finset.sum_le_sum
          intro i _
          exact h i
    _ = k * (scan word (fresh w)).peak := by simp

theorem initial_sum_zero {k : Nat} (top : Fin k) :
    widthSum (balanced top 0 0) = 0 := by
  simp [widthSum, balanced]

theorem initial_sum_spike {k : Nat} (top : Fin k) :
    widthSum (balanced top 0 (k - 1)) = k - 1 := by
  simp [widthSum, balanced]

theorem spike_le_peak {k : Nat} (top : Fin k) (word : List (Op k)) :
    k - 1 ≤ (scan word (fresh (balanced top 0 (k - 1)))).peak := by
  have hi : k - 1 ≤ (fresh (balanced top 0 (k - 1))).peak := by
    have hm := Finset.le_sup (f := balanced top 0 (k - 1)) (Finset.mem_univ top)
    simpa [fresh, balanced] using hm
  exact hi.trans (incoming_peak_le_scan word _)

theorem paid_le_two_peaks {k : Nat} (top : Fin k)
    (word : List (Instruction k))
    (hclosed : runRows word (identity k) = some (identity k)) :
    totalPaid word ≤
      min (k * (scan (widthWord word) (fresh (balanced top 0 0))).peak)
        (k * ((scan (widthWord word)
          (fresh (balanced top 0 (k - 1)))).peak - (k - 1)) +
          (k - 1)^2) := by
  let w0 := balanced top 0 0
  let w1 := balanced top 0 (k - 1)
  let p0 := (scan (widthWord word) (fresh w0)).peak
  let p1 := (scan (widthWord word) (fresh w1)).peak
  have hbalance := closed_shift_balance word hclosed
  have hn0 := (Paper.RowMass.runRows_mass_noUnderflow w0 word (identity k) hclosed).1
  have hn1 := (Paper.RowMass.runRows_mass_noUnderflow w1 word (identity k) hclosed).1
  have ha0 := scanner_word_account word w0 hn0
  have ha1 := scanner_word_account word w1 hn1
  have hb0 := fresh_sum_le_peak (widthWord word) w0
  have hb1 := fresh_sum_le_peak (widthWord word) w1
  have hs0 := initial_sum_zero top
  have hs1 := initial_sum_spike top
  have hp1 := spike_le_peak top (widthWord word)
  have htop := top.isLt
  have hk : k - 1 + 1 = k := by omega
  change widthSum w0 = 0 at hs0
  change widthSum w1 = k - 1 at hs1
  change k - 1 ≤ p1 at hp1
  change widthSum (runWidths (widthWord word) w0) ≤ k * p0 at hb0
  change widthSum (runWidths (widthWord word) w1) ≤ k * p1 at hb1
  rw [hbalance] at ha0 ha1
  apply le_min
  · change totalPaid word ≤ k * p0
    omega
  · change totalPaid word ≤ k * (p1 - (k - 1)) + (k - 1)^2
    have hsub : p1 = (p1 - (k - 1)) + (k - 1) := by omega
    nlinarith

theorem charge_le_three_paid {k : Nat} (op : Instruction k) :
    charge op ≤ 3 * paidOps op := by
  cases op <;> simp [charge, paidOps]
  split <;> omega

theorem word_charge_le_three_paid {k : Nat} (word : List (Instruction k)) :
    wordCharge word ≤ 3 * totalPaid word := by
  induction word with
  | nil => simp [wordCharge, totalPaid]
  | cons op rest ih =>
      have hop := charge_le_three_paid op
      simp only [wordCharge, totalPaid, List.map_cons, List.sum_cons] at *
      omega

theorem source_charge_eq {k : Nat} (ops : TableGeneration.Prog k) :
    Paper.PPEndToEnd.chargedCount ops =
      wordCharge (Paper.SourceBridge.mapToFull ops) := by
  have hf : (Paper.PPEndToEnd.chargedOp : TableGeneration.Operations.valid_ops k → Nat) =
      (fun op => FullDSL.charge (Paper.SourceBridge.toFull op)) := by
    funext op
    cases op <;> simp [Paper.PPEndToEnd.chargedOp,
      Paper.SourceBridge.toFull, FullDSL.charge]
  simp [Paper.PPEndToEnd.chargedCount, wordCharge,
    Paper.SourceBridge.mapToFull, List.map_map, hf, Function.comp_def]

theorem source_charged_bound {k : Nat} (top : Fin k)
    (ops : TableGeneration.Prog k)
    (hclosed : runRows (Paper.SourceBridge.mapToFull ops) (identity k) =
      some (identity k)) :
    let p := Paper.SourceBridge.sourceProfile top ops
    let t := totalPaid (Paper.SourceBridge.mapToFull ops)
    t ≤ min (k * p.peakA) (k * p.peakB + (k - 1)^2) ∧
      Paper.PPEndToEnd.chargedCount ops ≤ 3 * t := by
  dsimp
  constructor
  · simpa [Paper.SourceBridge.sourceProfile] using
      paid_le_two_peaks top (Paper.SourceBridge.mapToFull ops) hclosed
  · rw [source_charge_eq]
    exact word_charge_le_three_paid _

end Paper.ScannerPotential