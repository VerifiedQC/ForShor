import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Table.Contract
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Support.Mirror
import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Proofs.Support.Language
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Registers
import Mathlib.Tactic
/-!
# PTP register-width soundness

The value machine of one PTP operand: `k` limb registers holding integers,
transformed by the table's operations. Two semantics:

* exact, `runF id`: unbounded integers;
* wrapping at width `C`, `runF (Shor.tcWrapInt C)`: every written value is
  reduced to `C`-bit two's complement, which is what ForShor's `LowGate`
  adders/negators/shifters do on a width-`C` register
  (`Shor.extToInt_addScaledBasis_dst` etc.).

Results:

* `scan_sound`: the PTP magnitude scan is sound: if every register starts with
  `|v| < 2 ^ w_i`, every register value at every step stays below
  `2 ^ scanMax w ops` (shifts must be exact, which a successful run gives);
* `init_bound`: the top-heavy limbs of a signed width-`nW` operand meet the
  scan's initial bounds;
* `runF_wrap_eq`: if every value along the run is below `2 ^ (C - 1)`,
  wrapping at `C` changes nothing;
* `node_width_sound` (headline): for a table passing the PTP contract and three
  operands that fit their signed widths, every intermediate register value and
  every child operand of each of the three operands fits signed
  `childWidth3 n ops` bits, the wrapping run equals the exact run, the child
  operands are the declared-point values, and the run returns the limbs.
-/

namespace Shor
namespace PTP

open Operations

/-! ## List facts for the scan -/

theorem foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | y :: l, a => by
      obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
      refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_trans (le_max_right _ _) h1
      · exact h2 x hx

theorem get_le_wMax {k : Nat} (w : Widths) (i : Fin k) : wget w i ≤ wMax w := by
  unfold wget wMax
  rw [List.getD_eq_getElem?_getD]
  rcases h : w[i.1]? with _ | v
  · simp
  · simp only [Option.getD_some]
    exact (foldl_max_ge w 0).2 v (List.mem_of_getElem? h)

theorem get_set_self {k : Nat} (w : Widths) (i : Fin k) (hw : w.length = k) (v : Nat) :
    wget (w.set i.1 v) i = v := by
  unfold wget
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  simp [hw]

theorem get_set_ne {k : Nat} (w : Widths) (i j : Fin k) (h : j ≠ i) (v : Nat) :
    wget (w.set i.1 v) j = wget w j := by
  unfold wget
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  have : ¬ (i.1 = j.1) := fun e => h (Fin.ext e.symm)
  simp [this]

theorem wStep_length {k : Nat} (w : Widths) (op : valid_ops k) :
    (wStep w op).length = w.length := by
  cases op <;> simp [wStep]

/-! ## The value machine -/

/-- Register values of one operand. -/
abbrev Vals (k : Nat) := Fin k → ℤ

/-- Overwrite one register (the same `if` the Framework's `State.setReg` uses). -/
def upd {k : Nat} (V : Vals k) (i : Fin k) (v : ℤ) : Vals k :=
  fun j => if j = i then v else V j

/-- One operation; `f` is applied to the written value (`id`: exact;
`tcWrapInt C`: wrapping at width `C`). -/
def vStepF {k : Nat} (f : ℤ → ℤ) (V : Vals k) : valid_ops k → Vals k
  | .shiftL i n => upd V i (f (V i * 2 ^ n))
  | .shiftR i n => upd V i (f (V i / 2 ^ n))
  | .negate i => upd V i (f (-V i))
  | .addScaled d s neg sh => upd V d (f (V d + (if neg then -1 else 1) * V s * 2 ^ sh))
  | .phaseProduct _ => V

/-- Run the program: the register value at each `phaseProduct` checkpoint (in
order) and the final registers. -/
def runF {k : Nat} (f : ℤ → ℤ) : Vals k → Prog k → List ℤ × Vals k
  | V, [] => ([], V)
  | V, .phaseProduct i :: ops => ((V i) :: (runF f V ops).1, (runF f V ops).2)
  | V, .shiftL i n :: ops => runF f (vStepF f V (.shiftL i n)) ops
  | V, .shiftR i n :: ops => runF f (vStepF f V (.shiftR i n)) ops
  | V, .negate i :: ops => runF f (vStepF f V (.negate i)) ops
  | V, .addScaled d s neg sh :: ops => runF f (vStepF f V (.addScaled d s neg sh)) ops

theorem runF_cons {k : Nat} (f : ℤ → ℤ) (V : Vals k) (op : valid_ops k) (ops : Prog k) :
    runF f V (op :: ops) =
      match op with
      | .phaseProduct i => ((V i) :: (runF f V ops).1, (runF f V ops).2)
      | op => runF f (vStepF f V op) ops := by
  cases op <;> rfl

/-- Every register value in every state of the exact run is below `2 ^ B`. -/
def AllBounded {k : Nat} (B : Nat) : Vals k → Prog k → Prop
  | V, [] => ∀ i, |V i| < 2 ^ B
  | V, op :: ops => (∀ i, |V i| < 2 ^ B) ∧ AllBounded B (vStepF id V op) ops

/-- Every register value in every state of the exact run fits signed `C` bits. -/
def AllFits {k : Nat} (C : Nat) : Vals k → Prog k → Prop
  | V, [] => ∀ i, Shor.FitsSignedWidth C (V i)
  | V, op :: ops => (∀ i, Shor.FitsSignedWidth C (V i)) ∧ AllFits C (vStepF id V op) ops

/-- A right shift is exact on `V` (other operations: no condition). -/
def ShiftExact {k : Nat} (V : Vals k) : valid_ops k → Prop
  | .shiftR i n => (2 : ℤ) ^ n ∣ V i
  | _ => True

/-- Every right shift of the exact run is exact. -/
def ExactShifts {k : Nat} : Vals k → Prog k → Prop
  | _, [] => True
  | V, op :: ops => ShiftExact V op ∧ ExactShifts (vStepF id V op) ops

theorem AllBounded.head {k : Nat} {B : Nat} {V : Vals k} {ops : Prog k}
    (h : AllBounded B V ops) : ∀ i, |V i| < 2 ^ B := by
  cases ops with
  | nil => exact h
  | cons _ _ => exact h.1

theorem AllBounded.mono {k : Nat} {B B' : Nat} (hB : B ≤ B') :
    ∀ {V : Vals k} {ops : Prog k}, AllBounded B V ops → AllBounded B' V ops := by
  have hp : (2 : ℤ) ^ B ≤ 2 ^ B' := pow_le_pow_right₀ (by norm_num) hB
  intro V ops
  induction ops generalizing V with
  | nil => intro h i; exact lt_of_lt_of_le (h i) hp
  | cons op ops ih =>
      intro h
      exact ⟨fun i => lt_of_lt_of_le (h.1 i) hp, ih h.2⟩

/-- `|v| < 2 ^ (C - 1)` with `0 < C` is signed `C`-bit fit. -/
theorem fits_of_abs_lt {C : Nat} (hC : 0 < C) {v : ℤ} (h : |v| < 2 ^ (C - 1)) :
    Shor.FitsSignedWidth C v := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  refine ⟨hC, ?_, ?_⟩
  · unfold Shor.signedMin; push_cast; linarith
  · unfold Shor.signedMax; push_cast; linarith

theorem AllBounded.allFits {k : Nat} {C : Nat} (hC : 0 < C) :
    ∀ {V : Vals k} {ops : Prog k}, AllBounded (C - 1) V ops → AllFits C V ops := by
  intro V ops
  induction ops generalizing V with
  | nil => intro h i; exact fits_of_abs_lt hC (h i)
  | cons op ops ih => intro h; exact ⟨fun i => fits_of_abs_lt hC (h.1 i), ih h.2⟩

/-! ## Soundness of one scan transition -/

theorem abs_pow_two_mul {a : ℤ} {w n : Nat} (h : |a| < 2 ^ w) : |a * 2 ^ n| < 2 ^ (w + n) := by
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ n), pow_add]
  exact mul_lt_mul_of_pos_right h (by positivity)

theorem abs_ediv_pow_two {a : ℤ} {w n : Nat} (h : |a| < 2 ^ w) (hd : (2 : ℤ) ^ n ∣ a) :
    |a / 2 ^ n| < 2 ^ (w - n) := by
  obtain ⟨q, rfl⟩ := hd
  have h2 : (2 : ℤ) ^ n ≠ 0 := by positivity
  rw [Int.mul_ediv_cancel_left _ h2]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ n)] at h
  by_cases hn : n ≤ w
  · have hw : (2 : ℤ) ^ w = 2 ^ n * 2 ^ (w - n) := by
      rw [← pow_add]; congr 1; omega
    rw [hw] at h
    exact lt_of_mul_lt_mul_left h (by positivity)
  · have hw : (2 : ℤ) ^ w ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    have hq : |q| < 1 := by
      by_contra hc
      push Not at hc
      have : (2 : ℤ) ^ n * 1 ≤ 2 ^ n * |q| := mul_le_mul_of_nonneg_left hc (by positivity)
      linarith
    have : w - n = 0 := by omega
    rw [this]; simpa using hq

theorem abs_addScaled {a b : ℤ} {wa wb sh : Nat} (neg : Bool) (ha : |a| < 2 ^ wa)
    (hb : |b| < 2 ^ wb) :
    |a + (if neg then -1 else 1) * b * 2 ^ sh| < 2 ^ (1 + max wa (wb + sh)) := by
  have hb' : |(if neg then -1 else 1) * b * 2 ^ sh| < 2 ^ (wb + sh) := by
    have : |(if neg then (-1 : ℤ) else 1) * b * 2 ^ sh| = |b * 2 ^ sh| := by
      cases neg <;> simp [abs_mul]
    rw [this]; exact abs_pow_two_mul hb
  have h1 : (2 : ℤ) ^ wa ≤ 2 ^ max wa (wb + sh) := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have h2 : (2 : ℤ) ^ (wb + sh) ≤ 2 ^ max wa (wb + sh) :=
    pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
  calc |a + (if neg then -1 else 1) * b * 2 ^ sh|
      ≤ |a| + |(if neg then -1 else 1) * b * 2 ^ sh| := abs_add_le _ _
    _ < 2 ^ max wa (wb + sh) + 2 ^ max wa (wb + sh) := by linarith
    _ = 2 ^ (1 + max wa (wb + sh)) := by rw [pow_add]; ring

/-- One scan transition is sound for one operand. -/
theorem step_sound {k : Nat} (w : Widths) (hw : w.length = k) (V : Vals k)
    (hV : ∀ i, |V i| < 2 ^ (wget w i)) (op : valid_ops k)
    (hx : ShiftExact V op) :
    ∀ j, |vStepF id V op j| < 2 ^ (wget (wStep w op) j) := by
  intro j
  cases op with
  | shiftL i n =>
      simp only [vStepF, wStep, upd, id]
      by_cases hj : j = i
      · subst hj; simp only [↓reduceIte]; rw [get_set_self w j hw]; exact abs_pow_two_mul (hV j)
      · simp only [hj, ↓reduceIte]; rw [get_set_ne w i j hj]; exact hV j
  | shiftR i n =>
      simp only [vStepF, wStep, upd, id]
      by_cases hj : j = i
      · subst hj; simp only [↓reduceIte]; rw [get_set_self w j hw]; exact abs_ediv_pow_two (hV j) hx
      · simp only [hj, ↓reduceIte]; rw [get_set_ne w i j hj]; exact hV j
  | negate i =>
      simp only [vStepF, wStep, upd, id]
      by_cases hj : j = i
      · subst hj; simp only [↓reduceIte]; rw [abs_neg]; exact hV j
      · simp only [hj, ↓reduceIte]; exact hV j
  | addScaled d s neg sh =>
      simp only [vStepF, wStep, upd, id]
      by_cases hj : j = d
      · subst hj; simp only [↓reduceIte]; rw [get_set_self w j hw]
        exact abs_addScaled neg (hV j) (hV s)
      · simp only [hj, ↓reduceIte]; rw [get_set_ne w d j hj]; exact hV j
  | phaseProduct i => simpa [vStepF, wStep] using hV j

/-- **Scan soundness.** Starting within the bounds `w`, with exact shifts, every
register value along the exact run is below `2 ^ scanMax w ops`. -/
theorem scan_sound {k : Nat} :
    ∀ (ops : Prog k) (w : Widths) (V : Vals k), w.length = k →
      (∀ i, |V i| < 2 ^ (wget w i)) → ExactShifts V ops → AllBounded (scanMax w ops) V ops
  | [], w, V, _, hV, _ => fun i =>
      lt_of_lt_of_le (hV i) (pow_le_pow_right₀ (by norm_num) (get_le_wMax w i))
  | op :: ops, w, V, hw, hV, hx => by
      refine ⟨fun i => lt_of_lt_of_le (hV i) (pow_le_pow_right₀ (by norm_num)
        (le_trans (get_le_wMax w i) (le_max_left _ _))), ?_⟩
      have ih := scan_sound ops (wStep w op) (vStepF id V op) (by rw [wStep_length, hw])
        (step_sound w hw V hV op hx.1) hx.2
      exact AllBounded.mono (le_max_right _ _) ih

/-! ## Initial bounds of the top-heavy split -/

theorem lowerBound_le (nW W k : Nat) (hk : 0 < k) (hn : 0 < nW) (hW : W ≤ nW / k) :
    (k - 1) * W ≤ nW - 1 := by
  set q := nW / k with hq
  have h1 : (k - 1) * W ≤ (k - 1) * q := Nat.mul_le_mul_left _ hW
  have h2 : k * q ≤ nW := by rw [hq, Nat.mul_comm]; exact Nat.div_mul_le_self nW k
  have h3 : (k - 1) * q + q = k * q := by
    conv_rhs => rw [show k = (k - 1) + 1 by omega]
    ring
  by_cases hq0 : q = 0
  · rw [hq0, Nat.mul_zero] at h1; omega
  · omega

theorem init_get (nW W k : Nat) (i : Fin k) :
    wget (initW nW W k) i = if i.1 + 1 = k then nW - (k - 1) * W else W := by
  unfold initW wget
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.2]

theorem initW_length (nW W k : Nat) : (initW nW W k).length = k := by
  simp [initW]

/-- The top-heavy limbs of a signed width-`nW` operand meet the scan's initial
bounds: lower limbs are below `2 ^ W`, the top limb below `2 ^ (nW - (k-1) W)`. -/
theorem init_bound (nW W k : Nat) (hk : 0 < k) (hm : (k - 1) * W ≤ nW - 1) (x : ℤ)
    (hx : Shor.FitsSignedWidth nW x) :
    ∀ i : Fin k, |limbs k ((2 : ℤ) ^ W) x i| < 2 ^ (wget (initW nW W k) i) := by
  intro i
  obtain ⟨hn, hlo, hhi⟩ := hx
  unfold Shor.signedMin at hlo
  unfold Shor.signedMax at hhi
  push_cast at hlo hhi
  rw [init_get]
  unfold limbs
  by_cases ht : i.1 + 1 = k
  · simp only [ht, ↓reduceIte]
    have hi : (i : ℕ) = k - 1 := by omega
    rw [hi, ← pow_mul]
    set m := W * (k - 1) with hmdef
    have hm' : m ≤ nW - 1 := by rw [hmdef, Nat.mul_comm]; exact hm
    set e := nW - 1 - m with he
    have hsplit : (2 : ℤ) ^ (nW - 1) = 2 ^ e * 2 ^ m := by rw [← pow_add]; congr 1; omega
    have hpos : (0 : ℤ) < 2 ^ m := by positivity
    have hup : x / 2 ^ m < 2 ^ e := by
      rw [Int.ediv_lt_iff_lt_mul hpos]; linarith
    have hdown : -(2 : ℤ) ^ e ≤ x / 2 ^ m := by
      rw [Int.le_ediv_iff_mul_le hpos]; nlinarith
    have hexp : nW - (k - 1) * W = e + 1 := by
      rw [he, hmdef, Nat.mul_comm]; omega
    rw [hexp, abs_lt]
    constructor
    · have : (2 : ℤ) ^ e < 2 ^ (e + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith
    · have : (2 : ℤ) ^ e < 2 ^ (e + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith
  · simp only [ht, ↓reduceIte]
    have hB : (0 : ℤ) < 2 ^ W := by positivity
    rw [abs_of_nonneg (Int.emod_nonneg _ (ne_of_gt hB))]
    exact Int.emod_lt_of_pos _ hB

/-! ## Wrapping equals exact -/

theorem vStepF_wrap_eq {k : Nat} {C : Nat} (hC : 0 < C) (V : Vals k) (op : valid_ops k)
    (h : ∀ j, |vStepF id V op j| < 2 ^ (C - 1)) :
    vStepF (Shor.tcWrapInt C) V op = vStepF id V op := by
  have key : ∀ (i : Fin k) (v : ℤ), |upd V i v i| < 2 ^ (C - 1) →
      upd V i (Shor.tcWrapInt C v) = upd V i v := by
    intro i v hv
    have : upd V i v i = v := by simp [upd]
    rw [this] at hv
    rw [Shor.tcWrapInt_eq_of_fits hC (fits_of_abs_lt hC hv)]
  cases op with
  | shiftL i n => exact key i _ (h i)
  | shiftR i n => exact key i _ (h i)
  | negate i => exact key i _ (h i)
  | addScaled d s neg sh => exact key d _ (h d)
  | phaseProduct i => rfl

/-- **Wrapping at `C` equals the exact run** when every value along the exact
run is below `2 ^ (C - 1)`. -/
theorem runF_wrap_eq {k : Nat} {C : Nat} (hC : 0 < C) :
    ∀ (ops : Prog k) (V : Vals k), AllBounded (C - 1) V ops →
      runF (Shor.tcWrapInt C) V ops = runF id V ops
  | [], _, _ => rfl
  | op :: ops, V, h => by
      have hnext := h.2
      have hstep := vStepF_wrap_eq hC V op hnext.head
      have ih := runF_wrap_eq hC ops (vStepF id V op) hnext
      cases op with
      | phaseProduct i =>
          simp only [runF]
          have : vStepF id V (.phaseProduct i) = V := rfl
          rw [this] at ih
          rw [ih]
      | shiftL i n => simp only [runF]; rw [hstep, ih]
      | shiftR i n => simp only [runF]; rw [hstep, ih]
      | negate i => simp only [runF]; rw [hstep, ih]
      | addScaled d s neg sh => simp only [runF]; rw [hstep, ih]

/-! ## Link to the Framework's row semantics -/

/-- A register (row of coefficients) read against limb values. -/
def regVal {k : Nat} (r : Register k) (L : Fin k → ℤ) : ℤ := ∑ j, r j * L j

/-- All register values of a row state. -/
def valOf {k : Nat} (σ : State k) (L : Fin k → ℤ) : Vals k := fun i => regVal (σ i) L

theorem valOf_start {k : Nat} (L : Fin k → ℤ) : valOf State.start_state L = L := by
  funext i
  simp [valOf, regVal, State.start_state]

theorem valOf_setReg {k : Nat} (σ : State k) (i : Fin k) (r : Register k) (L : Fin k → ℤ) :
    valOf (State.setReg σ i r) L = upd (valOf σ L) i (regVal r L) := by
  funext j
  simp only [valOf, State.setReg, upd]
  split <;> rfl

/-- One successful table step moves the values by `vStepF id`, and a right shift
that succeeds on the row divides the value exactly. -/
theorem applyOp_val {k : Nat} (σ σ' : State k) (op : valid_ops k) (L : Fin k → ℤ)
    (h : applyOp? σ op = some σ') :
    valOf σ' L = vStepF id (valOf σ L) op ∧ ShiftExact (valOf σ L) op := by
  cases op with
  | shiftL i n =>
      simp only [applyOp?, Option.some.injEq] at h
      subst h
      refine ⟨?_, trivial⟩
      rw [State.shiftLReg, valOf_setReg]
      simp only [vStepF, id]
      congr 1
      simp only [regVal, valOf, Register.shiftL, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
  | shiftR i n =>
      by_cases hdiv : ∀ j, (2 : ℤ) ^ n ∣ σ i j
      · have hσ' : σ' = State.setReg σ i (fun j => σ i j / 2 ^ n) := by
          simp [applyOp?, State.shiftRReg?, Register.shiftR?, hdiv] at h
          exact h.symm
        subst hσ'
        have hsum : regVal (σ i) L = 2 ^ n * regVal (fun j => σ i j / 2 ^ n) L := by
          simp only [regVal, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_assoc, Int.mul_ediv_cancel' (hdiv j)]
        refine ⟨?_, ?_⟩
        · rw [valOf_setReg]
          simp only [vStepF, id, valOf]
          congr 1
          rw [hsum, Int.mul_ediv_cancel_left _ (by positivity)]
        · show (2 : ℤ) ^ n ∣ regVal (σ i) L
          rw [hsum]; exact dvd_mul_right _ _
      · simp [applyOp?, State.shiftRReg?, Register.shiftR?, hdiv] at h
  | negate i =>
      simp only [applyOp?, Option.some.injEq] at h
      subst h
      refine ⟨?_, trivial⟩
      rw [State.negateReg, valOf_setReg]
      simp only [vStepF, id]
      congr 1
      simp only [regVal, valOf, Register.negate, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
  | addScaled d s neg sh =>
      simp only [applyOp?, Option.some.injEq] at h
      subst h
      refine ⟨?_, trivial⟩
      rw [State.addScaledReg, valOf_setReg]
      simp only [vStepF, id]
      congr 1
      simp only [regVal, valOf, Register.addScaled, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by cases neg <;> simp <;> ring
  | phaseProduct i =>
      simp only [applyOp?, Option.some.injEq] at h
      subst h
      exact ⟨rfl, trivial⟩

/-- A successful run has exact shifts and its final values are the values of the
final rows. -/
theorem run_val {k : Nat} (L : Fin k → ℤ) :
    ∀ (ops : Prog k) (σ σ' : State k), run? ops σ = some σ' →
      ExactShifts (valOf σ L) ops ∧ (runF id (valOf σ L) ops).2 = valOf σ' L
  | [], σ, σ', h => by
      simp only [run?, Option.some.injEq] at h
      subst h; exact ⟨trivial, rfl⟩
  | op :: ops, σ, σ', h => by
      simp only [run?] at h
      rcases hσ : applyOp? σ op with _ | σ₁
      · rw [hσ] at h; cases h
      · rw [hσ] at h
        obtain ⟨hv, hx⟩ := applyOp_val σ σ₁ op L hσ
        obtain ⟨ih1, ih2⟩ := run_val L ops σ₁ σ' h
        rw [hv] at ih1 ih2
        refine ⟨⟨hx, ih1⟩, ?_⟩
        cases op with
        | phaseProduct i => simpa [runF, vStepF] using ih2
        | shiftL i n => simpa [runF] using ih2
        | shiftR i n => simpa [runF] using ih2
        | negate i => simpa [runF] using ih2
        | addScaled d s neg sh => simpa [runF] using ih2

/-- The checkpoint values of the exact run are the values of the checkpoint rows. -/
theorem checkpoint_val {k : Nat} (L : Fin k → ℤ) :
    ∀ (ops : Prog k) (σ : State k) (rows : List (Register k)),
      checkpointRows σ ops = some rows →
      (runF id (valOf σ L) ops).1 = rows.map (fun r => regVal r L)
  | [], σ, rows, h => by
      simp only [checkpointRows, Option.some.injEq] at h
      subst h; rfl
  | op :: ops, σ, rows, h => by
      cases op with
      | phaseProduct i =>
          simp only [checkpointRows] at h
          rcases hr : checkpointRows σ ops with _ | rs
          · rw [hr] at h; cases h
          · rw [hr] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            simp only [runF, List.map_cons]
            rw [checkpoint_val L ops σ rs hr]
            rfl
      | _ =>
          simp only [checkpointRows] at h
          rcases hσ : applyOp? σ _ with _ | σ₁
          all_goals first
            | (rw [hσ] at h; cases h)
            | (rw [hσ] at h
               have hv := (applyOp_val σ σ₁ _ L hσ).1
               have ih := checkpoint_val L ops σ₁ rows h
               rw [hv] at ih
               simpa [runF] using ih)

/-! ## Headline: register-width soundness of one PTP node -/

/-- Limbs of operand `x` at lower width `W`. -/
def limbsAt (k W : Nat) (x : ℤ) : Fin k → ℤ := limbs k ((2 : ℤ) ^ W) x

/-- **PTP register-width soundness (one node).** For a table passing the PTP
contract, three operand widths `n s ≥ 1` and operands `x s` fitting signed
`n s` bits, let `C = childWidth3 n T.ops` and `W = limbWidth3 n T.k`. Then for
each of the three operands:

1. every register value at every step of the exact run fits signed `C` bits;
2. the child operands (checkpoint values) are the declared-point values
   `regVal (expectedRow p) limbs` and each fits signed `C` bits;
3. the run with every write wrapped to `C` bits equals the exact run;
4. the run returns the registers to the limbs. -/
theorem node_width_sound (T : PTPTable) (hT : T.contract = true) (n : Fin 3 → Nat)
    (hn : ∀ s, 0 < n s) (x : Fin 3 → ℤ) (hx : ∀ s, Shor.FitsSignedWidth (n s) (x s)) (s : Fin 3) :
    let C := childWidth3 n T.ops
    let L := limbsAt T.k (limbWidth3 n T.k) (x s)
    AllFits C L T.ops ∧
      (runF id L T.ops).1 = T.pts.map (fun p => regVal (expectedRow p) L) ∧
      (∀ v ∈ (runF id L T.ops).1, Shor.FitsSignedWidth C v) ∧
      runF (Shor.tcWrapInt C) L T.ops = runF id L T.ops ∧
      (runF id L T.ops).2 = L := by
  intro C L
  obtain ⟨hk, _, hsafe⟩ := (PTPTable.contract_iff T).mp hT
  have hk0 : 0 < T.k := by omega
  set W := limbWidth3 n T.k with hW
  have hWs : ∀ s, W ≤ n s / T.k := by
    intro s
    simp only [hW, limbWidth3]
    fin_cases s <;> simp
  have hrun := (returnsToStartCheck_iff T.ops State.start_state).mp hsafe.returns_start
  obtain ⟨hex, hfin⟩ := run_val L T.ops State.start_state State.start_state hrun
  rw [valOf_start] at hex hfin
  have hb := scan_sound T.ops (initW (n s) W T.k) L (initW_length _ _ _)
    (init_bound (n s) W T.k hk0 (lowerBound_le _ _ _ hk0 (hn s) (hWs s)) (x s) (hx s)) hex
  have hCpos : 0 < C := by simp [C, childWidth3]
  have hle : scanMax (initW (n s) W T.k) T.ops ≤ C - 1 := by
    simp only [C, childWidth3, ← hW]
    fin_cases s <;> simp
  have hB : AllBounded (C - 1) L T.ops := AllBounded.mono hle hb
  have hrows := checkpointRows_of_consumes (positive_of_ge_two hk) T.ops
    State.start_state T.pts hsafe.consumes
  have hcp := checkpoint_val L T.ops State.start_state _ hrows
  rw [valOf_start, List.map_map] at hcp
  refine ⟨hB.allFits hCpos, hcp, ?_, runF_wrap_eq hCpos T.ops L hB, hfin⟩
  -- every checkpoint value is a register value of some reached state
  have hall : ∀ (ops : Prog T.k) (V : Vals T.k), AllBounded (C - 1) V ops →
      ∀ v ∈ (runF id V ops).1, |v| < 2 ^ (C - 1) := by
    intro ops
    induction ops with
    | nil => intro V _ v hv; simp [runF] at hv
    | cons op ops ih =>
        intro V hV v hv
        cases op with
        | phaseProduct i =>
            simp only [runF, List.mem_cons] at hv
            rcases hv with rfl | hv
            · exact hV.1 i
            · exact ih V hV.2 v hv
        | shiftL i n => exact ih _ hV.2 v (by simpa [runF] using hv)
        | shiftR i n => exact ih _ hV.2 v (by simpa [runF] using hv)
        | negate i => exact ih _ hV.2 v (by simpa [runF] using hv)
        | addScaled d s' neg sh => exact ih _ hV.2 v (by simpa [runF] using hv)
  intro v hv
  exact fits_of_abs_lt hCpos (hall T.ops L hB v hv)

end PTP
end Shor
