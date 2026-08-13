import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Core
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Toom_Cook_formula
/-!
# Phase-Product Compiler Support Lemmas
This file is the reusable proof layer above `PhaseProduct.Core`. It groups the
small but frequently used facts needed by larger correctness proofs: annotation
bookkeeping, signed-width safety, source-row arithmetic, width-scan consequences,
layout extensionality, and the canonical interpolation-point bridge to the pure
Toom-Cook math file.
-/
namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Section 1: Annotation and phase-product counting
    These lemmas are pure program-bookkeeping facts. They keep phase-product
    term indices stable under append and prove that local arithmetic helper
    programs do not introduce recursive phase-product leaves.
========================================================= -/

/-- Compatibility alias for older files: every concrete `Reg` already carries `Nodup`. -/
def WellFormedReg (r : Reg) : Prop := r.qubits.Nodup

@[simp] theorem wellFormedReg (r : Reg) : WellFormedReg r := r.nodup

/-- Annotating phase leaves commutes with appending programs, after shifting the second index. -/
lemma annotatePhaseTermsAux_append (k n : ℕ) (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k n (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k n ops₁ ++
      annotatePhaseTermsAux k (n + phaseProductCount ops₁) ops₂ := by
  induction ops₁ generalizing n with
  | nil =>
      simp [annotatePhaseTermsAux, phaseProductCount]
  | cons op ops₁ ih =>
      cases op <;>simp [annotatePhaseTermsAux, phaseProductCount, ih, Nat.add_assoc, Nat.add_comm]

/-- Append rule specialized to the usual initial phase index `0`. -/
lemma annotatePhaseTermsAux_append_zero (k : ℕ) (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k 0 (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k 0 ops₁ ++
      annotatePhaseTermsAux k (phaseProductCount ops₁) ops₂ := by
  simpa using annotatePhaseTermsAux_append k 0 ops₁ ops₂

/-- Constant-addition helper programs contain no phase-product leaves. -/
@[simp] lemma phaseProductCount_addConstAux
  {k : ℕ} (dst src : Fin k) (neg' : Bool) (n sh : ℕ) :
  phaseProductCount (addConstAux (k := k) dst src neg' n sh) = 0 := by
  rw [addConstAux_eq_shifts (k := k) (dst := dst) (src := src) (neg' := neg') n sh]
  induction shiftsOfAux n sh with
  | nil =>
      simp [phaseProductCount]
  | cons s ss ih =>
      simp [phaseProductCount, ih]

@[simp] lemma phaseProductCount_addConstFrom {k : ℕ} (dst src : Fin k) (c : Int) :
  phaseProductCount (addConstFrom (k := k) dst src c) = 0 := by
  by_cases hc : c = 0 <;> simp [addConstFrom, hc, phaseProductCount, phaseProductCount_addConstAux]

/-- Phase-product leaf counts add over program append. -/
@[simp] lemma phaseProductCount_append
  {k : ℕ} (xs ys : List (valid_ops k)) :
  phaseProductCount (xs ++ ys) =
    phaseProductCount xs + phaseProductCount ys := by
  induction xs with
  | nil =>
      simp [phaseProductCount]
  | cons op xs ih =>
      cases op <;> simp [phaseProductCount, ih,  Nat.add_comm, Nat.add_left_comm]

@[simp] lemma phaseProductCount_computeLocalAux
  {k : ℕ} (hk : 0 < k) (z : Int) :
  ∀ js : List (Fin k), phaseProductCount (computeLocalAux (k := k) hk z js) = 0
  | [] => by
      simp [computeLocalAux, phaseProductCount]
  | j :: js => by
      simp [computeLocalAux, phaseProductCount_append, phaseProductCount_addConstFrom, phaseProductCount_computeLocalAux]

@[simp] lemma phaseProductCount_computeLocal2 {k : ℕ} (hk : 0 < k) (z : Int) :
  phaseProductCount (computeLocal2 (k := k) hk z) = 0 := by simp [computeLocal2, phaseProductCount_computeLocalAux]

@[simp] lemma compileSignedAllocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedAllocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedAllocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedAllocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  compileSignedAllocationsAux src dst n hk' ;;
  allocChunkGate i (src.xslot i) (dst.xslot i) ;;
  allocChunkGate i (src.zslot i) (dst.zslot i) := rfl

@[simp] lemma compileSignedDeallocationsAux_zero {k : ℕ} (src dst : LayoutState k) (h : 0 ≤ k) :
  compileSignedDeallocationsAux src dst 0 h = Gate.id := rfl

@[simp] lemma compileSignedDeallocationsAux_succ {k : ℕ} (src dst : LayoutState k)
  (n : ℕ) (hn : n + 1 ≤ k) :
  compileSignedDeallocationsAux src dst (n + 1) hn
    =
  let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
  let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
  deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
  compileSignedDeallocationsAux src dst n hk' := rfl

variable (qs : QSemantics) [RegEncoding qs.Basis]

/-! =========================================================
    Section 2: Width scans and signed-fit safety
    This section turns symbolic width scans into usable signed-fit obligations.
    It also packages the arithmetic safety facts for shift, negate, and add-scaled
    source rows.
========================================================= -/

/-- Drop the scan-width bookkeeping from the stronger body invariant. -/
lemma EncodesStateFromWithWidths.toFits
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    {src dst : LayoutState k}
    {cur : WidthState k}
    {σ : State k}
    {b0 b : qs.Basis}
    (h :
      EncodesStateFromWithWidths
        (qs := qs)
        src dst cur σ b0 b) :
    EncodesStateFromFits
      (qs := qs)
      src dst σ b0 b := by
  rcases h with
    ⟨hEnc, ⟨hSoundX, hSoundZ⟩,
      ⟨hDomX, hDomZ⟩⟩
  refine ⟨hEnc, ?_, ?_⟩
  · intro i
    exact FitsSignedWidth_mono
      (hDomX i)
      (hSoundX i)
  · intro i
    exact FitsSignedWidth_mono
      (hDomZ i)
      (hSoundZ i)

/-- Unfolding lemma for the public width scanner. -/
lemma scanNeededWidths_eq_aux {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
  scanNeededWidths x z ops = scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops := by
  simp [scanNeededWidths]

/-- The scan result dominates the incoming `x` width lower bound. -/
lemma scanNeededWidthsAux_x_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.xneed i ≤ (scanNeededWidthsAux cur mx ops).xneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).xneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).xneed i :=
        scanNeededWidthsAux_x_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- The scan result dominates the incoming `z` width lower bound. -/
lemma scanNeededWidthsAux_z_ge
  {k : ℕ} (i : Fin k) :
  ∀ (ops : List (valid_ops k)) (cur : WidthState k) (mx : NeededWidths k),
    mx.zneed i ≤ (scanNeededWidthsAux cur mx ops).zneed i
  | [], cur, mx => by
      simp [scanNeededWidthsAux]
  | op :: rest, cur, mx => by
      simp [scanNeededWidthsAux]
      have htail :
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op))).zneed i
            ≤
          (scanNeededWidthsAux
              (updateWidthState cur op)
              (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
              rest).zneed i :=
        scanNeededWidthsAux_z_ge
          (i := i)
          rest
          (updateWidthState cur op)
          (mergeNeededWidths mx (widthsOfState (updateWidthState cur op)))
      exact le_trans (le_max_left _ _) htail

/-- An unsigned value below `2^w` fits in signed width `w+1`. -/
lemma FitsSignedWidth_of_nonneg_lt_pow
  {w : ℕ} {n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (n : ℤ) := by
  unfold FitsSignedWidth signedMin signedMax
  constructor <;> simp
  constructor
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
    have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
    omega
  omega
  norm_cast

/-- Decoding any `w`-bit pattern gives a signed value fitting width `w+1`. -/
lemma tcDecodeWidth_fits_succ
  {w n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (tcDecodeWidth w n) := by
  unfold FitsSignedWidth signedMin signedMax tcDecodeWidth
  by_cases hs : n < 2 ^ (w - 1)
  · simp
    constructor <;> split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      have hneg : (-(2 : ℤ) ^ (w + 1)) ≤ 0 := by
        have hpow0 : (0 : ℤ) ≤ (2 : ℤ) ^ (w + 1) := by positivity
        omega
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
    norm_cast
  · simp
    constructor <;> split
    next x x_1 =>
      simp_all only [pow_zero, Nat.lt_one_iff, zero_tsub, zero_lt_one, Int.reduceNeg, Left.neg_nonpos_iff,
        zero_le_one]
      simp at hs
    next x x_1 w =>
      simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, ↓reduceIte]
      have hge : 2 ^ w ≤ n := Nat.le_of_not_lt hs
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast Nat.zero_le n
      omega
    simp
    simp_all only [Nat.succ_eq_add_one, add_tsub_cancel_right, not_lt]
    split
    next h_1 => norm_cast
    next h_1 =>
      simp_all only [not_lt]; rename_i x1 x w
      have hlt : (n : ℤ) < (2 : ℤ) ^ (w + 1) := by
        exact_mod_cast h
      omega

/-- Child registers from the same split layout inherit owned-disjointness. -/
lemma phaseSplitChild_owned_disjoint {parent : ExtReg} {k W : ℕ} (layout : PhaseSplitLayout parent k W) {i j : Fin k} (hij : i ≠ j) :
    ExtReg.OwnedDisjoint (layout.child i) (layout.child j) := layout.child_owned_disjoint hij

/-- Cross operand children of a phase-product layout are owned-disjoint. -/
lemma phaseProductLayout_cross_disjoint {x z : ExtReg} {k : ℕ} (layout : Gate.PhaseProductLayout x z k) (i j : Fin k) :
    ExtReg.OwnedDisjoint (layout.xSplit.child i) (layout.zSplit.child j) := layout.cross_owned_disjoint i j

/-- The signed interpretation of an `ExtReg` always fits one bit wider than its active width. -/
lemma extToInt_fits_width_succ (e : ExtReg) (b : qs.Basis) : FitsSignedWidth (ExtReg.width e + 1) (extToInt e b) := by
  unfold extToInt
  exact tcDecodeWidth_fits_succ (by simpa using (ExtReg.toNat_lt (Basis := qs.Basis) (e := e) (b := b)))

/-- If `z` fits signed width `w+1`, then `(2^n) * z` fits signed width `w+n+1`. -/
lemma FitsSignedWidth_shiftL_raw
  {w n : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + n + 1) (((2 : ℤ)^n) * z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hp0 : (0 : ℤ) ≤ (2 : ℤ)^n := by positivity
  have hp : (0 : ℤ) < (2 : ℤ)^n := by positivity
  have hpow :
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
        = (((2 ^ (w + n) : ℕ) : ℤ)) := by
    calc
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ))
          = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ n * 2 ^ w : ℕ) : ℤ)) := by norm_num
      _ = (((2 ^ (n + w) : ℕ) : ℤ)) := by
            exact_mod_cast (pow_add 2 n w).symm
      _ = (((2 ^ (w + n) : ℕ) : ℤ)) := by rw [Nat.add_comm]
  have hpow_neg :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        = -(((2 ^ (w + n) : ℕ) : ℤ)) := by
    simp
    rw[pow_add,mul_comm]
  have hL :
      ((2 : ℤ)^n) * (-(((2 ^ w : ℕ) : ℤ)))
        ≤
      ((2 : ℤ)^n) * z := by
    exact mul_le_mul_of_nonneg_left (by simp_all) hp0
  have hU :
      ((2 : ℤ)^n) * z
        <
      ((2 : ℤ)^n) * (((2 ^ w : ℕ) : ℤ)) := by
    exact mul_lt_mul_of_pos_left (by simp_all) hp
  constructor
  · simp
  · aesop

/-- If `z = 2^n * q` and `z` fits signed width `w+1`, then the exact quotient
    fits signed width `(w - n) + 1`. -/
lemma FitsSignedWidth_shiftR_of_mul
  {w n : ℕ} {z q : ℤ}
  (hfit : FitsSignedWidth (w + 1) z)
  (hz : z = ((2 : ℤ)^n) * q) :
  FitsSignedWidth (w - n + 1) q := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  by_cases hnw : n ≤ w
  · have hpos : (0 : ℤ) < (2 : ℤ)^n := by positivity
    have hpow :
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
          = (((2 ^ w : ℕ) : ℤ)) := by
      calc
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ))
            = (((2 ^ n : ℕ) : ℤ)) * (((2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ n * 2 ^ (w - n) : ℕ) : ℤ)) := by norm_num
        _ = (((2 ^ (n + (w - n)) : ℕ) : ℤ)) := by
              exact_mod_cast (pow_add 2 n (w - n)).symm
        _ = (((2 ^ w : ℕ) : ℤ)) := by rw [Nat.add_sub_of_le hnw]
    have hupper :
        ((2 : ℤ)^n) * q
          <
        ((2 : ℤ)^n) * (((2 ^ (w - n) : ℕ) : ℤ)) := by
      simp_all
    have hlower :
        ((2 : ℤ)^n) * (-(((2 ^ (w - n) : ℕ) : ℤ)))
          ≤
        ((2 : ℤ)^n) * q := by
      have : -(((2 ^ w : ℕ) : ℤ)) ≤ ((2 : ℤ)^n) * q := by
        simp_all
      simp_all
    constructor
    · simp_all
    · simp_all
      constructor
      · have h1 : -(2 ^ n * 2 ^ (w - n) : ℤ) ≤ 2 ^ n * q := by
          rw [hpow]; exact hhi.1
        have h2 : (2 ^ n : ℤ) * -(2 ^ (w - n)) ≤ 2 ^ n * q := by
          rw [mul_neg]; exact h1
        exact le_of_mul_le_mul_left h2 (by positivity)
      · have h1 : (2 ^ n * q : ℤ) < 2 ^ n * 2 ^ (w - n) := by
          rw [hpow]; exact hhi.2
        exact lt_of_mul_lt_mul_left h1 (by positivity)
  · have hwn : w < n := lt_of_not_ge hnw
    have hpowNat : 2 ^ w < 2 ^ n := by
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) hwn
    have hpowInt : (((2 ^ w : ℕ) : ℤ)) < ((2 : ℤ)^n) := by
      exact_mod_cast hpowNat
    have hq0 : q = 0 := by
      by_cases hq : q = 0
      · exact hq
      · rcases lt_or_gt_of_ne hq with hqneg | hqpos
        · have hqle : q ≤ -1 := by omega
          have hmul : ((2 : ℤ)^n) * q ≤ -((2 : ℤ)^n) := by
            calc
              ((2 : ℤ)^n) * q ≤ ((2 : ℤ)^n) * (-1) := by
                gcongr
              _ = -((2 : ℤ)^n) := by ring
          have hzlt : z < -(((2 ^ w : ℕ) : ℤ)) := by
            rw [hz]
            have hnegpow : -((2 : ℤ)^n) < -(((2 ^ w : ℕ) : ℤ)) := by
              omega
            exact lt_of_le_of_lt hmul hnegpow
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega
        · have hqge : (1 : ℤ) ≤ q := by omega
          have hmul : ((2 : ℤ)^n) ≤ ((2 : ℤ)^n) * q := by
            calc
              ((2 : ℤ)^n) = ((2 : ℤ)^n) * 1 := by ring
              _ ≤ ((2 : ℤ)^n) * q := by
                gcongr
          have hzgt : (((2 ^ w : ℕ) : ℤ)) < z := by
            rw [hz]
            exact lt_of_lt_of_le hpowInt hmul
          simp_all
          rcases hhi with ⟨hlo, hhi⟩
          omega
    subst hq0
    have hw0 : w - n = 0 := by omega
    rw [hw0]
    constructor <;> norm_num [signedMin, signedMax]

/-- Negation is always safe if we widen by one additional bit. -/
lemma FitsSignedWidth_neg_widen
  {w : ℕ} {z : ℤ}
  (hfit : FitsSignedWidth (w + 1) z) :
  FitsSignedWidth (w + 2) (-z) := by
  unfold FitsSignedWidth signedMin signedMax at hfit ⊢
  rcases hfit with ⟨hlo, hhi⟩
  have hpow : (((2 ^ w : ℕ) : ℤ)) ≤ (((2 ^ (w + 1) : ℕ) : ℤ)) := by
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ w))
  constructor <;> simp_all
  refine ⟨?_, ?_⟩
  · linarith [hhi.2, hpow]
  · have hpos : (0 : ℤ) < 2 ^ w := by positivity
    omega

/-- Adding a shifted source into a destination is safe in the width prescribed
    by `updateWidthState` (plus the proof-only extra sign bit). -/

lemma FitsSignedWidth_addScaled_widen
  {wd ws sh : ℕ} {dstv srcv : ℤ} (negSrc : Bool)
  (hdst : FitsSignedWidth (wd + 1) dstv)
  (hsrc : FitsSignedWidth (ws + 1) srcv) :
  FitsSignedWidth (max wd (ws + sh) + 2)
    (dstv + (if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ)^sh) * srcv) := by
  have hscaled :
      FitsSignedWidth (ws + sh + 1) (((2 : ℤ)^sh) * srcv) := by
    exact FitsSignedWidth_shiftL_raw (w := ws) (n := sh) (z := srcv) hsrc
  unfold FitsSignedWidth signedMin signedMax at hdst hscaled ⊢
  rcases hdst with ⟨hdlo, hdhi⟩
  rcases hscaled with ⟨hslo, hshi⟩
  set M : ℕ := max wd (ws + sh)
  have hwdM : (((2 ^ wd : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_left wd (ws + sh)))
  have hwsM : (((2 ^ (ws + sh) : ℕ) : ℤ)) ≤ (((2 ^ M : ℕ) : ℤ)) := by
    dsimp [M]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right wd (ws + sh)))
  cases hsgn : negSrc <;> simp_all
  · constructor <;> omega
  · constructor <;> omega

/-! =========================================================
    Section 3: Concrete split layouts and budgeted construction

    These arithmetic and list-slicing facts turn the abstract top-heavy layout
    definitions from `Core` into concrete child registers. They live here because
    they are proof/construction support rather than compiler data definitions.
========================================================= -/

/-- The top chunk of a valid top-heavy split has positive width when the parent does. -/
lemma phaseLimbWidth_top_nonempty
    (w other k : ℕ)
    (hk : 0 < k) :
    w = 0 ∨
      (k - 1) * min (w / k) (other / k) < w := by
  by_cases hw : w = 0
  · exact Or.inl hw
  right
  have hwpos : 0 < w := Nat.pos_of_ne_zero hw
  let q := w / k
  have hW :
      min (w / k) (other / k) ≤ q := by
    exact Nat.min_le_left _ _
  have hleft :
      (k - 1) * min (w / k) (other / k)
        ≤
      (k - 1) * q :=
    Nat.mul_le_mul_left _ hW
  have hkpred : k - 1 < k := by
    omega
  by_cases hq : q = 0
  · have hmin_zero :
        min (w / k) (other / k) = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [hq] using hW)
    simp [hmin_zero]
    exact hwpos
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hstrict :
        (k - 1) * q < k * q :=
      Nat.mul_lt_mul_of_pos_right hkpred hqpos
    have hdiv :
        k * q ≤ w := by
      dsimp [q]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self w k
    exact lt_of_le_of_lt hleft
      (lt_of_lt_of_le hstrict hdiv)

lemma phaseLimbWidth_valid_left
    (x z : ExtReg)
    {k : ℕ}
    (hk : 0 < k) :
    ValidPhaseSplit x k (phaseLimbWidth x z k) := by
  refine ⟨hk, ?_, ?_⟩
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    have hW :
        min (x.width / k) (z.width / k)
          ≤ x.width / k :=
      Nat.min_le_left _ _
    have h₁ :
        (k - 1) * min (x.width / k) (z.width / k)
          ≤
        (k - 1) * (x.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ :
        (k - 1) * (x.width / k)
          ≤
        k * (x.width / k) := by
      exact Nat.mul_le_mul_right _
        (Nat.sub_le k 1)
    have h₃ :
        k * (x.width / k) ≤ x.width := by
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self x.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    exact phaseLimbWidth_top_nonempty
      x.width z.width k hk

lemma phaseLimbWidth_valid_right
    (x z : ExtReg)
    {k : ℕ}
    (hk : 0 < k) :
    ValidPhaseSplit z k (phaseLimbWidth x z k) := by
  refine ⟨hk, ?_, ?_⟩
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    have hW :
        min (x.width / k) (z.width / k)
          ≤ z.width / k :=
      Nat.min_le_right _ _
    have h₁ :
        (k - 1) * min (x.width / k) (z.width / k)
          ≤
        (k - 1) * (z.width / k) :=
      Nat.mul_le_mul_left _ hW
    have h₂ :
        (k - 1) * (z.width / k)
          ≤
        k * (z.width / k) := by
      exact Nat.mul_le_mul_right _
        (Nat.sub_le k 1)
    have h₃ :
        k * (z.width / k) ≤ z.width := by
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self z.width k
    exact h₁.trans (h₂.trans h₃)
  · unfold phaseLimbWidth phaseLimbWidthOfWidth
    simpa [Nat.min_comm] using
      phaseLimbWidth_top_nonempty
        z.width x.width k hk

/-! ---------------------------------------------------------
    Chunk width, reconstruction, and disjointness proofs
--------------------------------------------------------- -/

/-- Length of a concrete `drop`/`take` slice that lies inside a register. -/
lemma regSize_drop_take_of_add_le
    (r : Reg)
    (start len : ℕ)
    (h : start + len ≤ regSize r) :
    regSize ((r.drop start).take len) = len := by
  change ((r.qubits.drop start).take len).length = len
  rw [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  unfold regSize Reg.width at h
  omega

lemma phaseChunkActive_width
    (e : ExtReg)
    (k W : ℕ)
    (i : Fin k)
    (hvalid : ValidPhaseSplit e k W) :
    regSize (phaseChunkActive e k W i) =
      phaseSplitLogicalWidth e.width W k i := by
  obtain ⟨_hk, hbound, _htopNonempty⟩ := hvalid
  unfold phaseChunkActive
  by_cases htop : isTopChunk i
  · have hik : k - 1 = i.1 := by
      unfold isTopChunk at htop
      omega
    have hstart : i.1 * W ≤ e.width := by
      simpa [hik] using hbound
    apply regSize_drop_take_of_add_le
    simp only [phaseChunkStart, phaseSplitLogicalWidth, htop, if_pos]
    exact le_of_eq <| by
      calc
        i.1 * W + (e.width - i.1 * W) = e.width :=
          Nat.add_sub_of_le hstart
        _ = regSize e.active := rfl
  · have hi : i.1 + 1 ≤ k - 1 := by
      unfold isTopChunk at htop
      have hle : i.1 + 1 ≤ k :=
        Nat.succ_le_of_lt i.2
      omega
    have hmul :
        (i.1 + 1) * W ≤ (k - 1) * W :=
      Nat.mul_le_mul_right W hi
    have hfit :
        i.1 * W + W ≤ e.width := by
      calc
        i.1 * W + W = (i.1 + 1) * W := by
          rw [Nat.add_mul]
          simp
        _ ≤ (k - 1) * W := hmul
        _ ≤ e.width := hbound
    apply regSize_drop_take_of_add_le
    simpa [phaseChunkStart, phaseSplitLogicalWidth, htop] using hfit

lemma PhaseSplitLayout.child_width
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (i : Fin k) :
    (layout.child i).width =
      phaseSplitLogicalWidth parent.width W k i := by
  unfold PhaseSplitLayout.child ExtReg.width
  exact phaseChunkActive_width
    parent k W i layout.valid

lemma splitChunk_toNat_lt
    {Basis : Type u}
    [RegEncoding Basis]
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (i : Fin k)
    (b : Basis) :
    ExtReg.toNat (layout.child i) b
      <
    2 ^
      (if isTopChunk i then
        parent.width - i.1 * W
      else
        W) := by
  have h :=
    ExtReg.toNat_lt (layout.child i) b
  rw [layout.child_width i] at h
  simpa [phaseSplitLogicalWidth] using h

/-- A sequence of `n` base-`2^W` digits represents a number below
    `2^(n*W)`. -/
lemma fin_sum_digits_lt_pow
    (W : ℕ) :
    ∀ {n : ℕ}
      (digits : Fin n → ℕ),
      (∀ i, digits i < 2 ^ W) →
      (∑ i : Fin n,
          digits i * 2 ^ (i.1 * W))
        <
      2 ^ (n * W)
  | 0, digits, hdigits => by
      simp
  | n + 1, digits, hdigits => by
      have hlow :
          (∑ i : Fin n,
              digits i.castSucc *
                2 ^ (i.1 * W))
            <
          2 ^ (n * W) := by
        apply fin_sum_digits_lt_pow W
        intro i
        exact hdigits i.castSucc
      have hlast :
          digits (Fin.last n) < 2 ^ W :=
        hdigits (Fin.last n)
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      calc
        (∑ i : Fin n,
            digits i.castSucc *
              2 ^ (i.1 * W))
            +
          digits (Fin.last n) *
            2 ^ (n * W)
            <
          2 ^ (n * W) +
            digits (Fin.last n) *
              2 ^ (n * W) :=
          Nat.add_lt_add_right hlow _
        _ =
          (digits (Fin.last n) + 1) *
            2 ^ (n * W) := by
          ring
        _ ≤
          2 ^ W * 2 ^ (n * W) := by
          exact Nat.mul_le_mul_right
            (2 ^ (n * W))
            (Nat.succ_le_of_lt hlast)
        _ =
          2 ^ ((n + 1) * W) := by
          rw [Nat.add_mul, pow_add]
          simp [Nat.mul_comm]

/-- Concatenating an unsigned low block with a signed high block and then
    decoding gives the low block plus the shifted signed high block. -/
lemma tcDecodeWidth_concat
    {lowWidth highWidth low high : ℕ}
    (hHighWidth : 0 < highWidth)
    (hLow : low < 2 ^ lowWidth)
    (hHigh : high < 2 ^ highWidth) :
    tcDecodeWidth
        (lowWidth + highWidth)
        (low + high * 2 ^ lowWidth)
      =
    (low : ℤ) +
      tcDecodeWidth highWidth high *
        (2 : ℤ) ^ lowWidth := by
  obtain ⟨h, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hHighWidth)
  by_cases hsign : high < 2 ^ h
  · have hcombined :
        low + high * 2 ^ lowWidth
          <
        2 ^ (lowWidth + h) := by
      calc
        low + high * 2 ^ lowWidth
            <
        2 ^ lowWidth +
          high * 2 ^ lowWidth :=
          Nat.add_lt_add_right hLow _
        _ =
        (high + 1) * 2 ^ lowWidth := by
          ring
        _ ≤
        2 ^ h * 2 ^ lowWidth := by
          exact Nat.mul_le_mul_right
            (2 ^ lowWidth)
            (Nat.succ_le_of_lt hsign)
        _ =
        2 ^ (lowWidth + h) := by
          rw [pow_add]
          ring
    rw [show lowWidth + (h + 1) = (lowWidth + h) + 1 by omega]
    simp only [tcDecodeWidth]
    simp [hcombined, hsign]
  · have hhighLower : 2 ^ h ≤ high :=
      Nat.le_of_not_gt hsign
    have hcombined :
        ¬ low + high * 2 ^ lowWidth
            <
          2 ^ (lowWidth + h) := by
      apply Nat.not_lt_of_ge
      calc
        2 ^ (lowWidth + h)
            =
        2 ^ h * 2 ^ lowWidth := by
          rw [pow_add]
          ring
        _ ≤
        high * 2 ^ lowWidth :=
          Nat.mul_le_mul_right
            (2 ^ lowWidth)
            hhighLower
        _ ≤
        low + high * 2 ^ lowWidth :=
          Nat.le_add_left _ _
    rw [show lowWidth + (h + 1) = (lowWidth + h) + 1 by omega]
    simp only [tcDecodeWidth]
    simp [hsign, pow_add]
    rw[pow_add] at hcombined
    simp[hcombined]
    ring

/-- Binary positional decomposition for the concrete `take`/`drop` split. -/
lemma toNat_take_drop
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (m : ℕ)
    (hm : m ≤ regSize r)
    (b : Basis) :
    RegEncoding.toNat r b
      =
    RegEncoding.toNat (r.take m) b
      +
    2 ^ m * RegEncoding.toNat (r.drop m) b := by
  let sp : SplitPoint r := ⟨m, hm⟩
  have h :=
    RegEncoding.toNat_split
      (r := r)
      (m := sp)
      (b := b)
  unfold SplitPoint at *
  have hmin :
      min m r.qubits.length = m := by
    rw [Nat.min_eq_left]
    simpa [regSize, Reg.width] using hm
  simpa [sp, splitLeft, splitRight, ASize, regSize, Reg.width, Reg.take, hmin] using h

/-- Taking a block after first restricting to a prefix gives the same block,
    provided the complete block lies inside that prefix. -/
lemma take_drop_take_eq
    (r : Reg)
    (pre start width : ℕ)
    (hfit : start + width ≤ pre) :
    ((r.take pre).drop start).take width
      =
    (r.drop start).take width := by
  cases r with
  | mk qubits nodup =>
      have hw :
          width ≤ pre - start :=
        by omega
      simp [Reg.take, Reg.drop, List.drop_take, List.take_take, Nat.min_eq_left hw]

/-- Reconstruction of an `n·W`-bit register from `n` consecutive
    width-`W` blocks. -/
lemma toNat_uniform_chunks
    {Basis : Type u}
    [RegEncoding Basis]
    (W : ℕ) :
    ∀ (n : ℕ)
      (r : Reg)
      (b : Basis),
      regSize r = n * W →
      RegEncoding.toNat r b
        =
      ∑ i : Fin n,
        RegEncoding.toNat
          ((r.drop (i.1 * W)).take W)
          b *
        2 ^ (i.1 * W)
  | 0, r, b, hwidth => by
      have hlt :
          RegEncoding.toNat r b < ASize r :=
        RegEncoding.toNat_lt_ASize r b
      have hr0 : regSize r = 0 := by
        simpa using hwidth
      have hnat : RegEncoding.toNat r b = 0 := by
        unfold ASize at hlt
        rw [hr0] at hlt
        simp at hlt
        omega
      simp [hnat]
  | n + 1, r, b, hwidth => by
      have hWle : W ≤ regSize r := by
        rw [hwidth, Nat.add_mul]
        simp
      have hsplit :
          RegEncoding.toNat r b
            =
          RegEncoding.toNat (r.take W) b
            +
          2 ^ W *
            RegEncoding.toNat (r.drop W) b :=
        toNat_take_drop r W hWle b
      have htailWidth :
          regSize (r.drop W) = n * W := by
        have hwidth' :
            r.qubits.length = (n + 1) * W := by
          simpa [regSize, Reg.width] using hwidth
        have hdrop :
            r.qubits.length - W = n * W := by
          rw [hwidth']
          rw [Nat.succ_mul]
          simp [Nat.add_comm]
        simpa [regSize, Reg.width, Reg.drop] using hdrop
      have htail :
          RegEncoding.toNat (r.drop W) b
            =
          ∑ i : Fin n,
            RegEncoding.toNat
              (((r.drop W).drop (i.1 * W)).take W)
              b *
            2 ^ (i.1 * W) :=
        toNat_uniform_chunks W n (r.drop W) b htailWidth
      have hzero :
          (r.drop (0 * W)).take W = r.take W := by
        cases r
        simp [Reg.drop, Reg.take]
      have hsucc :
          ∀ i : Fin n,
            (r.drop ((i.succ : Fin (n + 1)).1 * W)).take W
              =
            ((r.drop W).drop (i.1 * W)).take W := by
        intro i
        cases r
        simp [Reg.drop, Reg.take, List.drop_drop, Nat.add_mul, Nat.add_comm]
      rw [hsplit, htail]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, zero_mul, pow_zero, Nat.mul_one]
      rw [show (r.drop 0).take W = r.take W by simpa using hzero]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsucc i]
      have hexp :
          ((i.succ : Fin (n + 1)).1 * W)
            =
          W + i.1 * W := by
        simp [Nat.add_mul, Nat.add_comm]
      rw [hexp, pow_add]
      ring

/-- A non-top phase chunk is the corresponding width-`W` block of the
    `(k-1)·W`-bit lower prefix. -/
lemma phaseChunkActive_castSucc
    (parent : ExtReg)
    (n W : ℕ)
    (i : Fin n)
    (_hcut : n * W ≤ parent.width) :
    phaseChunkActive
        parent (n + 1) W
        (i.castSucc : Fin (n + 1))
      =
    (((parent.active.take (n * W)).drop
        (i.1 * W)).take W) := by
  have hnotTop :
      ¬ isTopChunk
        (i.castSucc : Fin (n + 1)) := by
    unfold isTopChunk
    simp only [Fin.val_castSucc]
    omega
  have hi : i.1 + 1 ≤ n :=
    Nat.succ_le_of_lt i.2
  have hfit :
      i.1 * W + W ≤ n * W := by
    calc
      i.1 * W + W = (i.1 + 1) * W := by
        rw [Nat.add_mul]
        simp
      _ ≤ n * W :=
        Nat.mul_le_mul_right W hi
  unfold phaseChunkActive phaseChunkStart
  rw [phaseSplitLogicalWidth]
  simp only [hnotTop, if_false]
  exact
    (take_drop_take_eq
      parent.active
      (n * W)
      (i.1 * W)
      W
      hfit).symm

/-- The final phase chunk is exactly the suffix following the lower
    `(k-1)` width-`W` blocks. -/
lemma phaseChunkActive_last
    (parent : ExtReg)
    (n W : ℕ)
    (hcut : n * W ≤ parent.width) :
    phaseChunkActive
        parent (n + 1) W
        (Fin.last n)
      =
    parent.active.drop (n * W) := by
  have htop :
      isTopChunk
        (Fin.last n : Fin (n + 1)) := by
    unfold isTopChunk
    simp
  cases parent with
  | mk active reserve hdisj =>
      cases active with
      | mk qubits nodup =>
          simp [phaseChunkActive, phaseChunkStart, phaseSplitLogicalWidth, htop, ExtReg.width, regSize, Reg.width, Reg.take, Reg.drop]

/-- Reconstruct the unsigned parent value from all child chunk values. -/
theorem phaseChunks_reconstruct_nat
    {Basis : Type u}
    [RegEncoding Basis]
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (b : Basis) :
    ExtReg.toNat parent b
      =
    ∑ i : Fin k,
      ExtReg.toNat (layout.child i) b *
        2 ^ (i.1 * W) := by
  obtain ⟨hk, hbound, htopValid⟩ :=
    layout.valid
  cases k with
  | zero =>
      omega
  | succ n =>
      simp only [Nat.succ_sub_one] at hbound
      let cut : ℕ := n * W
      let lower : Reg := parent.active.take cut
      let upper : Reg := parent.active.drop cut
      have hcut :
          cut ≤ parent.width := by
        simpa [cut] using hbound
      have hlowerWidth :
          regSize lower = n * W := by
        dsimp [lower, cut]
        simp [regSize, Reg.width, Reg.take]
        unfold cut ExtReg.width regSize Reg.width at *
        apply hcut
      have hsplit :
          ExtReg.toNat parent b
            =
          RegEncoding.toNat lower b
            +
          2 ^ cut *
            RegEncoding.toNat upper b := by
        unfold ExtReg.toNat
        simpa [lower, upper, cut] using
          toNat_take_drop
            parent.active
            cut
            hcut
            b
      have hlower :
          RegEncoding.toNat lower b
            =
          ∑ i : Fin n,
            RegEncoding.toNat
              ((lower.drop (i.1 * W)).take W)
              b *
            2 ^ (i.1 * W) :=
        toNat_uniform_chunks
          W n lower b hlowerWidth
      have hlowerChild :
          ∀ i : Fin n,
            ExtReg.toNat
                (layout.child
                  (i.castSucc : Fin (n + 1)))
                b
              =
            RegEncoding.toNat
              ((lower.drop (i.1 * W)).take W)
              b := by
        intro i
        unfold ExtReg.toNat
        change
          RegEncoding.toNat
              (phaseChunkActive
                parent (n + 1) W
                (i.castSucc : Fin (n + 1))) b
            =
          RegEncoding.toNat ((lower.drop (i.1 * W)).take W) b
        rw [ phaseChunkActive_castSucc parent n W i hcut ]
      have hupperChild :
          ExtReg.toNat
              (layout.child
                (Fin.last n : Fin (n + 1)))
              b
            =
          RegEncoding.toNat upper b := by
        unfold ExtReg.toNat
        change
          RegEncoding.toNat
              (phaseChunkActive
                parent (n + 1) W
                (Fin.last n))
              b
            =
          RegEncoding.toNat upper b
        rw [phaseChunkActive_last parent n W hcut]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hsplit, hlower]
      have hlowerSum :
          (∑ i : Fin n,
              RegEncoding.toNat
                ((lower.drop (i.1 * W)).take W)
                b *
              2 ^ (i.1 * W))
            =
          ∑ i : Fin n,
              ExtReg.toNat
                (layout.child
                  (i.castSucc : Fin (n + 1)))
                b *
              2 ^ (i.1 * W) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hlowerChild i]
      rw [hlowerSum, hupperChild]
      dsimp [cut]
      ring

/-- Decode a chunk sum where the final chunk is interpreted as signed two's-complement. -/
theorem tcDecode_chunks_signed_top
    {k W total raw : ℕ}
    (hk : 0 < k)
    (hbound : (k - 1) * W ≤ total)
    (htop : total = 0 ∨ (k - 1) * W < total)
    (hraw : raw < 2 ^ total)
    (chunks : Fin k → ℕ)
    (hchunks :
      ∀ i : Fin k,
        chunks i <
          2 ^
            (if isTopChunk i then
              total - i.1 * W
            else
              W))
    (hchunk :
      raw =
        ∑ i : Fin k,
          chunks i * 2 ^ (i.1 * W)) :
    tcDecodeWidth total raw
      =
    ∑ i : Fin k,
      (if isTopChunk i then
          tcDecodeWidth
            (total - i.1 * W)
            (chunks i)
        else
          (chunks i : ℤ)) *
        (2 : ℤ) ^ (i.1 * W) := by
  cases k with
  | zero =>
      omega
  | succ n =>
      simp only [Nat.succ_sub_one] at hbound htop
      by_cases htotal : total = 0
      · subst total
        have hrawZero : raw = 0 := by
          simpa using hraw
        have hchunksZero :
            ∀ i : Fin (n + 1), chunks i = 0 := by
          intro i
          have htermLe :
              chunks i * 2 ^ (i.1 * W)
                ≤
              ∑ j : Fin (n + 1),
                chunks j * 2 ^ (j.1 * W) := by
            aesop
          rw [← hchunk, hrawZero] at htermLe
          have hpowPos :
              0 < 2 ^ (i.1 * W) := by
            positivity
          aesop
        subst raw
        simp [tcDecodeWidth, hchunksZero]
      · have htotalPos : 0 < total :=
          Nat.pos_of_ne_zero htotal
        have htopStrict : n * W < total :=
          htop.resolve_left htotal
        let lowWidth : ℕ := n * W
        let highWidth : ℕ := total - lowWidth
        let low : ℕ :=
          ∑ i : Fin n,
            chunks i.castSucc *
              2 ^ (i.1 * W)
        let high : ℕ :=
          chunks (Fin.last n)
        have hwidthEq :
            lowWidth + highWidth = total := by
          dsimp [lowWidth, highWidth]
          exact Nat.add_sub_of_le hbound
        have hHighWidthPos :
            0 < highWidth := by
          dsimp [highWidth, lowWidth]
          exact Nat.sub_pos_of_lt htopStrict
        have hnotTop :
            ∀ i : Fin n,
              ¬ isTopChunk
                (i.castSucc : Fin (n + 1)) := by
          intro i
          unfold isTopChunk
          simp only [Fin.val_castSucc]
          omega
        have htopLast :
            isTopChunk
              (Fin.last n : Fin (n + 1)) := by
          unfold isTopChunk
          simp
        have hlowerDigit :
            ∀ i : Fin n,
              chunks i.castSucc < 2 ^ W := by
          intro i
          have hi := hchunks i.castSucc
          simpa [hnotTop i] using hi
        have hLow :
            low < 2 ^ lowWidth := by
          dsimp [low, lowWidth]
          exact fin_sum_digits_lt_pow
            W
            (fun i : Fin n =>
              chunks i.castSucc)
            hlowerDigit
        have hHigh :
            high < 2 ^ highWidth := by
          have hi := hchunks
            (Fin.last n : Fin (n + 1))
          simpa [high, highWidth, lowWidth, htopLast] using hi
        have hdecomp :
            raw =
              low +
                high * 2 ^ lowWidth := by
          rw [hchunk, Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          rfl
        have hdecode :
            tcDecodeWidth total raw
              =
            (low : ℤ) +
              tcDecodeWidth highWidth high *
                (2 : ℤ) ^ lowWidth := by
          calc
            tcDecodeWidth total raw
                =
            tcDecodeWidth
              (lowWidth + highWidth)
              (low + high * 2 ^ lowWidth) := by
                rw [hwidthEq, hdecomp]
            _ =
            (low : ℤ) +
              tcDecodeWidth highWidth high *
                (2 : ℤ) ^ lowWidth :=
              tcDecodeWidth_concat
                hHighWidthPos hLow hHigh
        have hLowCast :
            (low : ℤ)
              =
            ∑ i : Fin n,
              (chunks i.castSucc : ℤ) *
                (2 : ℤ) ^ (i.1 * W) := by
          dsimp [low]
          push_cast
          rfl
        rw [hdecode, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        simp_rw [if_neg (hnotTop _)]
        rw [if_pos htopLast]
        rw [← hLowCast]

/-- Two consecutive-block slices of a `Nodup` list are disjoint whenever the
    first block ends no later than the second one starts. -/
theorem slice_disjoint {L : List ℕ} (hL : L.Nodup) {a b c d : ℕ} (h : b + a ≤ d) :
    (List.take a (List.drop b L)).Disjoint (List.take c (List.drop d L)) := by
  have e1 : List.take a (List.drop b L) = List.drop b (List.take (b + a) L) := by
    rw [List.drop_take]; congr 1; omega
  have sub1 : (List.take a (List.drop b L)).Sublist (List.take (b + a) L) := by
    rw [e1]; exact List.drop_sublist _ _
  have sub2 : (List.take c (List.drop d L)).Sublist (List.drop d L) :=
    List.take_sublist _ _
  have hdisj : (List.take (b + a) L).Disjoint (List.drop d L) :=
    List.disjoint_take_drop hL h
  exact List.disjoint_of_subset_left sub1.subset
    (List.disjoint_of_subset_right sub2.subset hdisj)

/-- Flattening `n` consecutive width-`W` blocks recovers the length-`n·W` prefix. -/
theorem flatten_blocks (L : List ℕ) (W : ℕ) : ∀ n : ℕ,
    (List.ofFn (n := n) fun i : Fin n => List.take W (List.drop (i.1 * W) L)).flatten
      = List.take (n * W) L := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.val_castSucc, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih]
    have hmul : (n + 1) * W = n * W + W := by ring
    have hlast : (Fin.last n).1 = n := rfl
    rw [hlast, hmul, List.take_add]

theorem phaseChunkActive_pairwise_disjoint
    (e : ExtReg)
    (k W : ℕ)
    (hvalid : ValidPhaseSplit e k W)
    {i j : Fin k}
    (hij : i ≠ j) :
    Disjoint
      (phaseChunkActive e k W i)
      (phaseChunkActive e k W j) := by
  obtain ⟨hk, hcap⟩ := hvalid
  have hL : e.active.qubits.Nodup := e.active.nodup
  have hijn : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hik := i.2; have hjk := j.2
  rcases Nat.lt_or_gt_of_ne hijn with hlt | hgt
  · have hnotop : ¬ isTopChunk i := by unfold isTopChunk; omega
    have hsi : phaseSplitLogicalWidth e.width W k i = W := by
      simp [phaseSplitLogicalWidth, hnotop]
    have hexp : ((i : ℕ) + 1) * W = (i : ℕ) * W + W := by ring
    have h1 : ((i : ℕ) + 1) * W ≤ (j : ℕ) * W := Nat.mul_le_mul_right W (by omega)
    have key : (i : ℕ) * W + W ≤ (j : ℕ) * W := by omega
    simp only [Disjoint, phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, hsi]
    exact slice_disjoint hL key
  · have hnotop : ¬ isTopChunk j := by unfold isTopChunk; omega
    have hsj : phaseSplitLogicalWidth e.width W k j = W := by
      simp [phaseSplitLogicalWidth, hnotop]
    have hexp : ((j : ℕ) + 1) * W = (j : ℕ) * W + W := by ring
    have h1 : ((j : ℕ) + 1) * W ≤ (i : ℕ) * W := Nat.mul_le_mul_right W (by omega)
    have key : (j : ℕ) * W + W ≤ (i : ℕ) * W := by omega
    simp only [Disjoint, phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, hsj]
    exact (slice_disjoint hL key).symm

theorem phaseChunkActive_partition
    (e : ExtReg)
    (k W : ℕ)
    (hvalid : ValidPhaseSplit e k W) :
    (List.ofFn fun i =>
      (phaseChunkActive e k W i).qubits).flatten
      =
    e.active.qubits := by
  obtain ⟨hk, hcap⟩ := hvalid
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hlow : ∀ i : Fin k', (phaseChunkActive e (k' + 1) W (i.castSucc)).qubits
      = List.take W (List.drop (i.1 * W) e.active.qubits) := by
    intro i
    have hnotop : ¬ isTopChunk (i.castSucc : Fin (k' + 1)) := by
      unfold isTopChunk; simp only [Fin.val_castSucc]; omega
    simp only [phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, Fin.val_castSucc, phaseSplitLogicalWidth, if_neg hnotop]
  have htop : (phaseChunkActive e (k' + 1) W (Fin.last k')).qubits
      = List.drop (k' * W) e.active.qubits := by
    have hT : isTopChunk (Fin.last k' : Fin (k' + 1)) := by
      unfold isTopChunk; simp [Fin.last]
    simp only [phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop, phaseSplitLogicalWidth, if_pos hT, Fin.val_last]
    apply List.take_of_length_le
    rw [List.length_drop]
    exact le_refl _
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  have hcong : (List.ofFn fun i : Fin k' => (phaseChunkActive e (k' + 1) W i.castSucc).qubits)
             = (List.ofFn fun i : Fin k' => List.take W (List.drop (i.1 * W) e.active.qubits)) := by
    congr 1; funext i; exact hlow i
  rw [hcong, flatten_blocks, htop, List.take_append_drop]

theorem splitChunkInt_reconstruct
    {Basis : Type u}
    [RegEncoding Basis]
    {parent : ExtReg}
    {k W : ℕ}
    (layout : PhaseSplitLayout parent k W)
    (b : Basis) :
    extToInt parent b
      =
    ∑ i : Fin k,
      splitChunkInt layout i b *
        ((2 : ℤ) ^ (i.1 * W)) := by
  obtain ⟨hk, hbound, htop⟩ := layout.valid
  have hraw :
      ExtReg.toNat parent b < 2 ^ parent.width :=
    ExtReg.toNat_lt parent b
  have hreconstruct :
      ExtReg.toNat parent b
        =
      ∑ i : Fin k,
        ExtReg.toNat (layout.child i) b *
          2 ^ (i.1 * W) :=
    phaseChunks_reconstruct_nat layout b
  unfold extToInt
  simpa [splitChunkInt] using
    tcDecode_chunks_signed_top
    (k := k)
    (W := W)
    (total := parent.width)
    (raw := ExtReg.toNat parent b)
    (chunks := fun i =>
      ExtReg.toNat (layout.child i) b)
    hk hbound htop hraw
    (fun i => splitChunk_toNat_lt layout i b)
    hreconstruct

/-! ---------------------------------------------------------
    Workspace preservation and reserve-budget construction
--------------------------------------------------------- -/

/-- Growing every slot to the target width preserves control disjointness. -/
theorem controlDisjoint_target
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ctrl : ℕ)
    (need : NeededWidths k)
    (hctrl : layout.ControlDisjoint ctrl) :
    let src := initSignedLayoutState layout
    let dst := targetSignedLayoutState src need
    (∀ i, ctrl ∉ (dst.xslot i).ownedQubits) ∧
    (∀ i, ctrl ∉ (dst.zslot i).ownedQubits) := by
  intro src dst
  obtain ⟨hx, hz⟩ := hctrl
  refine ⟨?_, ?_⟩
  · intro i
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, ExtReg.ownedQubits_grow] using hx i
  · intro i
    simpa [dst, targetSignedLayoutState, growExtRegTo, src, initSignedLayoutState, ExtReg.ownedQubits_grow] using hz i

/-- Growing an extendable register only moves qubits from reserve to active; ownership is unchanged. -/

@[simp]
theorem ExtReg.ownedQubits_grow
    (e : ExtReg)
    (n : ℕ) :
    (e.grow n).ownedQubits = e.ownedQubits := by
  simp [ExtReg.ownedQubits, ExtReg.grow, Reg.append, ExtReg.newBits, Reg.take, ExtReg.remainingReserve, Reg.drop, List.append_assoc, List.take_append_drop]

/-- Target widening preserves pairwise owned-disjointness of all slots. -/
theorem targetSignedLayoutState_owned_disjoint
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (need : NeededWidths k) :
    (targetSignedLayoutState
      (initSignedLayoutState layout)
      need).OwnedPairwiseDisjoint := by
  obtain ⟨hx, hz, hxz⟩ := initSignedLayoutState_owned_disjoint layout
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hx i j hij
  · intro i j hij
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hz i j hij
  · intro i j
    simpa [targetSignedLayoutState, growExtRegTo, ExtReg.OwnedDisjoint, ExtReg.ownedQubits_grow] using hxz i j

/-- Consecutive variable-width slices reconstruct the corresponding prefix. -/
private theorem flatten_consecutive_slices
    (L : List ℕ) :
    ∀ (k : ℕ) (size : Fin k → ℕ),
      (List.ofFn fun i =>
        List.take (size i)
          (List.drop
            (((List.ofFn size).take i.1).sum)
            L)).flatten
        =
      List.take ((List.ofFn size).sum) L := by
  intro k
  induction k with
  | zero =>
      intro size
      simp
  | succ k ih =>
      intro size
      let size' : Fin k → ℕ :=
        fun i => size i.castSucc
      have htake (i : Fin k) :
          (List.ofFn size).take i.1
            =
              (List.ofFn size').take i.1 := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size', List.take_append_of_le_length]
      have htakeLast :
          (List.ofFn size).take k
            =
          List.ofFn size' := by
        rw [List.ofFn_succ', List.concat_eq_append]
        simp [size']
      have hsum :
          (List.ofFn size).sum
            =
          (List.ofFn size').sum
            + size (Fin.last k) := by
        rw [List.ofFn_succ']
        simp [size']
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
      simp only [Fin.val_castSucc, List.flatten_cons, List.flatten_nil, List.append_nil]
      have hlastVal : (Fin.last k).1 = k := rfl
      rw [hlastVal]
      simp_rw [htake]
      change
        (List.ofFn fun i : Fin k =>
          List.take (size' i)
            (List.drop
              (((List.ofFn size').take i.1).sum)
              L)).flatten
          ++
        List.take (size (Fin.last k))
          (List.drop
            (((List.ofFn size).take k).sum)
            L)
          =
        List.take ((List.ofFn size).sum) L
      rw [ih size', htakeLast, hsum, List.take_add]

theorem ReserveBudget.flatten_childReserve
    {parent : ExtReg}
    {k : ℕ}
    (budget : ReserveBudget parent k) :
    (List.ofFn fun i =>
      (budget.childReserve i).qubits).flatten
      =
    parent.reserve.qubits := by
  simp only [ReserveBudget.childReserve, ReserveBudget.offset, Reg.take, Reg.drop]
  rw [flatten_consecutive_slices]
  rw [budget.total]
  simp [ExtReg.capacity, regSize, Reg.width]

private theorem phaseChunkActive_sublist
    (parent : ExtReg)
    (k W : ℕ)
    (i : Fin k) :
    (phaseChunkActive parent k W i).qubits.Sublist
      parent.active.qubits := by
  simp only [phaseChunkActive, phaseChunkStart, Reg.take, Reg.drop]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

private theorem ReserveBudget.childReserve_sublist
    {parent : ExtReg}
    {k : ℕ}
    (budget : ReserveBudget parent k)
    (i : Fin k) :
    (budget.childReserve i).qubits.Sublist
      parent.reserve.qubits := by
  simp only [ReserveBudget.childReserve, ReserveBudget.offset, Reg.take, Reg.drop]
  exact
    (List.take_sublist _ _).trans
      (List.drop_sublist _ _)

private theorem phaseChunkActive_childReserve_disjoint
    {parent : ExtReg}
    {k W : ℕ}
    (budget : ReserveBudget parent k)
    (i j : Fin k) :
    List.Disjoint
      (phaseChunkActive parent k W i).qubits
      (budget.childReserve j).qubits := by
  have hactive :=
    phaseChunkActive_sublist parent k W i
  have hreserve :=
    budget.childReserve_sublist j
  have hparent :
      parent.active.qubits.Disjoint
        parent.reserve.qubits := by
    simpa [Disjoint] using
      parent.active_reserve_disjoint
  exact
    List.disjoint_of_subset_left hactive.subset
      (List.disjoint_of_subset_right
        hreserve.subset
        hparent)

private theorem pairwise_disjoint_ofFn
    {α : Type*}
    {k : ℕ}
    {f : Fin k → List α}
    (hpair : (List.ofFn f).Pairwise List.Disjoint)
    {i j : Fin k}
    (hij : i ≠ j) :
    (f i).Disjoint (f j) := by
  have hval : i.1 ≠ j.1 := by
    intro h
    apply hij
    exact Fin.ext h
  rcases Nat.lt_or_gt_of_ne hval with hijlt | hjilt
  ·
    have h := (List.pairwise_iff_getElem.mp hpair)  i.1 j.1 (by simp) (by simp) hijlt
    simpa using h
  ·
    have h :=
      (List.pairwise_iff_getElem.mp hpair)
        j.1
        i.1
        (by simp)
        (by simp)
        hjilt
    simpa using h.symm

/-- Build an abstract split layout from concrete active slices and a reserve budget. -/
def PhaseSplitLayout.ofBudget
    (parent : ExtReg)
    (k W : ℕ)
    (hvalid : ValidPhaseSplit parent k W)
    (budget : ReserveBudget parent k) :
    PhaseSplitLayout parent k W :=
  {
    valid := hvalid
    reserve := budget.childReserve
    active_reserve_disjoint := by
      intro i
      simpa [Disjoint] using
        phaseChunkActive_childReserve_disjoint
          (W := W)
          budget i i
    reserve_partition := by
      exact budget.flatten_childReserve
    child_owned_pairwise := by
      intro i j hij
      have hAA :
          List.Disjoint
            (phaseChunkActive parent k W i).qubits
            (phaseChunkActive parent k W j).qubits := by
        simpa [Disjoint] using
          phaseChunkActive_pairwise_disjoint
            parent k W hvalid hij
      have hAR :
          List.Disjoint
            (phaseChunkActive parent k W i).qubits
            (budget.childReserve j).qubits :=
        phaseChunkActive_childReserve_disjoint
          (W := W)
          budget i j
      have hRA :
          List.Disjoint
            (budget.childReserve i).qubits
            (phaseChunkActive parent k W j).qubits :=
        (phaseChunkActive_childReserve_disjoint
          (W := W)
          budget j i).symm
      have hflatNodup :
          ((List.ofFn fun t : Fin k =>
            (budget.childReserve t).qubits).flatten).Nodup := by
        rw [budget.flatten_childReserve]
        exact parent.reserve.nodup
      have hreservePairwise :
          (List.ofFn fun t : Fin k =>
            (budget.childReserve t).qubits).Pairwise
              List.Disjoint :=
        (List.nodup_flatten.mp hflatNodup).2
      have hRR :
          List.Disjoint
            (budget.childReserve i).qubits
            (budget.childReserve j).qubits :=
        pairwise_disjoint_ofFn
          (f := fun t : Fin k =>
            (budget.childReserve t).qubits)
          hreservePairwise
          hij
      intro q hqLeft hqRight
      rcases List.mem_append.mp hqLeft with hqAi | hqRi
      · rcases List.mem_append.mp hqRight with hqAj | hqRj
        · exact hAA hqAi hqAj
        · exact hAR hqAi hqRj
      · rcases List.mem_append.mp hqRight with hqAj | hqRj
        · exact hRA hqRi hqAj
        · exact hRR hqRi hqRj
  }

/-! =========================================================
    Section 4: Start-state and initial layout facts
========================================================= -/

/-- Start-state row evaluation picks out the requested x-slot. -/
lemma evalRowX_start_state (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowX (qs := qs) st (State.start_state i) b = sourceChunkXInt (qs := qs) st i b := by unfold evalRowX State.start_state; simp

/-- Start-state row evaluation picks out the requested z-slot. -/
lemma evalRowZ_start_state (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowZ (qs := qs) st (State.start_state i) b = sourceChunkZInt (qs := qs) st i b := by unfold evalRowZ State.start_state; simp

/-- Final `x` slots are exactly the initial slots grown to the common target width. -/
lemma stFinal_xslot_eq_grow
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (need : NeededWidths k)
    (i : Fin k) :
    let stInit := initSignedLayoutState layout
    let Wwork := commonNeededWidth need
    (targetSignedLayoutState stInit need).xslot i
      =
    (stInit.xslot i).grow
      (Wwork - (stInit.xslot i).width) := by
  simp [targetSignedLayoutState, growExtRegTo]

/-- Final `z` slots are exactly the initial slots grown to the common target width. -/
lemma stFinal_zslot_eq_grow
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (need : NeededWidths k)
    (i : Fin k) :
    let stInit := initSignedLayoutState layout
    let Wwork := commonNeededWidth need
    (targetSignedLayoutState stInit need).zslot i
      =
    (stInit.zslot i).grow
      (Wwork - (stInit.zslot i).width) := by
  simp [targetSignedLayoutState, growExtRegTo]

/-- Initial `x` slot width agrees with the symbolic initial width state. -/
lemma stInit_xslot_width
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    ((initSignedLayoutState layout).xslot i).width
      =
    (initWidthState x z k).xw i := by
  change
    (layout.xSplit.child i).width
      =
    phaseSplitLogicalWidth
      x.width
      (phaseLimbWidth x z k)
      k i
  exact layout.xSplit.child_width i

/-- Initial `z` slot width agrees with the symbolic initial width state. -/
lemma stInit_zslot_width
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (i : Fin k) :
    ((initSignedLayoutState layout).zslot i).width
      =
    (initWidthState x z k).zw i := by
  change
    (layout.zSplit.child i).width
      =
    phaseSplitLogicalWidth
      z.width
      (phaseLimbWidth x z k)
      k i
  exact layout.zSplit.child_width i

/-! =========================================================
    Section 5: Source-row arithmetic
    These facts mirror the algebra of `Register` operations at the integer row
    evaluation level for both `x` and `z`.
========================================================= -/

/-- Left shift scales `x` row evaluation by `2^m`. -/
lemma evalRowX_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r b := by
  unfold evalRowX Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Left shift scales `z` row evaluation by `2^m`. -/
lemma evalRowZ_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (m : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (r.shiftL m) b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r b := by
  unfold evalRowZ Register.shiftL
  calc
    (∑ j : Fin k, (r j * (2 : ℤ)^m) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Negation negates `x` row evaluation. -/
lemma evalRowX_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.negate r) b
    =
  - evalRowX (qs := qs) src r b := by
  unfold evalRowX Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

/-- Negation negates `z` row evaluation. -/
lemma evalRowZ_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r : Register k)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.negate r) b
    =
  - evalRowZ (qs := qs) src r b := by
  unfold evalRowZ Register.negate
  calc
    (∑ j : Fin k, (-r j) * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, -(r j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = - ∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.sum_neg_distrib]

/-- Exact right shift gives an `x` row quotient relation. -/
lemma evalRowX_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowX (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowX (qs := qs) src r' b := by
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowX
  calc
    (∑ j : Fin k, r j * sourceChunkXInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkXInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkXInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkXInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Exact right shift gives a `z` row quotient relation. -/
lemma evalRowZ_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (r r' : Register k)
  (m : ℕ)
  (b : qs.Basis)
  (hshift : Register.shiftR? r m = some r') :
  evalRowZ (qs := qs) src r b
    =
  ((2 : ℤ)^m) * evalRowZ (qs := qs) src r' b := by
  have hdiv := Register.shiftR?_some_divisible hshift
  have hval := Register.shiftR?_some_value hshift
  unfold evalRowZ
  calc
    (∑ j : Fin k, r j * sourceChunkZInt (qs := qs) src j b)
      =
    ∑ j : Fin k, (((2 : ℤ)^m) * r' j) * sourceChunkZInt (qs := qs) src j b := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdvd : ((2 : ℤ)^m) ∣ r j := Int.dvd_of_emod_eq_zero (hdiv j)
        have hrj : r j = ((2 : ℤ)^m) * r' j := by
          calc
            r j = ((2 : ℤ)^m) * (r j / ((2 : ℤ)^m)) := by
              symm
              exact Int.mul_ediv_cancel' hdvd
            _ = ((2 : ℤ)^m) * r' j := by
              rw [hval j]
        rw [hrj]
    _ =
    ∑ j : Fin k, ((2 : ℤ)^m) * (r' j * sourceChunkZInt (qs := qs) src j b) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = ((2 : ℤ)^m) * ∑ j : Fin k, r' j * sourceChunkZInt (qs := qs) src j b := by
        rw [Finset.mul_sum]

/-- Add-scaled operation expands linearly on `x` rows. -/
lemma evalRowX_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowX (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowX (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowX (qs := qs) src srcReg b := by
  unfold evalRowX Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkXInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkXInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkXInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkXInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkXInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

/-- Add-scaled operation expands linearly on `z` rows. -/
lemma evalRowZ_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ}
  (src : LayoutState k)
  (dstReg srcReg : Register k)
  (negSrc : Bool)
  (sh : ℕ)
  (b : qs.Basis) :
  evalRowZ (qs := qs) src (Register.addScaled dstReg srcReg negSrc sh) b
    =
  evalRowZ (qs := qs) src dstReg b
    + (if negSrc then (-1 : ℤ) else 1)
        * ((2 : ℤ)^sh)
        * evalRowZ (qs := qs) src srcReg b := by
  unfold evalRowZ Register.addScaled
  calc
    (∑ j : Fin k,
        (dstReg j + (if negSrc then (-1 : ℤ) else 1) * srcReg j * (2 : ℤ) ^ sh)
          * sourceChunkZInt (qs := qs) src j b)
        =
    (∑ j : Fin k,
      (dstReg j * sourceChunkZInt (qs := qs) src j b
        +
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ∑ j : Fin k,
      ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
        * (srcReg j * sourceChunkZInt (qs := qs) src j b) := by
          rw [Finset.sum_add_distrib]
    _ =
    (∑ j : Fin k, dstReg j * sourceChunkZInt (qs := qs) src j b)
      +
    ((if negSrc then (-1 : ℤ) else 1) * ((2 : ℤ) ^ sh))
      * ∑ j : Fin k, srcReg j * sourceChunkZInt (qs := qs) src j b := by
          rw [Finset.mul_sum]

/-- The common target width dominates every scanned `x` need. -/
lemma commonNeededWidth_ge_xneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.xneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.xneed i ≤ _ := le_trans (le_max_left _ _) h
  omega

/-- The common target width dominates every scanned `z` need. -/
lemma commonNeededWidth_ge_zneed {k : ℕ} (need : NeededWidths k) (i : Fin k) :
  need.zneed i + 1 ≤ commonNeededWidth need := by
  unfold commonNeededWidth
  have h :
      max (need.xneed i) (need.zneed i)
        ≤ Finset.univ.sup (fun j : Fin k => max (need.xneed j) (need.zneed j)) :=
    Finset.le_sup (f := fun j : Fin k => max (need.xneed j) (need.zneed j))
      (Finset.mem_univ i)
  have h' : need.zneed i ≤ _ := le_trans (le_max_right _ _) h
  omega

/-! =========================================================
    Section 6: Scan consequences for target layouts
========================================================= -/

/-- The initial `x` width is included in the full width scan. -/
lemma scanNeededWidths_x_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).xw i ≤ (scanNeededWidths x z ops).xneed i := by
  simp [scanNeededWidths]
  exact
    scanNeededWidthsAux_x_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k))

/-- The initial z width is included in the full width scan. -/
lemma scanNeededWidths_z_ge_init
    {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) (i : Fin k) :
    (initWidthState x z k).zw i ≤ (scanNeededWidths x z ops).zneed i := by
  simp [scanNeededWidths]
  exact
    scanNeededWidthsAux_z_ge
      (i := i)
      ops
      (initWidthState x z k)
      (widthsOfState (initWidthState x z k))

/-- A grown target `x` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_xslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)).xslot i).width
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit :
      (stInit.xslot i).width =
        (initWidthState x z k).xw i := by
    simpa [stInit] using stInit_xslot_width layout i
  have hscan :
      (initWidthState x z k).xw i ≤ need.xneed i := by
    simpa [need] using
      scanNeededWidths_x_ge_init x z ops i
  have hneed :
      need.xneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_xneed need i
  have hle : (stInit.xslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow :
      (stInit.xslot i).CanGrow
        (Wwork - (stInit.xslot i).width) := by
    exact hcap.1 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo
      (stInit.xslot i) Wwork hle hgrow

/-- A grown target `z` slot has exactly the common scanned width. -/
lemma targetSignedLayoutState_zslot_width_scan
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    ((targetSignedLayoutState
      (initSignedLayoutState layout)
      (scanNeededWidths x z ops)).zslot i).width
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  let stInit := initSignedLayoutState layout
  let need := scanNeededWidths x z ops
  let Wwork := commonNeededWidth need
  have hinit :
      (stInit.zslot i).width =
        (initWidthState x z k).zw i := by
    simpa [stInit] using stInit_zslot_width layout i
  have hscan :
      (initWidthState x z k).zw i ≤ need.zneed i := by
    simpa [need] using
      scanNeededWidths_z_ge_init x z ops i
  have hneed :
      need.zneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_zneed need i
  have hle : (stInit.zslot i).width ≤ Wwork := by
    rw [hinit]
    omega
  have hgrow :
      (stInit.zslot i).CanGrow
        (Wwork - (stInit.zslot i).width) := by
    exact hcap.2 i
  simpa [stInit, need, Wwork, targetSignedLayoutState] using
    width_growExtRegTo
      (stInit.zslot i) Wwork hle hgrow

/-- The scanned target `x` slot strictly grows beyond its initial width. -/
lemma extraDelta_xslot_pos
    {x z : ExtReg}
    {k : ℕ}
    (layout : Gate.PhaseProductLayout x z k)
    (ops : Prog k)
    (i : Fin k)
    (hcap :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops)) :
    let stInit := initSignedLayoutState layout
    let stFinal :=
      targetSignedLayoutState stInit
        (scanNeededWidths x z ops)
    0 < extraDelta
      (stInit.xslot i)
      (stFinal.xslot i) := by
  dsimp
  unfold extraDelta
  rw [targetSignedLayoutState_xslot_width_scan layout ops i hcap, stInit_xslot_width layout i]
  have hscan :=
    scanNeededWidths_x_ge_init x z ops i
  have hneed :=
    commonNeededWidth_ge_xneed
      (scanNeededWidths x z ops) i
  omega

/-- Evaluation of compiled annotated programs respects append as sequential composition. -/
lemma eval_compileAnnotatedOpsToSignedGateAux_append
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
  {k : ℕ} (hk : 1 < k)
  (phi : ℝ)
  (coeff : Fin (q k) → ℚ)
  (st : LayoutState k)
  (xs ys : List (AnnotatedOp k))
  (ψ : qs.State) :
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff st (xs ++ ys))
      ψ
    =
  qs.eval
      (compileAnnotatedOpsToSignedGateAux k hk phi coeff st ys)
      (qs.eval
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff st xs)
        ψ) := by
  induction xs generalizing ψ with
  | nil =>
      simp [compileAnnotatedOpsToSignedGateAux, qs.eval_id]
  | cons a xs ih =>
      cases a with
      | mk op term? =>
          cases op <;>
            simp [compileAnnotatedOpsToSignedGateAux, qs.eval_seq, ih]
          aesop

/-! =========================================================
    Section 7: Layout locality and basis extensionality
    The compiler often proves that a gate changes only layout slots and leaves
    everything outside unchanged. These predicates and extensionality lemmas turn
    those slot/outside facts back into equality of basis states.
========================================================= -/

/-- Short name for the layout-wide owned-disjointness invariant. -/
abbrev LayoutSlotsDisjoint
    {k : ℕ}
    (st : LayoutState k) : Prop :=
  st.OwnedPairwiseDisjoint

/-- Register `e` is actively disjoint from every slot in a layout. -/
def OutsideLayout
    {k : ℕ}
    (dst : LayoutState k)
    (e : ExtReg) : Prop :=
  (∀ i : Fin k, ExtReg.ActiveDisjoint e (dst.xslot i)) ∧
  (∀ i : Fin k, ExtReg.ActiveDisjoint e (dst.zslot i))

/-- Two basis states agree on every register outside a layout. -/
def SameOutsideLayout
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (dst : LayoutState k)
    (b₁ b₂ : qs.Basis) : Prop :=
  ∀ e : ExtReg,
    OutsideLayout dst e →
    extToInt e b₁ = extToInt e b₂

lemma SameOutsideLayout.refl (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (dst : LayoutState k) (b : qs.Basis) :
  SameOutsideLayout qs dst b b := by intro e he; rfl

lemma SameOutsideLayout.symm (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} {dst : LayoutState k} {b1 b2 : qs.Basis}
    (h : SameOutsideLayout qs dst b1 b2) : SameOutsideLayout qs dst b2 b1 := by
  intro e he; exact (h e he).symm

lemma SameOutsideLayout.trans
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  {k : ℕ} {dst : LayoutState k} {b1 b2 b3 : qs.Basis}
  (h12 : SameOutsideLayout qs dst b1 b2)
  (h23 : SameOutsideLayout qs dst b2 b3) :
  SameOutsideLayout qs dst b1 b3 := by
  intro e he
  calc
    extToInt e b1 = extToInt e b2 := h12 e he
    _ = extToInt e b3 := h23 e he

/-- Every physical qubit is either in a slot or can be read by an outside singleton register. -/
def CoversLayoutBits
    {k : ℕ}
    (dst : LayoutState k) : Prop :=
  ∀ q : ℕ,
    (∃ i : Fin k, q ∈ (dst.xslot i).active.qubits) ∨
    (∃ i : Fin k, q ∈ (dst.zslot i).active.qubits) ∨
    OutsideLayout dst (ExtReg.ofReg (qubitReg q))

/-- Equal register values imply equal bits for qubits inside that register. -/
lemma bit_eq_of_toNat_eq_on_reg
    {Basis : Type u}
    [RegEncoding Basis]
    {r : Reg}
    {b₁ b₂ : Basis}
    {q : ℕ}
    (hNat :
      RegEncoding.toNat r b₁ =
        RegEncoding.toNat r b₂)
    (hq : q ∈ r.qubits) :
    RegEncoding.bit q b₁ =
      RegEncoding.bit q b₂ := by
  calc
    RegEncoding.bit q b₁
        =
    RegEncoding.bit q
      (RegEncoding.writeNat
        r (RegEncoding.toNat r b₁) b₁) := by
          rw [RegEncoding.writeNat_toNat]
    _ =
    RegEncoding.bit q
      (RegEncoding.writeNat
        r (RegEncoding.toNat r b₂) b₂) := by
          simpa [hNat] using
            (RegEncoding.bit_writeNat_in
              (r := r)
              (v := RegEncoding.toNat r b₁)
              (b₁ := b₁)
              (b₂ := b₂)
              (q := q)
              hq)
    _ = RegEncoding.bit q b₂ := by
          rw [RegEncoding.writeNat_toNat]

/-- Equal signed interpretations imply equal raw active-register values. -/
lemma toNat_eq_of_extToInt_eq
    {Basis : Type u}
    [RegEncoding Basis]
    {e : ExtReg}
    {b₁ b₂ : Basis}
    (h :
      extToInt e b₁ =
        extToInt e b₂) :
    ExtReg.toNat e b₁ =
      ExtReg.toNat e b₂ := by
  apply tcDecodeWidth_inj_of_lt
    (ExtReg.toNat_lt e b₁)
    (ExtReg.toNat_lt e b₂)
  simpa [extToInt] using h

/-- Equal signed interpretations imply equal active bits. -/
lemma bit_eq_of_extToInt_eq_on_active
    {Basis : Type u}
    [RegEncoding Basis]
    {e : ExtReg}
    {b₁ b₂ : Basis}
    {q : ℕ}
    (h :
      extToInt e b₁ = extToInt e b₂)
    (hq : q ∈ e.active.qubits) :
    RegEncoding.bit q b₁ =
      RegEncoding.bit q b₂ := by
  exact bit_eq_of_toNat_eq_on_reg
    (toNat_eq_of_extToInt_eq h)
    hq

lemma SameOutsideLayout.bit_eq_of_outside
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    {dst : LayoutState k}
    {b₁ b₂ : qs.Basis}
    (hSO : SameOutsideLayout qs dst b₁ b₂)
    (q : ℕ)
    (hout :
      OutsideLayout dst
        (ExtReg.ofReg (qubitReg q))) :
    RegEncoding.bit q b₂ =
      RegEncoding.bit q b₁ := by
  apply bit_eq_of_extToInt_eq_on_active
  · exact
      (hSO
        (ExtReg.ofReg (qubitReg q))
        hout).symm
  · simp [ExtReg.ofReg, qubitReg, Reg.singleton]

/-- Classify any qubit as lying in an `x` slot, a `z` slot, or outside the layout. -/
lemma qubit_in_layout_or_outside
    {k : ℕ}
    (dst : LayoutState k)
    (q : ℕ) :
    (∃ i : Fin k,
      q ∈ (dst.xslot i).active.qubits) ∨
    (∃ i : Fin k,
      q ∈ (dst.zslot i).active.qubits) ∨
    OutsideLayout dst
      (ExtReg.ofReg (qubitReg q)) := by
  by_cases hx :
      ∃ i : Fin k,
        q ∈ (dst.xslot i).active.qubits
  · exact Or.inl hx
  by_cases hz :
      ∃ i : Fin k,
        q ∈ (dst.zslot i).active.qubits
  · exact Or.inr (Or.inl hz)
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · intro i
    have hqi :
        q ∉ (dst.xslot i).active.qubits := by
      intro h
      exact hx ⟨i, h⟩
    simpa [ExtReg.ActiveDisjoint, ExtReg.ofReg, qubitReg, Reg.singleton, Disjoint] using hqi
  · intro i
    have hqi :
        q ∉ (dst.zslot i).active.qubits := by
      intro h
      exact hz ⟨i, h⟩
    simpa [ExtReg.ActiveDisjoint, ExtReg.ofReg, qubitReg, Reg.singleton, Disjoint] using hqi

/-- The qubit classifier packaged as the layout coverage predicate. -/
theorem layout_covers_bits {k : ℕ} (dst : LayoutState k) : CoversLayoutBits dst := qubit_in_layout_or_outside dst

/-- Agreement on all layout slots plus outside agreement determines the whole basis state. -/
lemma basis_eq_of_sameOutside_and_slots
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (dst : LayoutState k)
    (bMid bNext : qs.Basis)
    (hSO :
      SameOutsideLayout qs dst bMid bNext)
    (hXslots :
      ∀ i : Fin k, extToInt (dst.xslot i) bNext  = extToInt (dst.xslot i) bMid)
    (hZslots :
      ∀ i : Fin k, extToInt (dst.zslot i) bNext = extToInt  (dst.zslot i) bMid) :
    bNext = bMid := by
  apply RegEncoding.basis_ext
  intro q
  rcases qubit_in_layout_or_outside dst q with
    hx | hz | hout
  · rcases hx with ⟨i, hq⟩
    exact bit_eq_of_extToInt_eq_on_active
      (hXslots i) hq
  · rcases hz with ⟨i, hq⟩
    exact bit_eq_of_extToInt_eq_on_active
      (hZslots i) hq
  · exact bit_eq_of_extToInt_eq_on_active
      ((hSO
        (ExtReg.ofReg (qubitReg q))
        hout).symm)
      (by simp [ExtReg.ofReg, qubitReg, Reg.singleton])

/-- The accumulated phase scalar is never zero. -/
lemma phaseScalarFrom_ne_zero
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  (k : ℕ) (phi : ℝ) (coeff : Fin (q k) → ℚ)
  (src : LayoutState k) (b0 : qs.Basis) :
  ∀ (pts : List Point) (n : ℕ) (hn : n + pts.length = q k),
    phaseScalarFrom (qs := qs) k phi coeff src b0 pts n hn ≠ 0 := by
  intro pts
  induction pts with
  | nil =>
      intro n hn
      simp [phaseScalarFrom]
  | cons pt pts ih =>
      intro n hn
      simp [phaseScalarFrom]
      have htail :
          phaseScalarFrom (qs := qs) k phi coeff src b0 pts (n + 1)
            (by
              simp at hn
              omega) ≠ 0 := by
        exact ih (n + 1) (by
          simp at hn
          omega)
      aesop

/-- Nonzero equal scalar multiples of basis kets have the same basis label. -/
lemma ket_eq_of_same_nonzero_smul
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {a : ℂ} {b1 b2 : qs.Basis}
  (ha : a ≠ 0)
  (h : a • qs.ket b1 = a • qs.ket b2) :
  b1 = b2 := by
  have hket : qs.ket b1 = qs.ket b2 := by
    simp_all only [ne_eq, not_false_eq_true, smul_right_inj]
  exact qs.ket_inj hket

/-- Start-state encodings are unique once slot values determine the basis state. -/
lemma encodesStateFrom_start_unique_of_ext
  (qs : QSemantics)
  [RegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (b0 b1 b2 : qs.Basis)
  (h1 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b1)
  (h2 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b2)
  (hdet :
    (∀ i : Fin k,
      extToInt (dst.xslot i) b1 =
      extToInt (dst.xslot i) b2) ∧
    (∀ i : Fin k,
      extToInt (dst.zslot i) b1 =
      extToInt (dst.zslot i) b2) →
    b1 = b2) :
  b1 = b2 := by
  apply hdet
  constructor
  · intro i
    calc
      extToInt (dst.xslot i) b1
          = evalRowX (qs := qs) src (State.start_state i) b0 := h1.1 i
      _ = extToInt (dst.xslot i) b2 := (h2.1 i).symm
  · intro i
    calc
      extToInt (dst.zslot i) b1
          = evalRowZ (qs := qs) src (State.start_state i) b0 := h1.2 i
      _ = extToInt (dst.zslot i) b2 := (h2.2 i).symm

/-! =========================================================
    Section 8: Canonical interpolation points
    The compiler uses its own `Point` type, while the algebraic Toom-Cook proof
    lives in `Toom_Cook_formula`. This section bridges the two representations.
========================================================= -/

/-- Alternating integer interpolation points around zero. -/
def alternatingPoint (i : ℕ) : Point :=
  if i % 2 == 0 then Point.int (i / 2 : ℤ) else Point.int (-((i + 1) / 2 : ℤ))

/-- Generate the canonical `2k - 1` interpolation points. -/
def genInterpolationPoints (k : ℕ) : List Point := (List.range (2 * k - 1)).map alternatingPoint

/-- Use the standalone math definition as the real meaning of good Toom-Cook points. -/
def GoodToomCookPoints
  (k : ℕ)
  (pts : List Point)
  (hpts : pts.length = q k) : Prop :=
  ToomCookMath.GoodInterpolationPoints
    (row := interpEntry k)
    (pts := ToomCookMath.listToFin pts hpts)

/--
Convert a compiler interpolation point to the pure-math point representation.
-/

def toMathPoint : Point → ToomCookMath.Point
  | Point.int z  => ToomCookMath.Point.int z
  | Point.frac c => ToomCookMath.Point.frac c

/--
The compiler's interpolation row is definitionally the pure-math adjusted row.
-/

lemma toMathPoint_interpEntry
    {k : ℕ}
    (p : Point)
    (j : Fin (q k)) :
    ToomCookMath.pointRow
      (q k) (toMathPoint p) j
      =
    interpEntry k p j := by
  cases p <;> rfl

lemma toMathPoint_alternatingPoint
    (i : ℕ) :
    toMathPoint (alternatingPoint i)
      =
    ToomCookMath.alternatingPoint i := by
  unfold alternatingPoint ToomCookMath.alternatingPoint
  unfold ToomCookMath.alternatingInt
  by_cases h : i % 2 == 0
  · simp [h, toMathPoint]
  · simp [h, toMathPoint]

lemma listToFin_genInterpolationPoints_toMathPoint
    (k : ℕ)
    (hpts : (genInterpolationPoints k).length = q k)
    (hmath :
      (ToomCookMath.genFiniteInterpolationPoints (q k)).length = q k)
    (i : Fin (q k)) :
    ToomCookMath.listToFin
        (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath i
      =
    toMathPoint
      (ToomCookMath.listToFin (genInterpolationPoints k) hpts i) := by
  simp [ToomCookMath.listToFin, genInterpolationPoints, ToomCookMath.genFiniteInterpolationPoints, toMathPoint_alternatingPoint]

lemma genInterpolationPoints_good
    (k : ℕ) :
    GoodToomCookPoints k
      (genInterpolationPoints k)
      (by simp [genInterpolationPoints, q]) := by
  let hpts : (genInterpolationPoints k).length = q k := by
    simp [genInterpolationPoints, q]
  let hmath :
      (ToomCookMath.genFiniteInterpolationPoints (q k)).length = q k := by
    simp [ToomCookMath.genFiniteInterpolationPoints]
  unfold GoodToomCookPoints
  have hgoodMath :
      ToomCookMath.GoodInterpolationPoints
        (row := ToomCookMath.pointRow (q k))
        (pts :=
          ToomCookMath.listToFin
            (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath) := by
    exact ToomCookMath.genFiniteInterpolationPoints_good (q k) hmath
  apply ToomCookMath.GoodInterpolationPoints.congr_matrix
    (rowA := ToomCookMath.pointRow (q k))
    (rowB := interpEntry k)
    (ptsA :=
      ToomCookMath.listToFin
        (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath)
    (ptsB :=
      ToomCookMath.listToFin (genInterpolationPoints k) hpts)
  · intro i j
    rw [listToFin_genInterpolationPoints_toMathPoint (k := k) (hpts := hpts) (hmath := hmath) (i := i)]
    exact toMathPoint_interpEntry
      (k := k)
      ((ToomCookMath.listToFin (genInterpolationPoints k) hpts) i)
      j
  · exact hgoodMath
end Shor
