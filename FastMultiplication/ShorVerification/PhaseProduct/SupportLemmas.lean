import FastMultiplication.ShorVerification.PhaseProduct.Core
import FastMultiplication.ShorVerification.MathBackBone.Toom_Cook_formula

namespace Shor
open Gate
open Operations
open scoped BigOperators

def WellFormedReg (r : Reg) : Prop :=
  r.lo ≤ r.hi

lemma phaseLimbWidth_valid_left
    (x z : ExtReg) {k : ℕ} (hk : 0 < k) :
    ValidPhaseSplit x k (phaseLimbWidth x z k) := by
  unfold ValidPhaseSplit phaseLimbWidth phaseLimbWidthOfWidth
  constructor
  · exact hk
  ·
    have hW :
        min (ExtReg.width x / k) (ExtReg.width z / k) ≤ ExtReg.width x / k :=
      Nat.min_le_left _ _
    have hmul₁ :
        (k - 1) * min (ExtReg.width x / k) (ExtReg.width z / k)
          ≤ (k - 1) * (ExtReg.width x / k) :=
      Nat.mul_le_mul_left _ hW
    have hmul₂ :
        (k - 1) * (ExtReg.width x / k)
          ≤ k * (ExtReg.width x / k) := by
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hmul₃ :
        k * (ExtReg.width x / k) ≤ ExtReg.width x := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (ExtReg.width x) k
    exact le_trans hmul₁ (le_trans hmul₂ hmul₃)

lemma phaseLimbWidth_valid_right
    (x z : ExtReg) {k : ℕ} (hk : 0 < k) :
    ValidPhaseSplit z k (phaseLimbWidth x z k) := by
  unfold ValidPhaseSplit phaseLimbWidth phaseLimbWidthOfWidth
  constructor
  · exact hk
  ·
    have hW :
        min (ExtReg.width x / k) (ExtReg.width z / k) ≤ ExtReg.width z / k :=
      Nat.min_le_right _ _
    have hmul₁ :
        (k - 1) * min (ExtReg.width x / k) (ExtReg.width z / k)
          ≤ (k - 1) * (ExtReg.width z / k) :=
      Nat.mul_le_mul_left _ hW
    have hmul₂ :
        (k - 1) * (ExtReg.width z / k)
          ≤ k * (ExtReg.width z / k) := by
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hmul₃ :
        k * (ExtReg.width z / k) ≤ ExtReg.width z := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (ExtReg.width z) k
    exact le_trans hmul₁ (le_trans hmul₂ hmul₃)

lemma splitExtReg_disjoint
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (i j : Fin k)
    (hij : i ≠ j) :
    Disjoint (splitExtReg (Basis:=Basis) e k W i).base
             (splitExtReg (Basis:=Basis) e k W j).base := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_disjoint e k W i j hij

lemma splitExtReg_disjoint_of_disjoint
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (x z : ExtReg) (k W : ℕ) (i j : Fin k)
    (hxz : Disjoint x.base z.base) :
    Disjoint (splitExtReg (Basis:=Basis) x k W i).base
             (splitExtReg (Basis:=Basis) z k W j).base := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_disjoint_of_disjoint x z k W i j hxz

lemma splitExtReg_disjoint_reg_of_disjoint
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (r : Reg) (k W : ℕ) (i : Fin k)
    (her : Disjoint e.base r) :
    Disjoint (splitExtReg (Basis:=Basis) e k W i).base r := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_disjoint_reg_of_disjoint e r k W i her

lemma splitExtReg_reconstruct_int
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (b : Basis)
    (hValid : ValidPhaseSplit e k W) :
    ((ExtRegEncoding.extToInt e b : ℤ) : ℚ)
      =
    ∑ i : Fin k,
      ((splitChunkInt e W i b : ℤ) : ℚ)
        * ((2 : ℚ) ^ W) ^ (i : ℕ) := by
  unfold splitChunkInt splitExtReg
  simpa using
    ExtRegSplitSemantics.split_reconstruct_int
      (Basis := Basis) e k W b hValid

lemma annotatePhaseTermsAux_append
  (k : ℕ) (n : ℕ)
  (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k n (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k n ops₁ ++
      annotatePhaseTermsAux k (n + phaseProductCount ops₁) ops₂ := by
  induction ops₁ generalizing n with
  | nil =>
      simp [annotatePhaseTermsAux, phaseProductCount]
  | cons op ops₁ ih =>
      cases op <;>simp [annotatePhaseTermsAux, phaseProductCount, ih, Nat.add_assoc, Nat.add_comm]

lemma annotatePhaseTermsAux_append_zero
  (k : ℕ) (ops₁ ops₂ : List (valid_ops k)) :
  annotatePhaseTermsAux k 0 (ops₁ ++ ops₂) =
    annotatePhaseTermsAux k 0 ops₁ ++
      annotatePhaseTermsAux k (phaseProductCount ops₁) ops₂ := by
  simpa using annotatePhaseTermsAux_append k 0 ops₁ ops₂

@[simp] lemma phaseProductCount_addConstAux
  {k : ℕ} (dst src : Fin k) (neg' : Bool) (n sh : ℕ) :
  phaseProductCount (addConstAux (k := k) dst src neg' n sh) = 0 := by
  rw [addConstAux_eq_shifts (k := k) (dst := dst) (src := src) (neg' := neg') n sh]
  induction shiftsOfAux n sh with
  | nil =>
      simp [phaseProductCount]
  | cons s ss ih =>
      simp [phaseProductCount, ih]

@[simp] lemma phaseProductCount_addConstFrom
  {k : ℕ} (dst src : Fin k) (c : Int) :
  phaseProductCount (addConstFrom (k := k) dst src c) = 0 := by
  by_cases hc : c = 0
  · simp [addConstFrom, hc, phaseProductCount]
  · simp [addConstFrom, hc, phaseProductCount_addConstAux]

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
      simp [computeLocalAux, phaseProductCount_append,
            phaseProductCount_addConstFrom,
            phaseProductCount_computeLocalAux]

@[simp] lemma phaseProductCount_computeLocal2
  {k : ℕ} (hk : 0 < k) (z : Int) :
  phaseProductCount (computeLocal2 (k := k) hk z) = 0 := by
  simp [computeLocal2, phaseProductCount_computeLocalAux]

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

variable (qs : QSemantics) [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
variable [GateSemanticsFacts qs]

omit [RegEncoding QSemantics.Basis] in
lemma gate_eq_of_ket_eq
  {U V : Gate}
  (hket : ∀ b : qs.Basis, qs.eval U (qs.ket b) = qs.eval V (qs.ket b)) :
  ∀ ψ : qs.State, qs.eval U ψ = qs.eval V ψ := by
  intro ψ
  let P : qs.State → Prop := fun ψ => qs.eval U ψ = qs.eval V ψ
  have h0 : P 0 := by
    dsimp [P]
    rw [qs.eval_zero, qs.eval_zero]
  have hadd : ∀ ψ φ, P ψ → P φ → P (ψ + φ) := by
    intro ψ φ hψ hφ
    dsimp [P] at *
    rw [qs.eval_add, qs.eval_add, hψ, hφ]
  have hsmul : ∀ (a : ℂ) ψ, P ψ → P (a • ψ) := by
    intro a ψ hψ
    dsimp [P] at *
    rw [qs.eval_smul, qs.eval_smul, hψ]
  have hbasis : ∀ b : qs.Basis, P (qs.ket b) := by
    intro b
    dsimp [P]
    exact hket b
  exact qs.state_induction P h0 hadd hsmul hbasis ψ

lemma EncodesStateFromWithWidths.toFits
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  {src dst : LayoutState k} {cur : WidthState k}
  {σ : State k} {b0 b : qs.Basis}
  (h : EncodesStateFromWithWidths
    (qs := qs) src dst cur σ b0 b) :
  EncodesStateFromFits (qs := qs) src dst σ b0 b := by
  rcases h with ⟨hEnc, hSoundX, hDom⟩
  rcases hSoundX with ⟨hSoundX, hSoundZ⟩
  rcases hDom with ⟨hDomX, hDomZ⟩
  refine ⟨hEnc, ?_, ?_⟩
  ·
    intro i
    exact FitsSignedWidth_mono (hDomX i) (hSoundX i)
  ·
    intro i
    exact FitsSignedWidth_mono (hDomZ i) (hSoundZ i)

/-- I recommend replacing the original `scanNeededWidths` body by this exact helper call. -/
lemma scanNeededWidths_eq_aux {k : ℕ} (x z : ExtReg) (ops : List (valid_ops k)) :
  scanNeededWidths x z ops =
    scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops := by
  simp[scanNeededWidths]


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

lemma tcDecodeWidth_fits_succ
  {w n : ℕ}
  (h : n < 2 ^ w) :
  FitsSignedWidth (w + 1) (tcDecodeWidth w n) := by
  unfold FitsSignedWidth signedMin signedMax tcDecodeWidth
  by_cases hs : n < 2 ^ (w - 1)
  · simp
    constructor <;>
    split
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
    constructor <;>
    split
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

lemma extToInt_fits_width_succ
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  (e : ExtReg) (b : qs.Basis) :
  FitsSignedWidth (ExtReg.width e + 1) (ExtRegEncoding.extToInt e b) := by
  unfold ExtRegEncoding.extToInt
  have hlt : ExtRegEncoding.extToNat e b < 2 ^ ExtReg.width e := by
    simpa using
      (ExtRegEncoding.extToNat_lt
        (Basis := qs.Basis) (e := e) (b := b))
  exact tcDecodeWidth_fits_succ hlt


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
    Section 19: Start-state and layout-width lemmas
========================================================= -/

/-- Start-state row evaluation picks out the requested x-slot. -/
lemma evalRowX_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowX (qs := qs) st (State.start_state i) b = sourceChunkXInt (qs := qs) st i b := by
  unfold evalRowX State.start_state
  simp

/-- Start-state row evaluation picks out the requested z-slot. -/
lemma evalRowZ_start_state
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (st : LayoutState k) (i : Fin k) (b : qs.Basis) :
  evalRowZ (qs := qs) st (State.start_state i) b = sourceChunkZInt (qs := qs) st i b := by
  unfold evalRowZ State.start_state
  simp

lemma splitExtReg_width_of_valid
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    (e : ExtReg) (k W : ℕ) (i : Fin k)
    (hValid : ValidPhaseSplit e k W) :
    ExtReg.width (splitExtReg (Basis := Basis) e k W i)
      =
    phaseSplitLogicalWidth (ExtReg.width e) W k i := by
  simpa [splitExtReg] using
    ExtRegSplitSemantics.split_width
      (Basis := Basis) e k W i hValid

lemma stInit_xslot_width
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (i : Fin k) :
    ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).xslot i)
      =
    (initWidthState x z k).xw i := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hValidX : ValidPhaseSplit x k (phaseLimbWidth x z k) :=
    phaseLimbWidth_valid_left x z hk
  unfold initSignedLayoutState initWidthState
  dsimp
  exact
    splitExtReg_width_of_valid
      (Basis := Basis)
      x k (phaseLimbWidth x z k) i hValidX

lemma stInit_zslot_width
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (i : Fin k) :
    ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).zslot i)
      =
    (initWidthState x z k).zw i := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hValidZ : ValidPhaseSplit z k (phaseLimbWidth x z k) :=
    phaseLimbWidth_valid_right x z hk
  unfold initSignedLayoutState initWidthState
  dsimp
  exact
    splitExtReg_width_of_valid
      (Basis := Basis)
      z k (phaseLimbWidth x z k) i hValidZ

lemma stFinal_xslot_eq_addExtra
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := Basis) x z k
    let stFinal := targetSignedLayoutState (Basis := Basis) x z k
      (scanNeededWidths x z ops)
    stFinal.xslot i =
      ExtReg.addExtra (stInit.xslot i)
        (extraDelta (stInit.xslot i) (stFinal.xslot i)) := by
  dsimp [targetSignedLayoutState]
  exact widenExtRegTo_eq_addExtra _ _

lemma stFinal_zslot_eq_addExtra
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := Basis) x z k
    let stFinal := targetSignedLayoutState (Basis := Basis) x z k
      (scanNeededWidths x z ops)
    stFinal.zslot i =
      ExtReg.addExtra (stInit.zslot i)
        (extraDelta (stInit.zslot i) (stFinal.zslot i)) := by
  dsimp [targetSignedLayoutState]
  exact widenExtRegTo_eq_addExtra _ _

/-! =========================================================
    Section 20: Row-evaluation arithmetic lemmas
========================================================= -/


lemma evalRowX_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma evalRowZ_shiftL_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma evalRowX_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma evalRowZ_negate_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma evalRowX_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma evalRowZ_shiftR_exact
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma evalRowX_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma evalRowZ_addScaled_raw
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma widenExtRegTo_width_of_le
    (e : ExtReg) (W : ℕ)
    (h : ExtReg.width e ≤ W) :
    ExtReg.width (widenExtRegTo e W) = W := by
  simp [widenExtRegTo, ExtReg.width, ExtReg.addExtra]
  have : regSize e.base + e.extra ≤ W := by
    simp [ExtReg.width] at h
    exact h
  omega

lemma targetSignedLayoutState_xslot_width_scan
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    ExtReg.width
      ((targetSignedLayoutState
        (Basis := Basis) x z k (scanNeededWidths x z ops)).xslot i)
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  apply widenExtRegTo_width_of_le
  have hinit :
      ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).xslot i)
        =
      (initWidthState x z k).xw i :=
    stInit_xslot_width (Basis := Basis) x z i
  have hscan :
      (initWidthState x z k).xw i
        ≤
      (scanNeededWidths x z ops).xneed i := by
    rw [scanNeededWidths_eq_aux]
    simpa [widthsOfState] using
      scanNeededWidthsAux_x_ge
        (i := i)
        ops
        (initWidthState x z k)
        (widthsOfState (initWidthState x z k))
  have hW :
      (scanNeededWidths x z ops).xneed i + 1
        ≤
      commonNeededWidth (scanNeededWidths x z ops) :=
    commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i
  rw [hinit]
  omega

lemma targetSignedLayoutState_zslot_width_scan
    {Basis : Type u}
    [RegEncoding Basis]
    [ExtRegEncoding Basis]
    [ExtRegSplitSemantics Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    ExtReg.width
      ((targetSignedLayoutState
        (Basis := Basis) x z k (scanNeededWidths x z ops)).zslot i)
      =
    commonNeededWidth (scanNeededWidths x z ops) := by
  apply widenExtRegTo_width_of_le
  have hinit :
      ExtReg.width ((initSignedLayoutState (Basis := Basis) x z k).zslot i)
        =
      (initWidthState x z k).zw i :=
    stInit_zslot_width (Basis := Basis) x z i
  have hscan :
      (initWidthState x z k).zw i
        ≤
      (scanNeededWidths x z ops).zneed i := by
    rw [scanNeededWidths_eq_aux]
    simpa [widthsOfState] using
      scanNeededWidthsAux_z_ge
        (i := i)
        ops
        (initWidthState x z k)
        (widthsOfState (initWidthState x z k))
  have hW :
      (scanNeededWidths x z ops).zneed i + 1
        ≤
      commonNeededWidth (scanNeededWidths x z ops) :=
    commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i
  rw [hinit]
  omega

/-! =========================================================
    Section 24: Source chunk fit and initial soundness
========================================================= -/

lemma sourceChunkXInt_fits_width_succ
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (st : LayoutState k)
  (i : Fin k)
  (b : qs.Basis) :
  FitsSignedWidth (ExtReg.width (st.xslot i) + 1)
    (sourceChunkXInt (qs := qs) st i b) := by
  unfold sourceChunkXInt
  by_cases htop : isTopChunk i
  · simp [htop]
    exact extToInt_fits_width_succ qs (st.xslot i) b
  · simp [htop]
    apply FitsSignedWidth_of_nonneg_lt_pow
    simpa [ExtReg.toNat] using
      (ExtRegEncoding.extToNat_lt (e := st.xslot i) (b := b))

lemma sourceChunkZInt_fits_width_succ
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [ExtRegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {k : ℕ}
  (st : LayoutState k)
  (i : Fin k)
  (b : qs.Basis) :
  FitsSignedWidth (ExtReg.width (st.zslot i) + 1)
    (sourceChunkZInt (qs := qs) st i b) := by
  unfold sourceChunkZInt
  by_cases htop : isTopChunk i
  · simp [htop]
    exact extToInt_fits_width_succ qs (st.zslot i) b
  · simp [htop]
    apply FitsSignedWidth_of_nonneg_lt_pow
    simpa [ExtReg.toNat] using
      (ExtRegEncoding.extToNat_lt (e := st.zslot i) (b := b))



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

lemma extraDelta_xslot_pos
    (qs : QSemantics)
    [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
    let stFinal := targetSignedLayoutState
      (Basis := qs.Basis) x z k (scanNeededWidths x z ops)
    0 < extraDelta (stInit.xslot i) (stFinal.xslot i) := by
  dsimp
  let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
  let Wwork := commonNeededWidth (scanNeededWidths x z ops)

  have hinit :
      ExtReg.width (stInit.xslot i) = (initWidthState x z k).xw i := by
    simpa [stInit] using
      stInit_xslot_width (Basis := qs.Basis) x z i

  have hscan :
      (initWidthState x z k).xw i ≤
        (scanNeededWidths x z ops).xneed i :=
    scanNeededWidths_x_ge_init x z ops i

  have hW :
      (scanNeededWidths x z ops).xneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_xneed (scanNeededWidths x z ops) i

  have hlt : ExtReg.width (stInit.xslot i) < Wwork := by
    rw [hinit]
    omega

  simpa [targetSignedLayoutState, stInit, Wwork] using
    extraDelta_widenExtRegTo_pos (stInit.xslot i) Wwork hlt

lemma extraDelta_zslot_pos
    (qs : QSemantics)
    [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
    [ExtRegSplitSemantics qs.Basis]
    {k : ℕ} (x z : ExtReg) (ops : Prog k) (i : Fin k) :
    let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
    let stFinal := targetSignedLayoutState
      (Basis := qs.Basis) x z k (scanNeededWidths x z ops)
    0 < extraDelta (stInit.zslot i) (stFinal.zslot i) := by
  dsimp
  let stInit := initSignedLayoutState (Basis := qs.Basis) x z k
  let Wwork := commonNeededWidth (scanNeededWidths x z ops)

  have hinit :
      ExtReg.width (stInit.zslot i) = (initWidthState x z k).zw i := by
    simpa [stInit] using
      stInit_zslot_width (Basis := qs.Basis) x z i

  have hscan :
      (initWidthState x z k).zw i ≤
        (scanNeededWidths x z ops).zneed i :=
    scanNeededWidths_z_ge_init x z ops i

  have hW :
      (scanNeededWidths x z ops).zneed i + 1 ≤ Wwork :=
    commonNeededWidth_ge_zneed (scanNeededWidths x z ops) i

  have hlt : ExtReg.width (stInit.zslot i) < Wwork := by
    rw [hinit]
    omega

  simpa [targetSignedLayoutState, stInit, Wwork] using
    extraDelta_widenExtRegTo_pos (stInit.zslot i) Wwork hlt

lemma eval_compileAnnotatedOpsToSignedGateAux_append
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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
    Section 7: Layout disjointness
========================================================= -/

def LayoutSlotsDisjoint {k : ℕ} (st : LayoutState k) : Prop :=
  (∀ i j : Fin k, i ≠ j → Disjoint (st.xslot i).base (st.xslot j).base) ∧
  (∀ i j : Fin k, i ≠ j → Disjoint (st.zslot i).base (st.zslot j).base) ∧
  (∀ i j : Fin k, Disjoint (st.xslot i).base (st.zslot j).base)

def OutsideLayout {k : ℕ} (dst : LayoutState k) (e : ExtReg) : Prop :=
  (∀ i : Fin k, Disjoint e.base (dst.xslot i).base) ∧
  (∀ i : Fin k, Disjoint e.base (dst.zslot i).base)

def SameOutsideLayout
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (dst : LayoutState k) (b1 b2 : qs.Basis) : Prop :=
  ∀ e : ExtReg, OutsideLayout dst e →
    ExtRegEncoding.extToInt e b1 = ExtRegEncoding.extToInt e b2

lemma SameOutsideLayout.refl
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} (dst : LayoutState k) (b : qs.Basis) :
  SameOutsideLayout qs dst b b := by
  intro e he
  rfl

lemma SameOutsideLayout.symm
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} {dst : LayoutState k} {b1 b2 : qs.Basis}
  (h : SameOutsideLayout qs dst b1 b2) :
  SameOutsideLayout qs dst b2 b1 := by
  intro e he
  symm
  exact h e he

lemma SameOutsideLayout.trans
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ} {dst : LayoutState k} {b1 b2 b3 : qs.Basis}
  (h12 : SameOutsideLayout qs dst b1 b2)
  (h23 : SameOutsideLayout qs dst b2 b3) :
  SameOutsideLayout qs dst b1 b3 := by
  intro e he
  calc
    ExtRegEncoding.extToInt e b1 = ExtRegEncoding.extToInt e b2 := h12 e he
    _ = ExtRegEncoding.extToInt e b3 := h23 e he


def CoversLayoutBits {k : ℕ} (dst : LayoutState k) : Prop :=
  ∀ q : ℕ,
    (∃ i : Fin k, (dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi) ∨
    (∃ i : Fin k, (dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi) ∨
    OutsideLayout dst (ExtReg.ofReg (qubitReg q))

lemma bit_eq_of_toNat_eq_on_reg
  {Basis : Type u} [RegEncoding Basis]
  {r : Reg} {b1 b2 : Basis} {q : ℕ}
  (hNat : RegEncoding.toNat r b1 = RegEncoding.toNat r b2)
  (hqlo : r.lo ≤ q) (hqhi : q < r.hi) :
  RegEncoding.bit q b1 = RegEncoding.bit q b2 := by
  calc
    RegEncoding.bit q b1
        = RegEncoding.bit q (RegEncoding.writeNat r (RegEncoding.toNat r b1) b1) := by
            rw [RegEncoding.writeNat_toNat]
    _   = RegEncoding.bit q (RegEncoding.writeNat r (RegEncoding.toNat r b2) b2) := by
            simpa [hNat] using
              (RegEncoding.bit_writeNat_in
                (r := r) (v := RegEncoding.toNat r b1)
                (b1 := b1) (b2 := b2) (q := q) hqlo hqhi)
    _   = RegEncoding.bit q b2 := by
            rw [RegEncoding.writeNat_toNat]

lemma basis_eq_of_sameOutside_and_slots
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  {k : ℕ}
  (dst : LayoutState k)
  (bMid bNext : qs.Basis)
  (hSO : SameOutsideLayout qs dst bMid bNext)
  (hXslots :
    ∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.xslot i) bNext
        = ExtRegEncoding.extToInt (dst.xslot i) bMid)
  (hZslots :
    ∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.zslot i) bNext
        = ExtRegEncoding.extToInt (dst.zslot i) bMid)
  (hcover : CoversLayoutBits dst)
  (hbit_of_ext :
    ∀ (e : ExtReg) (b1 b2 : qs.Basis) (q : ℕ),
      ExtRegEncoding.extToInt e b1 = ExtRegEncoding.extToInt e b2 →
      e.base.lo ≤ q → q < e.base.hi →
      RegEncoding.bit q b1 = RegEncoding.bit q b2) :
  bNext = bMid := by
  apply RegEncoding.basis_ext
  intro q
  rcases hcover q with hx | hz | hout
  · rcases hx with ⟨i, hqlo, hqhi⟩
    exact hbit_of_ext (dst.xslot i) bNext bMid q (hXslots i) hqlo hqhi
  · rcases hz with ⟨i, hqlo, hqhi⟩
    exact hbit_of_ext (dst.zslot i) bNext bMid q (hZslots i) hqlo hqhi
  · exact hbit_of_ext (ExtReg.ofReg (qubitReg q)) bNext bMid q
      (by
        symm
        exact hSO (ExtReg.ofReg (qubitReg q)) hout)
      (by simp [qubitReg, ExtReg.ofReg])
      (by simp [qubitReg, ExtReg.ofReg])


lemma qubit_in_layout_or_outside
  {k : ℕ} (dst : LayoutState k) (q : ℕ) :
  (∃ i : Fin k, (dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi) ∨
  (∃ i : Fin k, (dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi) ∨
  OutsideLayout dst (ExtReg.ofReg (qubitReg q)) := by
  by_cases hx : ∃ i : Fin k, (dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi
  · exact Or.inl hx
  · by_cases hz : ∃ i : Fin k, (dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (by
        constructor
        · intro i
          have hnot : ¬ ((dst.xslot i).base.lo ≤ q ∧ q < (dst.xslot i).base.hi) := by
            intro hqi
            exact hx ⟨i, hqi.1, hqi.2⟩
          unfold Disjoint qubitReg
          simp at *; simp[ExtReg.ofReg]
          omega
        · intro i
          have hnot : ¬ ((dst.zslot i).base.lo ≤ q ∧ q < (dst.zslot i).base.hi) := by
            intro hqi
            exact hz ⟨i, hqi.1, hqi.2⟩
          unfold Disjoint qubitReg
          simp at *; simp[ExtReg.ofReg]
          omega))

lemma phaseScalarFrom_ne_zero
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
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

lemma ket_eq_of_same_nonzero_smul
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis]
  [GateSemanticsFacts qs]
  {a : ℂ} {b1 b2 : qs.Basis}
  (ha : a ≠ 0)
  (h : a • qs.ket b1 = a • qs.ket b2) :
  b1 = b2 := by
  have hket : qs.ket b1 = qs.ket b2 := by
    simp_all only [ne_eq, not_false_eq_true, smul_right_inj]
  exact qs.ket_inj hket

lemma encodesStateFrom_start_unique_of_ext
  (qs : QSemantics)
  [RegEncoding qs.Basis] [ExtRegEncoding qs.Basis] [GateSemanticsFacts qs]
  {k : ℕ}
  (src dst : LayoutState k)
  (b0 b1 b2 : qs.Basis)
  (h1 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b1)
  (h2 : EncodesStateFrom (qs := qs) src dst State.start_state b0 b2)
  (hdet :
    (∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.xslot i) b1 =
      ExtRegEncoding.extToInt (dst.xslot i) b2) ∧
    (∀ i : Fin k,
      ExtRegEncoding.extToInt (dst.zslot i) b1 =
      ExtRegEncoding.extToInt (dst.zslot i) b2) →
    b1 = b2) :
  b1 = b2 := by
  apply hdet
  constructor
  · intro i
    calc
      ExtRegEncoding.extToInt (dst.xslot i) b1
          = evalRowX (qs := qs) src (State.start_state i) b0 := h1.1 i
      _ = ExtRegEncoding.extToInt (dst.xslot i) b2 := (h2.1 i).symm
  · intro i
    calc
      ExtRegEncoding.extToInt (dst.zslot i) b1
          = evalRowZ (qs := qs) src (State.start_state i) b0 := h1.2 i
      _ = ExtRegEncoding.extToInt (dst.zslot i) b2 := (h2.2 i).symm


/-- Alternating integer interpolation points around zero. -/
def alternatingPoint (i : ℕ) : Point :=
  if i % 2 == 0 then
    Point.int (i / 2 : ℤ)
  else
    Point.int (-((i + 1) / 2 : ℤ))

/-- Generate the canonical `2k - 1` interpolation points. -/
def genInterpolationPoints (k : ℕ) : List Point :=
  (List.range (2 * k - 1)).map alternatingPoint

/-- Use the standalone math definition as the real meaning of good Toom-Cook points. -/
def GoodToomCookPoints
  (k : ℕ)
  (pts : List Point)
  (hpts : pts.length = q k) : Prop :=
  ToomCookMath.GoodInterpolationPoints
    (row := interpEntry k)
    (pts := ToomCookMath.listToFin pts hpts)

/-- Convert Shor interpolation points to the pure math point type. -/
def toMathPoint : Point → ToomCookMath.Point
  | Point.int z => ToomCookMath.Point.int z
  | Point.inf   => ToomCookMath.Point.inf

lemma toMathPoint_interpEntry
    {k : ℕ}
    (p : Point)
    (j : Fin (q k)) :
    ToomCookMath.pointRow (q k) (toMathPoint p) j
      =
    interpEntry k p j := by
  cases p with
  | int z =>
      simp [toMathPoint, ToomCookMath.pointRow, interpEntry]
  | inf =>
      simp [toMathPoint, ToomCookMath.pointRow, interpEntry, q]

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
  simp [
    ToomCookMath.listToFin,
    genInterpolationPoints,
    ToomCookMath.genFiniteInterpolationPoints,
    toMathPoint_alternatingPoint
  ]

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
    rw [listToFin_genInterpolationPoints_toMathPoint
      (k := k)
      (hpts := hpts)
      (hmath := hmath)
      (i := i)]
    exact toMathPoint_interpEntry
      (k := k)
      ((ToomCookMath.listToFin (genInterpolationPoints k) hpts) i)
      j

  · exact hgoodMath

end Shor
