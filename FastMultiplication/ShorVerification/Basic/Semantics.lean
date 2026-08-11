import FastMultiplication.ShorVerification.Basic.Gates
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — abstract quantum semantics
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

/-! =========================================================
    Section 6: Abstract quantum semantics
========================================================= -/

/--
Abstract Hilbert-space semantics. This class deliberately does not mention any
circuit language: high-level `Gate` and low-level `LowGate` evaluators are
separate semantic interfaces built on top of the same quantum state space.
-/
class QSemantics where
  Basis : Type u
  State : Type u

  [instNormed : NormedAddCommGroup State]
  [instIP     : InnerProductSpace ℂ State]

  ket   : Basis → State

  state_induction :
    ∀ (P : State → Prop),
      P 0 →
      (∀ ψ φ, P ψ → P φ → P (ψ + φ)) →
      (∀ (a : ℂ) ψ, P ψ → P (a • ψ)) →
      (∀ b : Basis, P (ket b)) →
      ∀ ψ, P ψ

  ket_ne_zero (b : Basis) :
    ket b ≠ 0

  ket_inj : Function.Injective ket

  ket_inner_eq_of_eq :
    ∀ {b₁ b₂ : Basis},
      b₁ = b₂ →
      inner ℂ (ket b₁) (ket b₂) = (1 : ℂ)

  ket_inner_eq_zero_of_ne :
    ∀ {b₁ b₂ : Basis},
      b₁ ≠ b₂ →
      inner ℂ (ket b₁) (ket b₂) = 0


open QSemantics


attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

lemma ket_inner_self
    (qs : QSemantics)
    (b : qs.Basis) :
    inner ℂ (qs.ket b) (qs.ket b) = (1 : ℂ) := by
  exact qs.ket_inner_eq_of_eq rfl

lemma ket_inner_ne
    (qs : QSemantics)
    {b₁ b₂ : qs.Basis}
    (h : b₁ ≠ b₂) :
    inner ℂ (qs.ket b₁) (qs.ket b₂) = 0 := by
  exact qs.ket_inner_eq_zero_of_ne h

lemma ket_norm_one
    (qs : QSemantics)
    (b : qs.Basis) :
    ‖qs.ket b‖ = 1 := by
  have hinner :
      inner ℂ (qs.ket b) (qs.ket b) = (1 : ℂ) :=
    ket_inner_self qs b

  have hsq :
      ‖qs.ket b‖ ^ 2 = (1 : ℝ) := by
    calc
      ‖qs.ket b‖ ^ 2
          = Complex.re (inner ℂ (qs.ket b) (qs.ket b)) := by
              simpa using
                (norm_sq_eq_re_inner (𝕜 := ℂ) (qs.ket b))
      _ = 1 := by
              simp at hinner; cases hinner<;> rename_i h<;> simp[h]

  have hnonneg : 0 ≤ ‖qs.ket b‖ := norm_nonneg _

  have hfactor :
      (‖qs.ket b‖ - 1) * (‖qs.ket b‖ + 1) = 0 := by
    nlinarith

  have hplus_ne :
      ‖qs.ket b‖ + 1 ≠ 0 := by
    nlinarith

  have hminus :
      ‖qs.ket b‖ - 1 = 0 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact h
    · exfalso
      exact hplus_ne h

  nlinarith
/-! =========================================================
    Section 7: Gate-specific semantic fact classes
========================================================= -/

/--
Generic semantics for the internal high-level `Gate` language.

This is intentionally separate from `QSemantics`: the quantum model supplies
states and basis kets, while this class supplies the evaluator and the generic
linear/isometric laws for the private proof IR.
-/
class GateSemanticsCore
  (qs : QSemantics)
  [RegEncoding qs.Basis] : Type where

  eval  : Gate → qs.State → qs.State

  eval_id  : ∀ ψ, eval Gate.id ψ = ψ
  eval_seq : ∀ U V ψ, eval (U ;; V) ψ = eval V (eval U ψ)

  inner_preserved :
    ∀ U ψ φ, inner ℂ (eval U ψ) (eval U φ) = inner ℂ ψ φ

  eval_zero : ∀ U, eval U 0 = 0
  eval_add  : ∀ U ψ φ, eval U (ψ + φ) = eval U ψ + eval U φ
  eval_smul : ∀ U (a : ℂ) ψ, eval U (a • ψ) = a • eval U ψ

  hsub : ∀ U ψ φ, eval U (ψ - φ) = eval U ψ - eval U φ

  eval_adj_apply :
    ∀ (U : Gate) (ψ : qs.State),
      eval (Gate.adj U) (eval U ψ) = ψ

  eval_apply_adj :
    ∀ (U : Gate) (ψ : qs.State),
      eval U (eval (Gate.adj U) ψ) = ψ

namespace QSemantics

noncomputable abbrev eval
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] :
    Gate → qs.State → qs.State :=
  GateSemanticsCore.eval (qs := qs)

theorem eval_id
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (ψ : qs.State) :
    qs.eval Gate.id ψ = ψ :=
  GateSemanticsCore.eval_id (qs := qs) ψ

theorem eval_seq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U V : Gate)
    (ψ : qs.State) :
    qs.eval (U ;; V) ψ = qs.eval V (qs.eval U ψ) :=
  GateSemanticsCore.eval_seq (qs := qs) U V ψ

theorem inner_preserved
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    inner ℂ (qs.eval U ψ) (qs.eval U φ) = inner ℂ ψ φ :=
  GateSemanticsCore.inner_preserved (qs := qs) U ψ φ

theorem eval_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate) :
    qs.eval U 0 = 0 :=
  GateSemanticsCore.eval_zero (qs := qs) U

theorem eval_add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    qs.eval U (ψ + φ) = qs.eval U ψ + qs.eval U φ :=
  GateSemanticsCore.eval_add (qs := qs) U ψ φ

theorem eval_smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (a : ℂ)
    (ψ : qs.State) :
    qs.eval U (a • ψ) = a • qs.eval U ψ :=
  GateSemanticsCore.eval_smul (qs := qs) U a ψ

theorem hsub
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ φ : qs.State) :
    qs.eval U (ψ - φ) = qs.eval U ψ - qs.eval U φ :=
  GateSemanticsCore.hsub (qs := qs) U ψ φ

theorem eval_adj_apply
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
    qs.eval (Gate.adj U) (qs.eval U ψ) = ψ :=
  GateSemanticsCore.eval_adj_apply (qs := qs) U ψ

theorem eval_apply_adj
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
    qs.eval U (qs.eval (Gate.adj U) ψ) = ψ :=
  GateSemanticsCore.eval_apply_adj (qs := qs) U ψ

end QSemantics

/-- QFT-specific semantic facts. -/
class QFTSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs] : Type where

  eval_QFT_size0 :
    ∀ (r : ExtReg) (ψ : qs.State),
      r.width = 0 →
      qs.eval (Gate.QFT r) ψ = qs.eval Gate.id ψ

  eval_QFT_size1 :
    ∀ (r : ExtReg) (ψ : qs.State)
      (hsize : r.width = 1),
      qs.eval (Gate.QFT r) ψ =
        qs.eval (Gate.H (r.active.lowQubit (by
          simp [ExtReg.width] at hsize
          omega))) ψ

  eval_QFT_ket :
    ∀ (r : ExtReg) (b : qs.Basis),
      qs.eval (Gate.QFT r) (qs.ket b)
        =
      ((1 / Real.sqrt ((2^r.width : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (2^r.width),
          (qftPhase (2^r.width) (ExtReg.toNat r b) y.1) •
            qs.ket (RegEncoding.writeNat r.active y.1 b)

  eval_adj_QFT_ket :
    ∀ (r : ExtReg) (b : qs.Basis),
      qs.eval (Gate.adj (Gate.QFT r)) (qs.ket b)
        =
      ((1 / Real.sqrt ((ASize r.active : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (ASize r.active),
          star
              (qftPhase
                (ASize r.active)
                (ExtReg.toNat r b)
                y.1) •
            qs.ket (RegEncoding.writeNat r.active y.1 b)

class HadamardSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  eval_H_ket :
    ∀ (q : ℕ) (b : qs.Basis),
      qs.eval (Gate.H q) (qs.ket b)
        =
      ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (
          qs.ket (RegEncoding.writeNat (qubitReg q) 0 b)
          +
          (if RegEncoding.bit q b then (-1 : ℂ) else 1) •
            qs.ket (RegEncoding.writeNat (qubitReg q) 1 b)
        )

class PauliXSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  eval_X_ket :
    ∀ (q : ℕ) (b : qs.Basis),
      qs.eval (Gate.X q) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (qubitReg q)
          (if RegEncoding.bit q b then 0 else 1)
          b)

  eval_X_low_zero_reg_ket :
    ∀ (r : Reg) (b : qs.Basis),
      (hpos : 0 < regSize r) →
      RegEncoding.toNat r b = 0 →
      qs.eval (Gate.X (r.lowQubit hpos)) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat r 1 b)

class RegisterHadamardSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  eval_Hreg_ket :
    ∀ (r : Reg) (b : qs.Basis),
      ∃ α : Fin (ASize r) → ℂ,
        qs.eval
            ((regQubits r).foldl
              (fun acc q => Gate.seq (Gate.H q) acc)
              Gate.id)
            (qs.ket b)
          =
        ∑ t : Fin (ASize r),
          α t • qs.ket (RegEncoding.writeNat r t.1 b)

class RadixReverseSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs] : Type where

  eval_RadixReverse_ket :
    ∀ (r : Reg) (m : ℕ) (hm : m ≤ regSize r)
      (b : qs.Basis) (kL kH : ℕ),
      let sp : SplitPoint r := ⟨m, hm⟩
      let left  : Reg := splitLeft r sp
      let right : Reg := splitRight r sp
      kL < ASize left →
      kH < ASize right →
      qs.eval (Gate.RadixReverse r m)
        (qs.ket
          (RegEncoding.writeNat left kL
            (RegEncoding.writeNat right kH b)))
      =
      qs.ket
        (RegEncoding.writeNat r
          (radixReverseIndex r m hm kL kH)
          b)

/-- Signed phase-product semantic facts. -/
class PhaseSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs] : Type where

  eval_SignedPhaseProd_ket :
    ∀ (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b)
        =
      (Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ))))) •
        qs.ket b

  eval_CSignedPhaseProd_ket :
    ∀ (ctrl : ℕ) (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b)
        =
      if RegEncoding.bit ctrl b then
        (Complex.exp
          (phi * Complex.I *
            (((extToInt x b : ℤ) : ℂ) *
             (((extToInt z b : ℤ) : ℂ))))) •
          qs.ket b
      else
        qs.ket b

/-- Zero/sign extension and deallocation semantic facts. -/
class ExtensionSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs] : Type where

  eval_zeroExtend :
    ∀ (r : ExtReg) (n : ℕ) (ψ : qs.State),
      qs.eval (Gate.zeroExtend r n) ψ = ψ

  eval_zeroDealloc :
    ∀ (r : ExtReg) (n : ℕ) (ψ : qs.State),
      qs.eval (Gate.zeroDealloc r n) ψ = ψ

  eval_signExtend_ket :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
    r.CanGrow n → ExtReg.FreshFor r n b →
      ∃ b' : qs.Basis,
        qs.eval (Gate.signExtend r n) (qs.ket b) = qs.ket b'
        ∧
        ExtReg.toNat r b' = ExtReg.toNat r b
        ∧
        extToInt (r.grow n) b' = extToInt r b
        ∧
        (∀ e : ExtReg, ExtReg.ActiveDisjoint e (r.grow n) →
          ExtReg.toNat e b' = ExtReg.toNat e b)

  eval_signDealloc_eq_adj :
    ∀ r n ψ,
      qs.eval (Gate.signDealloc r n) ψ = qs.eval (Gate.adj (Gate.signExtend r n)) ψ

theorem ExtReg.toNat_grow_of_fresh
    (r : ExtReg)
    (n : ℕ)
    (b : Basis)
    (_hcap : r.CanGrow n)
    (hzero : r.FreshFor n b) :
    ExtReg.toNat (r.grow n) b =
      ExtReg.toNat r b := by
  exact Gate.ExtReg.toNat_grow_of_fresh r n b hzero

theorem eval_zeroExtend_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b : qs.Basis)
    (hcap : r.CanGrow n)
    (hzero : ExtReg.FreshFor r n b) :
    qs.eval
        (Gate.zeroExtend r n)
        (qs.ket b)
      =
    qs.ket b
    ∧
    ExtReg.toNat (r.grow n) b =
      ExtReg.toNat r b := by
  constructor
  · exact ExtensionSemantics.eval_zeroExtend r n (qs.ket b)
  · exact ExtReg.toNat_grow_of_fresh r n b hcap hzero

lemma zeroExtend_preserves_bit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (q : ℕ)
    (hEval :
      qs.eval (Gate.zeroExtend r n) (qs.ket b) =
        qs.ket b') :
    RegEncoding.bit q b' =
      RegEncoding.bit q b := by
  have hket :
      qs.ket b = qs.ket b' := by
    calc
      qs.ket b
          = qs.eval (Gate.zeroExtend r n) (qs.ket b) := by
              symm
              exact ExtensionSemantics.eval_zeroExtend
                r n (qs.ket b)
      _ = qs.ket b' := hEval

  have hb : b = b' := qs.ket_inj hket
  subst b'
  rfl

lemma signExtend_preserves_disjoint_extToInt
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r e : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (hcap : r.CanGrow n)
    (hfresh : r.FreshFor n b)
    (hdisj :
      ExtReg.ActiveDisjoint e (r.grow n))
    (heval :
      qs.eval (Gate.signExtend r n) (qs.ket b) =
        qs.ket b') :
    extToInt e b' = extToInt e b := by
  rcases ExtensionSemantics.eval_signExtend_ket
      r n b hcap hfresh with
    ⟨bout, heval', _hr, _hwide, hloc⟩

  have hbout : bout = b' := by
    apply qs.ket_inj
    rw [← heval, ← heval']

  subst bout

  unfold extToInt
  rw [hloc e hdisj]

lemma tcDecodeWidth_succ_eq_of_lt {w n : ℕ} (h : n < 2 ^ w) :
  tcDecodeWidth (w + 1) n = (n : ℤ) := by
  simp [tcDecodeWidth, h]

class ArithmeticSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  eval_ShiftL_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
    FitsSignedWidth r.width ((2 : ℤ) ^ n * extToInt r b) →
      ∃ b' : qs.Basis,
        qs.eval (Gate.ShiftL r n) (qs.ket b) = qs.ket b'
        ∧
        extToInt r b' = (2 : ℤ) ^ n * extToInt r b
        ∧
        (∀ e : ExtReg, ExtReg.ActiveDisjoint e r →
           extToInt e b' = extToInt e b)

  eval_ShiftR_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis) (q : ℤ),
    extToInt r b = (2 : ℤ) ^ n * q →
    FitsSignedWidth r.width q →
    ∃ b' : qs.Basis,
      qs.eval (Gate.ShiftR r n) (qs.ket b) = qs.ket b'
        ∧
      extToInt r b' = q
        ∧
      (∀ e : ExtReg,  ExtReg.ActiveDisjoint e r →
           extToInt e b' = extToInt e b)

  eval_Negate_ket_mod :
    ∀ (r : ExtReg) (b : qs.Basis),
    ∃ b' : qs.Basis,
      qs.eval (Gate.Negate r) (qs.ket b) = qs.ket b'
        ∧
      extToInt r b' = tcWrapInt r.width (- extToInt r b)
        ∧
      (∀ e : ExtReg,  ExtReg.ActiveDisjoint e r →
         extToInt e b' = extToInt e b)

  eval_AddScaled_ket_mod :
    ∀ (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) (b : qs.Basis),
    ExtReg.ActiveDisjoint dst src →
    ∃ b' : qs.Basis,
      qs.eval (Gate.AddScaled dst src negSrc sh) (qs.ket b) = qs.ket b'
        ∧
      extToInt dst b' = tcWrapInt dst.width (extToInt dst b + (if negSrc then (-1 : ℤ) else 1) * (2 : ℤ) ^ sh * extToInt src b)
        ∧
      extToInt src b' = extToInt src b
        ∧
      (∀ e : ExtReg,
          ExtReg.ActiveDisjoint e dst →
          ExtReg.ActiveDisjoint e src →
           extToInt e b' = extToInt e b)


/-- Bundled semantic interface for all gate families used in this file. -/
class GateSemanticsFacts
  (qs : QSemantics)
  [RegEncoding qs.Basis] :
  Type extends
    GateSemanticsCore qs,
    QFTSemantics qs,
    PhaseSemantics qs,
    ExtensionSemantics qs,
    ArithmeticSemantics qs,
    RadixReverseSemantics qs,
    HadamardSemantics qs,
    PauliXSemantics qs,
    RegisterHadamardSemantics qs where

  eval_Hreg_zero_eq_QFT :
    ∀ (r : ExtReg) (b : qs.Basis),
      ExtReg.toNat r b = 0 →
      qs.eval
          ((regQubits r.active).foldl
            (fun acc q => Gate.seq (Gate.H q) acc)
            Gate.id)
          (qs.ket b)
        =
      qs.eval (Gate.QFT r) (qs.ket b)

namespace GateSemanticsFacts

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [GateSemanticsFacts qs]

theorem eval_RadixReverse_split_ket
  (r : Reg) (m : ℕ) (hm : m ≤ regSize r) (b : qs.Basis)
  (kL kH : ℕ)
  (hkL : kL < ASize (splitLeft r ⟨m, hm⟩))
  (hkH : kH < ASize (splitRight r ⟨m, hm⟩)) :
  qs.eval (Gate.RadixReverse r m)
    (qs.ket
      (RegEncoding.writeNat (splitLeft r ⟨m, hm⟩) kL
        (RegEncoding.writeNat (splitRight r ⟨m, hm⟩) kH b)))
  =
  qs.ket
    (RegEncoding.writeNat r
      (radixReverseIndex r m hm kL kH)
      b) := by
  simpa [radixReverseIndex] using
    (RadixReverseSemantics.eval_RadixReverse_ket
      (qs := qs)
      (r := r) (m := m) (hm := hm) (b := b)
      (kL := kL) (kH := kH)
      hkL
      hkH)


private lemma zeroExtend_preserves_bit
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    (r : ExtReg)
    (n : ℕ)
    (b b' : qs.Basis)
    (q : ℕ)
    (hEval :
      qs.eval (Gate.zeroExtend r n) (qs.ket b) = qs.ket b') :
    RegEncoding.bit q b' = RegEncoding.bit q b := by
  classical
  exact Shor.zeroExtend_preserves_bit qs r n b b' q hEval

lemma eval_CSignedPhaseProd_ket_as_if_SignedPhaseProd
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [PhaseSemantics qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (b : qs.Basis) :
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) (qs.ket b)
      =
    if RegEncoding.bit ctrl b then
      qs.eval (Gate.SignedPhaseProd phi x z) (qs.ket b)
    else
      qs.ket b := by
  by_cases hctrl : RegEncoding.bit ctrl b
  ·
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_pos hctrl, if_pos hctrl]
    exact
      (PhaseSemantics.eval_SignedPhaseProd_ket
        (qs := qs) phi x z b).symm
  ·
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    rw [if_neg hctrl, if_neg hctrl]

open Gate
/--
Semantic bridge for the unsigned macro: on clean workspace, `PhaseProdUsing` contributes
exactly the expected phase `exp(i * phi * x * z)` and restores the basis state.
-/
theorem eval_PhaseProdUsing_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (phi : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (hclean : ws.Clean b) :
    qs.eval
        (Gate.PhaseProdUsing phi x z ws)
        (qs.ket b)
      =
    Complex.exp
        (phi * Complex.I *
          ((RegEncoding.toNat x b : ℂ) *
           (RegEncoding.toNat z b : ℂ))) •
      qs.ket b := by
  have hxFresh :
      ws.xExt.FreshFor 1 b :=
    hclean.1

  have hzFresh :
      ws.zExt.FreshFor 1 b :=
    hclean.2

  have hxInt :
      extToInt
          (ws.xExt.grow 1) b
        =
      (RegEncoding.toNat x b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.xExt)
        (n := 1)
        (b := b)
        ws.xExt_canGrow
        hxFresh
        (by omega))

  have hzInt :
      extToInt
          (ws.zExt.grow 1) b
        =
      (RegEncoding.toNat z b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.zExt)
        (n := 1)
        (b := b)
        ws.zExt_canGrow
        hzFresh
        (by omega))

  simp only [
    Gate.PhaseProdUsing,
    qs.eval_seq,
    ExtensionSemantics.eval_zeroExtend,
    ExtensionSemantics.eval_zeroDealloc
  ]

  rw [PhaseSemantics.eval_SignedPhaseProd_ket]
  rw [hxInt, hzInt]

  simp

/-- Controlled version of `eval_PhaseProdUsing_ket`; the phase appears only when `ctrl` is one. -/
theorem eval_CPhaseProdUsing_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : Reg)
    (ws : Gate.PhaseProdWorkspace x z)
    (b : qs.Basis)
    (hclean : ws.Clean b):
    qs.eval
        (Gate.CPhaseProdUsing ctrl phi x z ws)
        (qs.ket b)
      =
    (if RegEncoding.bit ctrl b then
        Complex.exp
          (phi * Complex.I *
            ((RegEncoding.toNat x b : ℂ) *
             (RegEncoding.toNat z b : ℂ)))
      else
        1) •
      qs.ket b := by
  have hxFresh :
      ws.xExt.FreshFor 1 b :=
    hclean.1

  have hzFresh :
      ws.zExt.FreshFor 1 b :=
    hclean.2

  have hxInt :
      extToInt
          (ws.xExt.grow 1) b
        =
      (RegEncoding.toNat x b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.xExt)
        (n := 1)
        (b := b)
        ws.xExt_canGrow
        hxFresh
        (by omega))

  have hzInt :
      extToInt
          (ws.zExt.grow 1) b
        =
      (RegEncoding.toNat z b : ℤ) := by
    simpa using
      (ExtReg.extToInt_grow_of_fresh
        (e := ws.zExt)
        (n := 1)
        (b := b)
        ws.zExt_canGrow
        hzFresh
        (by omega))

  simp only [Gate.CPhaseProdUsing, qs.eval_seq, ExtensionSemantics.eval_zeroExtend,ExtensionSemantics.eval_zeroDealloc]

  rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
  rw [hxInt, hzInt]

  by_cases hc : RegEncoding.bit ctrl b
  · simp [hc]
  · simp [hc]

end GateSemanticsFacts

/-! =========================================================
    Section 8: General algebraic lemmas for `eval`
========================================================= -/

lemma eval_sum
    {α : Type}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (s : Finset α)
    (f : α → qs.State) :
    qs.eval U (∑ a ∈ s, f a) = ∑ a ∈ s, qs.eval U (f a) := by
  classical
  refine Finset.induction_on s ?h0 ?hs
  · simp [QSemantics.eval_zero]
  · intro a s ha hs
    simp [Finset.sum_insert ha, QSemantics.eval_add, hs]

lemma eval_sum_univ
    {α : Type}
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Fintype α]
    (U : Gate)
    (f : α → qs.State) :
    qs.eval U (∑ a : α, f a) = ∑ a : α, qs.eval U (f a) := by
  have := (eval_sum qs U Finset.univ f)
  aesop

/-! =========================================================
    Section 9: Encoding transport lemmas
========================================================= -/

lemma toNat_left_write_right [QSemantics] [RegEncoding (QSemantics.Basis)]
  (left right : Reg) (h : Disjoint left right) (b : QSemantics.Basis) (yR : ℕ) :
  RegEncoding.toNat left (RegEncoding.writeNat right yR b)
    = RegEncoding.toNat left b := by
  simpa using
    (RegEncoding.toNat_left_write_right
      (left := left) (right := right) (Basis:=QSemantics.Basis) (b := b) (yR := yR) h)

/-! =========================================================
    Section 10: Norm, isometry, and overlap inequalities
========================================================= -/

/-- `eval U` is an isometry if it preserves inner products. -/
lemma eval_isometry
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
  (U : Gate)
  (hU : ∀ ψ φ : qs.State, inner ℂ (qs.eval U ψ) (qs.eval U φ) = inner ℂ ψ φ) :
  ∀ ψ φ : qs.State, ‖qs.eval U ψ - qs.eval U φ‖ = ‖ψ - φ‖ := by
  intro ψ φ
  have hnorm : ‖qs.eval U (ψ - φ)‖ = ‖ψ - φ‖ := by
    have : ‖qs.eval U (ψ - φ)‖ ^ 2 = ‖ψ - φ‖ ^ 2 := by
      simpa [sq] using congrArg Complex.re (hU (ψ - φ) (ψ - φ))
    aesop
  simpa [qs.hsub U ψ φ] using hnorm

@[simp] lemma eval_seq_simp
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs]
  (U V : Gate) (ψ : qs.State) :
  qs.eval (U ;; V) ψ = qs.eval V (qs.eval U ψ) := by
  simpa using (qs.eval_seq U V ψ)

lemma eval_norm_preserved
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    (U : Gate)
    (ψ : qs.State) :
  ‖qs.eval U ψ‖ = ‖ψ‖ := by
  have h := eval_isometry qs U (by intro ψ φ; simpa using qs.inner_preserved U ψ φ) ψ 0
  simpa [qs.eval_zero U] using h

lemma FreshZero.of_eq_on_bits
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (b₁ b₂ : Basis)
    (hbits :
      ∀ q : ℕ,
        q ∈ r.qubits →
        RegEncoding.bit q b₂ =
          RegEncoding.bit q b₁)
    (hzero : FreshZero r b₁) :
    FreshZero r b₂ := by
  unfold FreshZero at hzero ⊢

  apply Nat.zero_of_testBit_eq_false
  intro j

  by_cases hj : j < regSize r

  · let i : Fin (regSize r) :=
      ⟨j, hj⟩

    let q : ℕ :=
      r.get i

    have hq :
        q ∈ r.qubits := by
      dsimp [q, i, Reg.get]
      exact List.get_mem r.qubits _

    calc
      Nat.testBit
          (RegEncoding.toNat r b₂)
          j
          =
        RegEncoding.bit q b₂ := by
          symm
          simpa [q, i] using
            RegEncoding.bit_eq_testBit_toNat
              r b₂ i

      _ =
        RegEncoding.bit q b₁ :=
          hbits q hq

      _ =
        Nat.testBit
          (RegEncoding.toNat r b₁)
          j := by
            simpa [q, i] using
              RegEncoding.bit_eq_testBit_toNat
                r b₁ i

      _ = false := by
        rw [hzero]
        simp

  · have hwidth :
        regSize r ≤ j :=
      Nat.le_of_not_gt hj

    have hToNat :
        RegEncoding.toNat r b₂
          <
        2 ^ regSize r := by
      simpa [ASize] using
        RegEncoding.toNat_lt_ASize
          (r := r)
          (b := b₂)

    have hpow :
        2 ^ regSize r ≤ 2 ^ j := by
      exact
        Nat.pow_le_pow_right
          (by omega)
          hwidth

    exact
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hToNat hpow)

/-! =========================================================
    Section 7: Generic basis-clean linear closure

    Many workspace "clean-state" predicates are the same construction:
    the linear subspace spanned by basis vectors satisfying some
    per-basis cleanliness predicate `P`. `CleanClosure P` captures it
    once; the specific clean-state families are `CleanClosure` at a
    particular `P` (see the `abbrev`s at each use site).
========================================================= -/

/-- The set of states reachable from `P`-clean basis kets by `+` and `•`:
    a `zero/ket/add/smul` linear closure parameterized by the per-basis
    predicate `P`. -/
inductive CleanClosure {qs : QSemantics} [RegEncoding qs.Basis]
    (P : qs.Basis → Prop) : qs.State → Prop
  | zero : CleanClosure P 0
  | ket (b : qs.Basis) (h : P b) : CleanClosure P (qs.ket b)
  | add {ψ φ : qs.State} (hψ : CleanClosure P ψ) (hφ : CleanClosure P φ) :
      CleanClosure P (ψ + φ)
  | smul (a : ℂ) {ψ : qs.State} (hψ : CleanClosure P ψ) :
      CleanClosure P (a • ψ)



end Shor
