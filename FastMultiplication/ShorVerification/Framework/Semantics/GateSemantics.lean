import FastMultiplication.ShorVerification.Framework.Quantum.QSemantics
import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — gate-evaluation semantics

The classes that give semantic meaning to the `Gate` language on top of the
quantum state space: `GateSemanticsCore`, the per-gate semantic classes, and
`GateSemanticsFacts`, plus the generic `eval` lemmas and clean-closure.
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

open QSemantics

attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

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
        (RegEncoding.writeNat (qubitReg q)
          (if RegEncoding.bit q b then 0 else 1) b)

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

end Shor
