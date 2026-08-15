import FastMultiplication.ShorVerification.Framework.Quantum.QSemantics
import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Shor verification core — gate-evaluation semantics

The classes and definitions that give semantic meaning to the `Gate` language
on top of the quantum state space: `GateSemanticsCore`, the per-gate semantic
classes, and the bundled `GateSemanticsFacts` interface.
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

open QSemantics

attribute [instance] QSemantics.instNormed
attribute [instance] QSemantics.instIP

/-! =========================================================
    Gate-specific semantic interfaces
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

  /-- Evaluate a structured gate on a quantum state. -/
  eval  : Gate → qs.State → qs.State

  -- Structural laws. In `U ;; V`, `U` runs before `V`.
  eval_id  : ∀ ψ, eval Gate.id ψ = ψ
  eval_seq : ∀ U V ψ, eval (U ;; V) ψ = eval V (eval U ψ)

  -- Gate evaluation is isometric and complex-linear.
  inner_preserved :
    ∀ U ψ φ, inner ℂ (eval U ψ) (eval U φ) = inner ℂ ψ φ

  eval_add  : ∀ U ψ φ, eval U (ψ + φ) = eval U ψ + eval U φ
  eval_smul : ∀ U (a : ℂ) ψ, eval U (a • ψ) = a • eval U ψ

  -- A gate followed by its adjoint returns the original state.
  eval_adj_apply :
    ∀ (U : Gate) (ψ : qs.State),
      eval (Gate.adj U) (eval U ψ) = ψ

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

  eval_QFT_ket :
    ∀ (r : ExtReg) (b : qs.Basis),
      qs.eval (Gate.QFT r) (qs.ket b)
        =
      ((1 / Real.sqrt ((2^r.width : ℕ) : ℝ) : ℂ)) •
        ∑ y : Fin (2^r.width),
          (qftPhase (2^r.width) (ExtReg.toNat r b) y.1) •
            qs.ket (RegEncoding.writeNat r.active y.1 b)

/-- Hadamard-gate behavior on computational-basis kets. -/
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

/-- Pauli-X behavior on computational-basis kets. -/
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

/-- Semantics of recombining two logical register blocks in the opposite order. -/
class RadixReverseSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs] : Type where

  eval_RadixReverse_ket :
    ∀ (r : Reg) (m : ℕ) (hm : m ≤ Reg.width r)
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

/-- Zero/sign extension and deallocation semantic facts.

Zero extension and deallocation change only the logical register view and hence
act as identity on the state. Sign extension writes the activated reserve bits
so that the decoded signed value is preserved. -/
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

/-- Signed arithmetic behavior on computational-basis kets.

The `_exact` shifts require representability or exact divisibility. The `_mod`
operations wrap to the destination width. Each law also records that disjoint
registers retain their previous values. -/
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
    PauliXSemantics qs

/-! ### Reference modular-multiplication semantics

The remaining declarations describe the ideal gates, layouts, and opaque
primitive tags used by the repository's reference modular-multiplication
construction. They are not required to understand the generic gate evaluator.
-/

/-- Ideal modular multiplication specifications used by the correctness layer. -/
class Spec where
  idealModMul     : (c N : ℕ) → (x : Reg) → Gate
  idealCtrlModMul : (c N : ℕ) → (x : Reg) → (ctrl : ℕ) → Gate

/-- `q` is not a qubit of register `r`. -/
def QubitOutside (q : ℕ) (r : Reg) : Prop :=
  q ∉ r.qubits

/--
Layout assumptions for one invocation of the reference in-place controlled
modular-multiplication core.

`data.grow 1` is used because the construction temporarily activates one
reserve bit of `data` as its carry/high bit.
-/
def ModMulCoreLayout
    (data work : ExtReg)
    (flag ctrl : ℕ) :
    Prop :=
  ExtReg.OwnedDisjoint data work ∧
  flag ∉ data.ownedQubits ∧
  flag ∉ work.ownedQubits ∧
  ctrl ∉ data.ownedQubits ∧
  ctrl ∉ work.ownedQubits ∧
  ctrl ≠ flag

/--
A computational-basis input accepted by the reference modular-multiplication core.

The data register contains a canonical residue; the two data reserve bits,
the fractional/work register, and the comparator flag are clean.
All other qubits, including the control and exponent registers, are arbitrary.
-/
def GoodModMulBasisInput
    (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data work : ExtReg) (flag : ℕ)
    (b : qs.Basis) : Prop :=
  RegEncoding.toNat data.active b < N ∧
  data.FreshFor 2 b ∧
  RegEncoding.toNat work.active b = 0 ∧
  work.FreshFor 1 b ∧
  RegEncoding.toNat (qubitReg flag) b = 0

/-- Exact basis semantics required of the ideal controlled modular multiplier. -/
class IdealCtrlModMulExactSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [Spec] : Prop where

  eval_idealCtrlModMul_good_ket_exact :
    ∀ (c N : ℕ) (data work : ExtReg) (flag ctrl : ℕ) (b : qs.Basis),
      1 < N →
      N ≤ ASize data.active →
      Nat.Coprime c N →
      ModMulCoreLayout data work flag ctrl →
      GoodModMulBasisInput qs N data work flag b →
      qs.eval (Spec.idealCtrlModMul c N data.active ctrl) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat data.active
          (if RegEncoding.bit ctrl b then
            (c * RegEncoding.toNat data.active b) % N
          else
            RegEncoding.toNat data.active b)
          b)

/--
Semantic facts for the opaque arithmetic primitives used by the reference
modular-multiplication implementation.
-/
class ModMulPrimitiveGateSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  /--
  `CMP_GE_CONST` reversibly XORs the comparison `N ≤ x` into `flag`.
  -/
  eval_cmp_ge_const_ket :
    ∀ (N : ℕ) (data : Reg) (flag : ℕ) (b : qs.Basis),
      flag ∉ data.qubits →
      qs.eval
          (Gate.Prim "CMP_GE_CONST" ([N, flag] ++ data.qubits))
          (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (qubitReg flag)
          (if RegEncoding.bit flag b then
            if N ≤ RegEncoding.toNat data b then 0 else 1
          else
            if N ≤ RegEncoding.toNat data b then 1 else 0)
          b)

  /--
  `CSUB_CONST` subtracts `N` modulo the width of `data` when `flag = 1`.
  -/
  eval_csub_const_ket :
    ∀ (N : ℕ) (data : Reg) (flag : ℕ) (b : qs.Basis),
      flag ∉ data.qubits →
      qs.eval
          (Gate.Prim "CSUB_CONST" ([N, flag] ++ data.qubits))
          (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat data
          (if RegEncoding.bit flag b then
            (RegEncoding.toNat data b
                + ASize data
                - (N % ASize data)) % ASize data
          else
            RegEncoding.toNat data b)
          b)

  /--
  `CMP_LT_NW` reversibly XORs the comparison

      x * 2^|work| < N * work

  into `flag`.
  -/
  eval_cmp_lt_nw_ket :
    ∀ (N : ℕ) (data work : Reg) (flag : ℕ) (b : qs.Basis),
      flag ∉ data.qubits →
      flag ∉ work.qubits →
      qs.eval
          (Gate.Prim "CMP_LT_NW"
            ([N, flag] ++ data.qubits ++ work.qubits))
          (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (qubitReg flag)
          (if RegEncoding.bit flag b then
            if RegEncoding.toNat data b * ASize work
                < N * RegEncoding.toNat work b then
              0
            else
              1
          else
            if RegEncoding.toNat data b * ASize work
                < N * RegEncoding.toNat work b then
              1
            else
              0)
          b)
end Shor
