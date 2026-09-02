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

  eval  : Gate → qs.State → qs.State

  eval_id  : ∀ ψ, eval Gate.id ψ = ψ
  eval_seq : ∀ U V ψ, eval (U ;; V) ψ = eval V (eval U ψ)

  inner_preserved :
    ∀ U ψ φ, inner ℂ (eval U ψ) (eval U φ) = inner ℂ ψ φ

  eval_add  : ∀ U ψ φ, eval U (ψ + φ) = eval U ψ + eval U φ
  eval_smul : ∀ U (a : ℂ) ψ, eval U (a • ψ) = a • eval U ψ

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

def radixReverseBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg)
    (m : ℕ)
    (b : Basis) : Basis :=
  if hm : m ≤ regSize r then
    let sp : SplitPoint r := ⟨m, hm⟩
    let left := splitLeft r sp
    let right := splitRight r sp
    RegEncoding.writeNat r
      (radixReverseIndex r m hm
        (RegEncoding.toNat left b)
        (RegEncoding.toNat right b))
      b
  else
    b

class RadixReverseSemantics
  (qs : QSemantics)
  [RegEncoding qs.Basis]
  [GateSemanticsCore qs] : Type where

  eval_RadixReverse_ket_total :
    ∀ (r : Reg) (m : ℕ) (b : qs.Basis),
      qs.eval (Gate.RadixReverse r m) (qs.ket b)
        =
      qs.ket (radixReverseBasis r m b)
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

/-! =========================================================
    Canonical total basis action for sign extension
========================================================= -/

/--
The value written to the newly activated bits by sign extension.

If the active value is negative, complement all newly activated bits.
Otherwise leave them unchanged.

This is total and reversible.  On fresh-zero reserve it produces exactly
the usual two's-complement sign-extension bits.
-/
def signExtendNewValue
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) : ℕ :=
  let hi := RegEncoding.toNat (r.newBits n) b
  if extToInt r b < 0 then
    ASize (r.newBits n) - 1 - hi
  else
    hi


def signExtendBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) : Basis :=
  RegEncoding.writeNat
    (r.newBits n)
    (signExtendNewValue r n b)
    b


/--
Sign deallocation is the inverse of sign extension.

The canonical sign-extension basis map is an involution, so the same basis
map represents its inverse.
-/
def signDeallocBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) : Basis :=
  signExtendBasis r n b

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

  eval_signExtend_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      qs.eval (Gate.signExtend r n) (qs.ket b)
        =
      qs.ket (signExtendBasis r n b)

  eval_signDealloc_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      qs.eval (Gate.signDealloc r n) (qs.ket b)
        =
      qs.ket (signDeallocBasis r n b)
/--
A reversible total completion of signed left shift.

For `n < w`, the upper `n` input bits are not discarded.  Instead their
difference from the sign-extension pattern is stored in the low `n` output
bits.  On inputs for which signed left shift does not overflow, those low
bits are all zero, so this agrees with ordinary signed left shift.

For `n ≥ w` we use the identity on the `w`-bit word.
-/
def signedShiftLWord (w n u : ℕ) : ℕ :=
  if _h : n < w then
    let k := w - n
    let kept := u % (2 ^ k)
    let dropped := u / (2 ^ k)
    let sign := Nat.testBit u (k - 1)
    let mask := if sign then 2 ^ n - 1 else 0
    Nat.xor dropped mask + 2 ^ n * kept
  else
    u % (2 ^ w)

/--
Inverse reversible completion of `signedShiftLWord`.
-/
def signedShiftRWord (w n u : ℕ) : ℕ :=
  if _h : n < w then
    let k := w - n
    let kept := u / (2 ^ n)
    let syndrome := u % (2 ^ n)
    let sign := Nat.testBit u (w - 1)
    let mask := if sign then 2 ^ n - 1 else 0
    kept + 2 ^ k * Nat.xor syndrome mask
  else
    u % (2 ^ w)

def shiftLBasisRaw
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) : Basis :=
  RegEncoding.writeNat
    r.active
    (signedShiftLWord r.width n (ExtReg.toNat r b))
    b


def shiftRBasisRaw
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) : Basis :=
  RegEncoding.writeNat
    r.active
    (signedShiftRWord r.width n (ExtReg.toNat r b))
    b

noncomputable def shiftLBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) : Basis := by
  classical
  let z : ℤ := (2 : ℤ) ^ n * extToInt r b
  exact
    if h : FitsSignedWidth r.width z then
      RegEncoding.writeNat
        r.active
        (tcModWidth r.width z)
        b
    else
      shiftLBasisRaw r n b

noncomputable def shiftRBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (n : ℕ)
    (b : Basis) : Basis := by
  classical
  exact
    if h :
        ∃ q : ℤ,
          extToInt r b = (2 : ℤ) ^ n * q ∧
          FitsSignedWidth r.width q
    then
      RegEncoding.writeNat
        r.active
        (tcModWidth r.width (Classical.choose h))
        b
    else
      shiftRBasisRaw r n b

def negateBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (r : ExtReg)
    (b : Basis) : Basis :=
  RegEncoding.writeNat r.active (tcModWidth r.width (- extToInt r b)) b


noncomputable def addScaledBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : Basis) : Basis := by
  classical
  exact
    if _h : ExtReg.ActiveDisjoint dst src then
      RegEncoding.writeNat
        dst.active
        (tcModWidth dst.width
          (extToInt dst b
            + (if negSrc then (-1 : ℤ) else 1)
                * (2 : ℤ) ^ sh
                * extToInt src b)) b
    else
      b

class ArithmeticSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  eval_ShiftL_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      qs.eval (Gate.ShiftL r n) (qs.ket b)
        =
      qs.ket (shiftLBasis r n b)

  eval_ShiftR_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      qs.eval (Gate.ShiftR r n) (qs.ket b)
        =
      qs.ket (shiftRBasis r n b)

  eval_Negate_ket_total :
    ∀ (r : ExtReg) (b : qs.Basis),
      qs.eval (Gate.Negate r) (qs.ket b)
        =
      qs.ket (negateBasis r b)

  eval_AddScaled_ket_total :
    ∀ (dst src : ExtReg)
      (negSrc : Bool)
      (sh : ℕ)
      (b : qs.Basis),
      qs.eval
          (Gate.AddScaled dst src negSrc sh)
          (qs.ket b)
        =
      qs.ket
        (addScaledBasis dst src negSrc sh b)

def cnotBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (ctrl target : ℕ)
    (b : Basis) : Basis :=
  if ctrl = target then b
  else if RegEncoding.bit ctrl b then
    RegEncoding.writeNat (qubitReg target)
      (if RegEncoding.bit target b then 0 else 1) b
  else b

def toffoliBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (c₁ c₂ target : ℕ)
    (b : Basis) : Basis :=
  if c₁ = c₂ ∨ c₁ = target ∨ c₂ = target then b
  else if RegEncoding.bit c₁ b ∧ RegEncoding.bit c₂ b then
    RegEncoding.writeNat (qubitReg target)
      (if RegEncoding.bit target b then 0 else 1) b
  else b

class ClassicalReversibleSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  eval_CNOT_ket :
    ∀ (ctrl target : ℕ) (b : qs.Basis),
      qs.eval (Gate.CNOT ctrl target) (qs.ket b) =
        qs.ket (cnotBasis ctrl target b)

  eval_Toffoli_ket :
    ∀ (c₁ c₂ target : ℕ) (b : qs.Basis),
      qs.eval (Gate.Toffoli c₁ c₂ target) (qs.ket b) =
        qs.ket (toffoliBasis c₁ c₂ target b)

def cmpGeConstBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (N : ℕ)
    (data : Reg)
    (flag : ℕ)
    (b : Basis) : Basis :=
  if flag ∈ data.qubits then b
  else RegEncoding.writeNat (qubitReg flag)
      (if RegEncoding.bit flag b then
        if N ≤ RegEncoding.toNat data b then 0 else 1
      else if N ≤ RegEncoding.toNat data b then 1 else 0) b

def csubConstBasis
    {Basis : Type u}
    [RegEncoding Basis]
    (N : ℕ)
    (data : Reg)
    (flag : ℕ)
    (b : Basis) : Basis :=
  if flag ∈ data.qubits then b
  else RegEncoding.writeNat data
      (if RegEncoding.bit flag b then
        (RegEncoding.toNat data b + ASize data - (N % ASize data)) % ASize data
      else RegEncoding.toNat data b) b

class ModularArithmeticSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs] : Type where

  eval_CmpGeConst_ket :
    ∀ (N : ℕ) (data scratch : ExtReg) (flag : ℕ) (b : qs.Basis),
      qs.eval (Gate.CmpGeConst N data scratch flag) (qs.ket b) =
        qs.ket (cmpGeConstBasis N data.active flag b)

  eval_CSubConst_ket :
    ∀ (N : ℕ) (data scratch : ExtReg) (flag : ℕ) (b : qs.Basis),
      qs.eval (Gate.CSubConst N data scratch flag) (qs.ket b) =
        qs.ket (csubConstBasis N data.active flag b)

/-- Exact basis semantics required of the ideal controlled modular multiplier. -/
class IdealCtrlModMulExactSemantics
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]: Prop where

  eval_idealCtrlModMul_ket_exact :
    ∀ (c N : ℕ) (data : Reg) (ctrl : ℕ) (b : qs.Basis),
      1 < N → N ≤ ASize data → Nat.Coprime c N → ctrl ∉ data.qubits →
      RegEncoding.toNat data b < N →
      qs.eval (Gate.idealCtrlModMul c N data ctrl) (qs.ket b)
        =
      qs.ket (RegEncoding.writeNat data
          (if RegEncoding.bit ctrl b then (c * RegEncoding.toNat data b) % N
          else RegEncoding.toNat data b) b)


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
      ModularArithmeticSemantics qs,
      RadixReverseSemantics qs,
      HadamardSemantics qs,
      PauliXSemantics qs,
      ClassicalReversibleSemantics qs,
      IdealCtrlModMulExactSemantics qs

/-- `q` is not a qubit of register `r`. -/
def QubitOutside (q : ℕ) (r : Reg) : Prop :=
  q ∉ r.qubits

/--
Layout assumptions for one invocation of `CmodMulInPlaceCore`.

`data.grow 1` is used because Algorithm 1 temporarily activates one reserve
bit of `data` as its carry/high bit.
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
A computational-basis input on which Algorithm 1 is allowed to be called.

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


end Shor
