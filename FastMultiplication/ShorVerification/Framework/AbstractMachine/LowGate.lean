import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics

namespace Shor

/-!
# Low-Level Gate Language

This file contains the abstract target language for lowering.  It is separated
from the phase-product correctness development so the abstract-machine layer
owns only the low-level syntax and the recursive translation machinery.
-/

/-! =========================================================
    Section 1: Low-level target syntax

    `LowGate` mirrors primitive high-level gates and includes explicit nodes
    for allocation, deallocation, phase-product fallbacks, and radix reversal.
========================================================= -/

/-- Low-level target gate language for lowering. -/
inductive LowGate : Type
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  | H : ℕ → LowGate
  | X : ℕ → LowGate
  | Prim : String → List ℕ → LowGate
  | ShiftL    : (r : ExtReg) → (n : ℕ) → LowGate
  | ShiftR    : (r : ExtReg) → (n : ℕ) → LowGate
  | Negate    : (r : ExtReg) → LowGate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : ℕ) → LowGate
  | Naive_SignedPhaseProd : (phi : Real) → (x z : ExtReg) → LowGate
  | Naive_CSignedPhaseProd : (ctrl : ℕ) → (phi : Real) → (x z : ExtReg) → LowGate
  | zeroExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | signExtend : (r : ExtReg) → (n : ℕ) → LowGate
  | zeroDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  | signDealloc : (r : ExtReg) → (n : ℕ) → LowGate
  | RadixReverse : (r : Reg) → (m : ℕ) → LowGate
deriving Inhabited

namespace LowGate

/-- Sequential composition notation for low gates. -/
infixr:80 " ;; " => LowGate.seq

/-- Adjoint notation for low gates. -/
prefix:90 "†" => LowGate.adj

end LowGate

/-! =========================================================
    Section 2: Low-level semantic interface
    `LowerGateClass` is the semantic interface for lowered gates. It is stated
    directly over the low-level evaluator and basis-ket behavior; comparison
    with the internal high-level `Gate` evaluator is kept in bridge lemmas below.
========================================================= -/

/-- Semantic interface for interpreting low-level gates in a quantum semantics. -/
class LowerGateClass
    (qs : QSemantics)
    [RegEncoding qs.Basis] : Type where
  evalL : LowGate → qs.State → qs.State

  evalL_id : ∀ ψ, evalL LowGate.id ψ = ψ

  evalL_seq : ∀ (U V : LowGate) (ψ : qs.State), evalL (U ;; V) ψ = evalL V (evalL U ψ)

  evalL_zero : ∀ (L : LowGate), evalL L 0 = 0

  evalL_add :
    ∀ (L : LowGate) (ψ φ : qs.State),
      evalL L (ψ + φ) = evalL L ψ + evalL L φ

  evalL_smul :
    ∀ (L : LowGate) (a : ℂ) (ψ : qs.State),
      evalL L (a • ψ) = a • evalL L ψ

  evalL_H_ket :
    ∀ (q : ℕ) (b : qs.Basis),
      evalL (LowGate.H q) (qs.ket b)
        =
      ((1 / Real.sqrt (2 : ℝ) : ℂ)) •
        (
          qs.ket (RegEncoding.writeNat (qubitReg q) 0 b)
          +
          (if RegEncoding.bit q b then (-1 : ℂ) else 1) •
            qs.ket (RegEncoding.writeNat (qubitReg q) 1 b)
        )

  evalL_X_ket :
    ∀ (q : ℕ) (b : qs.Basis),
      evalL (LowGate.X q) (qs.ket b)
        =
      qs.ket
        (RegEncoding.writeNat
          (qubitReg q)
          (if RegEncoding.bit q b then 0 else 1)
          b)

  evalL_shiftL_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
    FitsSignedWidth r.width ((2 : ℤ) ^ n * extToInt r b) →
      ∃ b' : qs.Basis,
        evalL (LowGate.ShiftL r n) (qs.ket b) = qs.ket b'
        ∧
        extToInt r b' = (2 : ℤ) ^ n * extToInt r b
        ∧
        (∀ e : ExtReg, ExtReg.ActiveDisjoint e r →
           extToInt e b' = extToInt e b)

  evalL_shiftR_ket_exact :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis) (q : ℤ),
    extToInt r b = (2 : ℤ) ^ n * q →
    FitsSignedWidth r.width q →
    ∃ b' : qs.Basis,
      evalL (LowGate.ShiftR r n) (qs.ket b) = qs.ket b'
        ∧
      extToInt r b' = q
        ∧
      (∀ e : ExtReg, ExtReg.ActiveDisjoint e r →
           extToInt e b' = extToInt e b)

  evalL_negate_ket_mod :
    ∀ (r : ExtReg) (b : qs.Basis),
    ∃ b' : qs.Basis,
      evalL (LowGate.Negate r) (qs.ket b) = qs.ket b'
        ∧
      extToInt r b' = tcWrapInt r.width (- extToInt r b)
        ∧
      (∀ e : ExtReg, ExtReg.ActiveDisjoint e r →
         extToInt e b' = extToInt e b)

  evalL_addScaled_ket_mod :
    ∀ (dst src : ExtReg) (negSrc : Bool) (sh : ℕ) (b : qs.Basis),
    ExtReg.ActiveDisjoint dst src →
    ∃ b' : qs.Basis,
      evalL (LowGate.AddScaled dst src negSrc sh) (qs.ket b) = qs.ket b'
        ∧
      extToInt dst b' =
        tcWrapInt dst.width
          (extToInt dst b
            + (if negSrc then (-1 : ℤ) else 1) * (2 : ℤ) ^ sh * extToInt src b)
        ∧
      extToInt src b' = extToInt src b
        ∧
      (∀ e : ExtReg,
          ExtReg.ActiveDisjoint e dst →
          ExtReg.ActiveDisjoint e src →
           extToInt e b' = extToInt e b)

  evalL_naive_signedPhaseProd_ket :
    ∀ (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      evalL (LowGate.Naive_SignedPhaseProd phi x z) (qs.ket b)
        =
      (Complex.exp
        (phi * Complex.I *
          (((extToInt x b : ℤ) : ℂ) *
           (((extToInt z b : ℤ) : ℂ))))) •
        qs.ket b

  evalL_naive_csignedPhaseProd_ket :
    ∀ (ctrl : ℕ) (phi : ℝ) (x z : ExtReg) (b : qs.Basis),
      evalL (LowGate.Naive_CSignedPhaseProd ctrl phi x z) (qs.ket b)
        =
      if RegEncoding.bit ctrl b then
        (Complex.exp
          (phi * Complex.I *
            (((extToInt x b : ℤ) : ℂ) *
             (((extToInt z b : ℤ) : ℂ))))) •
          qs.ket b
      else
        qs.ket b

  evalL_zeroExtend_id : ∀ r n ψ, evalL (LowGate.zeroExtend r n) ψ = ψ

  evalL_signExtend_ket :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
    r.CanGrow n → ExtReg.FreshFor r n b →
      ∃ b' : qs.Basis,
        evalL (LowGate.signExtend r n) (qs.ket b) = qs.ket b'
        ∧
        ExtReg.toNat r b' = ExtReg.toNat r b
        ∧
        extToInt (r.grow n) b' = extToInt r b
        ∧
        (∀ e : ExtReg, ExtReg.ActiveDisjoint e (r.grow n) →
          ExtReg.toNat e b' = ExtReg.toNat e b)

  evalL_zeroDealloc_id : ∀ r n ψ, evalL (LowGate.zeroDealloc r n) ψ = ψ

  evalL_signDealloc_eq_adj :
    ∀ r n ψ,
      evalL (LowGate.signDealloc r n) ψ =
        evalL (LowGate.adj (LowGate.signExtend r n)) ψ

  evalL_radixReverse_ket :
    ∀ (r : Reg) (m : ℕ) (hm : m ≤ regSize r)
      (b : qs.Basis) (kL kH : ℕ),
      let sp : SplitPoint r := ⟨m, hm⟩
      let left  : Reg := splitLeft r sp
      let right : Reg := splitRight r sp
      kL < ASize left →
      kH < ASize right →
      evalL (LowGate.RadixReverse r m)
        (qs.ket
          (RegEncoding.writeNat left kL
            (RegEncoding.writeNat right kH b)))
      =
      qs.ket
        (RegEncoding.writeNat r
          (radixReverseIndex r m hm kL kH)
          b)

  evalL_adj_apply :
    ∀ (L : LowGate) (ψ : qs.State),
      evalL (LowGate.adj L) (evalL L ψ) = ψ

/--
Opaque primitive tags have no independent mathematical specification in the
current framework, so their agreement with the internal `Gate.Prim` evaluator is
kept as an explicit bridge assumption rather than part of `LowerGateClass`.
-/
class LowerGatePrimitiveBridge
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs] : Prop where
  evalL_Prim :
    ∀ (tag : String) (args : List ℕ) (ψ : qs.State),
      LowerGateClass.evalL (qs := qs) (LowGate.Prim tag args) ψ =
        qs.eval (Gate.Prim tag args) ψ

/--
For low-level constructors whose high-level `Gate` semantics is currently only
specified operationally, this class carries the comparison to the internal proof
IR. As the high-level semantics is made more concrete, fields should migrate
from here to derivable bridge lemmas like `evalL_H`.
-/
class LowerGateGateBridge
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs] : Prop extends LowerGatePrimitiveBridge qs where
  evalL_shiftL : ∀ r n ψ,
    LowerGateClass.evalL (qs := qs) (LowGate.ShiftL r n) ψ =
      qs.eval (Gate.ShiftL r n) ψ
  evalL_shiftR : ∀ r n ψ,
    LowerGateClass.evalL (qs := qs) (LowGate.ShiftR r n) ψ =
      qs.eval (Gate.ShiftR r n) ψ
  evalL_negate : ∀ r ψ,
    LowerGateClass.evalL (qs := qs) (LowGate.Negate r) ψ =
      qs.eval (Gate.Negate r) ψ
  evalL_addScaled : ∀ dst src negSrc shift ψ,
    LowerGateClass.evalL (qs := qs) (LowGate.AddScaled dst src negSrc shift) ψ =
      qs.eval (Gate.AddScaled dst src negSrc shift) ψ
  evalL_signExtend : ∀ r n ψ,
    LowerGateClass.evalL (qs := qs) (LowGate.signExtend r n) ψ =
      qs.eval (Gate.signExtend r n) ψ
  evalL_signDealloc : ∀ r n ψ,
    LowerGateClass.evalL (qs := qs) (LowGate.signDealloc r n) ψ =
      qs.eval (Gate.signDealloc r n) ψ
  evalL_radixReverse : ∀ r m ψ,
    LowerGateClass.evalL (qs := qs) (LowGate.RadixReverse r m) ψ =
      qs.eval (Gate.RadixReverse r m) ψ



end Shor
