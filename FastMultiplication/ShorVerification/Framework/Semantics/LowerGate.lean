import FastMultiplication.ShorVerification.Framework.AbstractMachine.LowGate
import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics

namespace Shor

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

  evalL_shiftL_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      evalL (LowGate.ShiftL r n) (qs.ket b) =
        qs.ket (shiftLBasis r n b)

  evalL_shiftR_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      evalL (LowGate.ShiftR r n) (qs.ket b) =
        qs.ket (shiftRBasis r n b)

  evalL_negate_ket_total :
    ∀ (r : ExtReg) (b : qs.Basis),
      evalL (LowGate.Negate r) (qs.ket b) =
        qs.ket (negateBasis r b)

  evalL_addScaled_ket_total :
    ∀ (dst src : ExtReg)
      (negSrc : Bool) (sh : ℕ) (b : qs.Basis),
      evalL
          (LowGate.AddScaled dst src negSrc sh)
          (qs.ket b)
        =
      qs.ket (addScaledBasis dst src negSrc sh b)

  evalL_Phase_ket :
    ∀ q θ b,
      evalL (LowGate.Phase q θ) (qs.ket b) =
        (if RegEncoding.bit q b then
          Complex.exp (θ * Complex.I) • qs.ket b
        else
          qs.ket b)

  evalL_CNOT_ket :
    ∀ ctrl target b,
      evalL (LowGate.CNOT ctrl target) (qs.ket b) =
        qs.ket (cnotBasis ctrl target b)

  evalL_Toffoli_ket :
    ∀ c₁ c₂ target b,
      evalL (LowGate.Toffoli c₁ c₂ target) (qs.ket b) =
        qs.ket (toffoliBasis c₁ c₂ target b)

  evalL_zeroExtend_id :
    ∀ r n ψ,
      evalL (LowGate.zeroExtend r n) ψ = ψ

  evalL_signExtend_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      evalL (LowGate.signExtend r n) (qs.ket b) =
        qs.ket (signExtendBasis r n b)

  evalL_zeroDealloc_id :
    ∀ r n ψ,
      evalL (LowGate.zeroDealloc r n) ψ = ψ

  evalL_signDealloc_ket_total :
    ∀ (r : ExtReg) (n : ℕ) (b : qs.Basis),
      evalL (LowGate.signDealloc r n) (qs.ket b) =
        qs.ket (signDeallocBasis r n b)

  evalL_radixReverse_ket_total :
    ∀ (r : Reg) (m : ℕ) (b : qs.Basis),
      evalL (LowGate.RadixReverse r m) (qs.ket b) =
        qs.ket (radixReverseBasis r m b)

  evalL_adj_apply :
    ∀ (L : LowGate) (ψ : qs.State),
      evalL (LowGate.adj L) (evalL L ψ) = ψ

namespace LowerGateClass

@[simp] theorem evalL_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (L : LowGate) :
    LowerGateClass.evalL (qs := qs) L 0 = 0 := by
  simpa using
    (LowerGateClass.evalL_smul
      (qs := qs) L (0 : ℂ) (0 : qs.State))

end LowerGateClass

end Shor
