import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Registers
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.States
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.GateLaws

/-!
# `LowerGateClass.evalL` on each primitive, and the `Gate` bridge

Derived laws of `Framework/Semantics/LowGateSemantics.lean`: the zero/algebra
consequences of `LowerGateClass.evalL`'s primitive laws (`LowerGateClass`),
and the `evalL` correctness lemmas for the unsigned macro gates that are
implemented in terms of the signed primitives (`LowerGateGateBridge`).
-/

universe u

namespace Shor

variable {Basis : Type u} [RegEncoding Basis]

open QSemantics

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


theorem evalL_eq_eval_of_ket_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    (L : LowGate)
    (G : Gate)
    (hket :
      ∀ b : qs.Basis,
        LowerGateClass.evalL (qs := qs) L (qs.ket b) =
          qs.eval G (qs.ket b)) :
    ∀ ψ : qs.State,
      LowerGateClass.evalL (qs := qs) L ψ =
        qs.eval G ψ := by
  apply qs.state_induction
    (fun ψ =>
      LowerGateClass.evalL (qs := qs) L ψ =
        qs.eval G ψ)

  · rw [LowerGateClass.evalL_zero]
    have h0 :=
      GateSemanticsCore.eval_smul
        (qs := qs)
        G
        (0 : ℂ)
        (0 : qs.State)
    simp

  · intro ψ φ hψ hφ
    simp [
      LowerGateClass.evalL_add,
      GateSemanticsCore.eval_add,
      hψ, hφ
    ]

  · intro a ψ hψ
    simp [
      LowerGateClass.evalL_smul,
      GateSemanticsCore.eval_smul,
      hψ
    ]

  · intro b
    exact hket b
end LowerGateClass

namespace LowerGateGateBridge
open LowerGateClass
theorem evalL_shiftL
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (r : ExtReg) (n : ℕ) (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.ShiftL r n) ψ
      =
    qs.eval (Gate.ShiftL r n) ψ := by
  apply
    evalL_eq_eval_of_ket_eq
      qs
      (LowGate.ShiftL r n)
      (Gate.ShiftL r n)
  intro b
  rw [
    LowerGateClass.evalL_shiftL_ket_total,
    ArithmeticSemantics.eval_ShiftL_ket_total
  ]

theorem evalL_shiftR
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (r : ExtReg) (n : ℕ) (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.ShiftR r n) ψ
      =
    qs.eval (Gate.ShiftR r n) ψ := by
  apply
    evalL_eq_eval_of_ket_eq
      qs
      (LowGate.ShiftR r n)
      (Gate.ShiftR r n)
  intro b
  rw [
    LowerGateClass.evalL_shiftR_ket_total,
    ArithmeticSemantics.eval_ShiftR_ket_total
  ]

theorem evalL_negate
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (r : ExtReg) (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.Negate r) ψ
      =
    qs.eval (Gate.Negate r) ψ := by
  apply
    evalL_eq_eval_of_ket_eq
      qs
      (LowGate.Negate r)
      (Gate.Negate r)
  intro b
  rw [
    LowerGateClass.evalL_negate_ket_total,
    ArithmeticSemantics.eval_Negate_ket_total
  ]

theorem evalL_addScaled
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (dst src : ExtReg)
    (negSrc : Bool)
    (shift : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.AddScaled dst src negSrc shift) ψ
      =
    qs.eval
      (Gate.AddScaled dst src negSrc shift) ψ := by
  apply
    evalL_eq_eval_of_ket_eq
      qs
      (LowGate.AddScaled dst src negSrc shift)
      (Gate.AddScaled dst src negSrc shift)
  intro b
  rw [
    LowerGateClass.evalL_addScaled_ket_total,
    ArithmeticSemantics.eval_AddScaled_ket_total
  ]


theorem evalL_signExtend
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (r : ExtReg) (n : ℕ) (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.signExtend r n) ψ
      =
    qs.eval (Gate.signExtend r n) ψ := by
  apply
    evalL_eq_eval_of_ket_eq
      qs
      (LowGate.signExtend r n)
      (Gate.signExtend r n)
  intro b
  rw [
    LowerGateClass.evalL_signExtend_ket_total,
    ExtensionSemantics.eval_signExtend_ket_total
  ]


theorem evalL_signDealloc
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (r : ExtReg) (n : ℕ) (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.signDealloc r n) ψ
      =
    qs.eval (Gate.signDealloc r n) ψ := by
  apply
    evalL_eq_eval_of_ket_eq
      qs
      (LowGate.signDealloc r n)
      (Gate.signDealloc r n)
  intro b
  rw [
    LowerGateClass.evalL_signDealloc_ket_total,
    ExtensionSemantics.eval_signDealloc_ket_total
  ]

theorem evalL_radixReverse
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (r : Reg) (m : ℕ) (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.RadixReverse r m) ψ
      =
    qs.eval (Gate.RadixReverse r m) ψ := by
  apply
    evalL_eq_eval_of_ket_eq
      qs
      (LowGate.RadixReverse r m)
      (Gate.RadixReverse r m)
  intro b
  rw [
    LowerGateClass.evalL_radixReverse_ket_total,
    RadixReverseSemantics.eval_RadixReverse_ket_total
  ]

end LowerGateGateBridge

end Shor
