import FastMultiplication.ShorVerification.Framework.Semantics.LowGateSemantics
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import FastMultiplication.ShorVerification.Implementation.Shared.States
import FastMultiplication.ShorVerification.Implementation.Shared.GateLaws

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


theorem evalL_eq_of_ket_eq
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (U V : LowGate)
    (hket :
      ∀ b : qs.Basis,
        LowerGateClass.evalL (qs := qs) U (qs.ket b) =
          LowerGateClass.evalL (qs := qs) V (qs.ket b)) :
    ∀ ψ : qs.State,
      LowerGateClass.evalL (qs := qs) U ψ =
        LowerGateClass.evalL (qs := qs) V ψ := by
  apply qs.state_induction
    (fun ψ =>
      LowerGateClass.evalL (qs := qs) U ψ =
        LowerGateClass.evalL (qs := qs) V ψ)
  · rw [evalL_zero, evalL_zero]
  · intro ψ φ hψ hφ
    rw [
      LowerGateClass.evalL_add,
      LowerGateClass.evalL_add,
      hψ, hφ
    ]
  · intro a ψ hψ
    rw [
      LowerGateClass.evalL_smul,
      LowerGateClass.evalL_smul,
      hψ
    ]
  · intro b
    exact hket b

theorem evalL_shiftL_ket_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (r : ExtReg) (n : ℕ) (b : qs.Basis)
    (hfit :
      FitsSignedWidth r.width
        ((2 : ℤ) ^ n * extToInt r b)) :
    ∃ b' : qs.Basis,
      LowerGateClass.evalL (qs := qs)
          (LowGate.ShiftL r n) (qs.ket b) =
        qs.ket b'
      ∧
      extToInt r b' =
        (2 : ℤ) ^ n * extToInt r b
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e r →
        extToInt e b' = extToInt e b) := by
  refine ⟨shiftLBasis r n b, ?_, ?_, ?_⟩
  · exact
      LowerGateClass.evalL_shiftL_ket_total
        (qs := qs) r n b
  · exact
      extToInt_shiftLBasis_of_fits r n b hfit
  · intro e he
    exact
      extToInt_shiftLBasis_of_activeDisjoint
        r e n b he


theorem evalL_shiftR_ket_exact
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (r : ExtReg) (n : ℕ)
    (b : qs.Basis) (q : ℤ)
    (hexact :
      extToInt r b = (2 : ℤ) ^ n * q)
    (hfit : FitsSignedWidth r.width q) :
    ∃ b' : qs.Basis,
      LowerGateClass.evalL (qs := qs)
          (LowGate.ShiftR r n) (qs.ket b) =
        qs.ket b'
      ∧
      extToInt r b' = q
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e r →
        extToInt e b' = extToInt e b) := by
  refine ⟨shiftRBasis r n b, ?_, ?_, ?_⟩
  · exact
      LowerGateClass.evalL_shiftR_ket_total
        (qs := qs) r n b
  · exact
      extToInt_shiftRBasis_of_exact
        r n b q hexact hfit
  · intro e he
    exact
      extToInt_shiftRBasis_of_activeDisjoint
        r e n b he


theorem evalL_negate_ket_mod
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (r : ExtReg) (b : qs.Basis) :
    ∃ b' : qs.Basis,
      LowerGateClass.evalL (qs := qs)
          (LowGate.Negate r) (qs.ket b) =
        qs.ket b'
      ∧
      extToInt r b' =
        tcWrapInt r.width (- extToInt r b)
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e r →
        extToInt e b' = extToInt e b) := by
  refine ⟨negateBasis r b, ?_, ?_, ?_⟩
  · exact
      LowerGateClass.evalL_negate_ket_total
        (qs := qs) r b
  · exact extToInt_negateBasis r b
  · intro e he
    exact
      extToInt_negateBasis_of_activeDisjoint
        r e b he


theorem evalL_addScaled_ket_mod
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (dst src : ExtReg)
    (negSrc : Bool)
    (sh : ℕ)
    (b : qs.Basis)
    (hdisj : ExtReg.ActiveDisjoint dst src) :
    ∃ b' : qs.Basis,
      LowerGateClass.evalL (qs := qs)
          (LowGate.AddScaled dst src negSrc sh)
          (qs.ket b)
        =
      qs.ket b'
      ∧
      extToInt dst b' =
        tcWrapInt dst.width
          (extToInt dst b
            + (if negSrc then (-1 : ℤ) else 1)
                * (2 : ℤ) ^ sh
                * extToInt src b)
      ∧
      extToInt src b' = extToInt src b
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e dst →
        ExtReg.ActiveDisjoint e src →
        extToInt e b' = extToInt e b) := by
  refine
    ⟨addScaledBasis dst src negSrc sh b,
      ?_, ?_, ?_, ?_⟩
  · exact
      LowerGateClass.evalL_addScaled_ket_total
        (qs := qs) dst src negSrc sh b
  · simpa [addScaledValue] using
      extToInt_addScaledBasis_dst
        dst src negSrc sh b hdisj
  · exact
      extToInt_addScaledBasis_src
        dst src negSrc sh b hdisj
  · intro e hed _hes
    exact
      extToInt_addScaledBasis_of_activeDisjoint
        dst src e negSrc sh b hdisj hed

theorem evalL_signExtend_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (r : ExtReg)
    (n : ℕ)
    (b : qs.Basis)
    (hcap : r.CanGrow n)
    (hfresh : ExtReg.FreshFor r n b) :
    ∃ b' : qs.Basis,
      LowerGateClass.evalL (qs := qs)
          (LowGate.signExtend r n)
          (qs.ket b)
        =
      qs.ket b'
      ∧
      ExtReg.toNat r b' =
        ExtReg.toNat r b
      ∧
      extToInt (r.grow n) b' =
        extToInt r b
      ∧
      (∀ e : ExtReg,
        ExtReg.ActiveDisjoint e (r.grow n) →
        ExtReg.toNat e b' =
          ExtReg.toNat e b) := by
  refine ⟨signExtendBasis r n b, ?_, ?_, ?_, ?_⟩
  · exact
      LowerGateClass.evalL_signExtend_ket_total
        (qs := qs) r n b
  · exact toNat_signExtendBasis r n b
  · exact
      extToInt_grow_signExtendBasis
        r n b hcap hfresh
  · intro e he
    exact
      toNat_signExtendBasis_of_activeDisjoint
        r e n b he

theorem evalL_signDealloc_eq_adj
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs)
        (LowGate.signDealloc r n) ψ
      =
    LowerGateClass.evalL (qs := qs)
        (LowGate.adj (LowGate.signExtend r n)) ψ := by
  apply
    LowerGateClass.evalL_eq_of_ket_eq
      qs
      (LowGate.signDealloc r n)
      (LowGate.adj (LowGate.signExtend r n))

  intro b

  rw [LowerGateClass.evalL_signDealloc_ket_total]

  have hadj :=
    LowerGateClass.evalL_adj_apply
      (qs := qs)
      (LowGate.signExtend r n)
      (qs.ket (signExtendBasis r n b))

  rw [
    LowerGateClass.evalL_signExtend_ket_total,
    signExtendBasis_involutive
  ] at hadj

  simpa [signDeallocBasis] using hadj.symm

theorem evalL_radixReverse_ket
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    (r : Reg) (m : ℕ) (hm : m ≤ regSize r)
    (b : qs.Basis) (kL kH : ℕ) :
    let sp : SplitPoint r := ⟨m, hm⟩
    let left  : Reg := splitLeft r sp
    let right : Reg := splitRight r sp
    kL < ASize left →
    kH < ASize right →
    LowerGateClass.evalL (qs := qs)
      (LowGate.RadixReverse r m)
      (qs.ket
        (RegEncoding.writeNat left kL
          (RegEncoding.writeNat right kH b)))
    =
    qs.ket
      (RegEncoding.writeNat r
        (radixReverseIndex r m hm kL kH)
        b) := by
  dsimp
  intro hkL hkH

  rw [LowerGateClass.evalL_radixReverse_ket_total]

  exact congrArg qs.ket
    (radixReverseBasis_writeNat
      r m hm b kL kH hkL hkH)

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
