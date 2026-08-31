import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas

/-!
# Lowered-Gate Evaluation Lemmas

`evalL_*` rewrite lemmas that unfold the low-level gate evaluator
(`LowerGateClass.evalL`) for each phase-product primitive — the simp library the
rest of the lowering-correctness proofs build on.
-/


namespace Shor
open Gate
open Operations

namespace LowerGateClass

theorem evalL_eq_eval_of_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    (L : LowGate)
    (U : Gate)
    (hket :
      ∀ b : qs.Basis,
        LowerGateClass.evalL (qs := qs) L (qs.ket b) =
          qs.eval U (qs.ket b)) :
    ∀ ψ : qs.State,
      LowerGateClass.evalL (qs := qs) L ψ =
        qs.eval U ψ := by
  refine qs.state_induction
    (fun ψ =>
      LowerGateClass.evalL (qs := qs) L ψ =
        qs.eval U ψ)
    ?hzero ?hadd ?hsmul hket
  · change LowerGateClass.evalL (qs := qs) L 0 = qs.eval U 0
    rw [LowerGateClass.evalL_zero, QSemantics.eval_zero]
  · intro ψ φ hψ hφ
    change
      LowerGateClass.evalL (qs := qs) L (ψ + φ) =
        qs.eval U (ψ + φ)
    rw [LowerGateClass.evalL_add, QSemantics.eval_add, hψ, hφ]
  · intro a ψ hψ
    change
      LowerGateClass.evalL (qs := qs) L (a • ψ) =
        qs.eval U (a • ψ)
    rw [LowerGateClass.evalL_smul, QSemantics.eval_smul, hψ]

theorem evalL_H
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [HadamardSemantics qs]
    [LowerGateClass qs]
    (qbit : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.H qbit) ψ =
      qs.eval (Gate.H qbit) ψ := by
  exact evalL_eq_eval_of_ket
    (qs := qs)
    (LowGate.H qbit)
    (Gate.H qbit)
    (by
      intro b
      rw [LowerGateClass.evalL_H_ket, HadamardSemantics.eval_H_ket])
    ψ

theorem evalL_X
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [PauliXSemantics qs]
    [LowerGateClass qs]
    (qbit : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.X qbit) ψ =
      qs.eval (Gate.X qbit) ψ := by
  exact evalL_eq_eval_of_ket
    (qs := qs)
    (LowGate.X qbit)
    (Gate.X qbit)
    (by
      intro b
      rw [LowerGateClass.evalL_X_ket, PauliXSemantics.eval_X_ket])
    ψ


theorem evalL_shiftL
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.ShiftL r n) ψ =
      qs.eval (Gate.ShiftL r n) ψ :=
  LowerGateGateBridge.evalL_shiftL qs r n ψ

theorem evalL_shiftR
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.ShiftR r n) ψ =
      qs.eval (Gate.ShiftR r n) ψ :=
  LowerGateGateBridge.evalL_shiftR qs r n ψ

theorem evalL_negate
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.Negate r) ψ =
      qs.eval (Gate.Negate r) ψ :=
  LowerGateGateBridge.evalL_negate qs r ψ

theorem evalL_addScaled
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (dst src : ExtReg)
    (negSrc : Bool)
    (shift : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.AddScaled dst src negSrc shift) ψ =
      qs.eval (Gate.AddScaled dst src negSrc shift) ψ :=
  LowerGateGateBridge.evalL_addScaled qs dst src negSrc shift ψ

theorem evalL_naive_signedPhaseProd
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [PhaseSemantics qs]
    [LowerGateClass qs]
    (phi : ℝ)
    (x z : ExtReg)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.Naive_SignedPhaseProd phi x z) ψ =
      qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
  exact evalL_eq_eval_of_ket
    (qs := qs)
    (LowGate.Naive_SignedPhaseProd phi x z)
    (Gate.SignedPhaseProd phi x z)
    (by
      intro b
      rw [
        LowerGateClass.evalL_naive_signedPhaseProd_ket,
        PhaseSemantics.eval_SignedPhaseProd_ket
      ])
    ψ

theorem evalL_naive_csignedPhaseProd
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [PhaseSemantics qs]
    [LowerGateClass qs]
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.Naive_CSignedPhaseProd ctrl phi x z) ψ =
      qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
  exact evalL_eq_eval_of_ket
    (qs := qs)
    (LowGate.Naive_CSignedPhaseProd ctrl phi x z)
    (Gate.CSignedPhaseProd ctrl phi x z)
    (by
      intro b
      rw [
        LowerGateClass.evalL_naive_csignedPhaseProd_ket,
        PhaseSemantics.eval_CSignedPhaseProd_ket
      ])
    ψ

theorem evalL_zeroExtend
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    [LowerGateClass qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.zeroExtend r n) ψ =
      qs.eval (Gate.zeroExtend r n) ψ := by
  rw [LowerGateClass.evalL_zeroExtend_id, ExtensionSemantics.eval_zeroExtend]

theorem evalL_signExtend
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.signExtend r n) ψ =
      qs.eval (Gate.signExtend r n) ψ :=
  LowerGateGateBridge.evalL_signExtend qs r n ψ

theorem evalL_zeroDealloc
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [ExtensionSemantics qs]
    [LowerGateClass qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.zeroDealloc r n) ψ =
      qs.eval (Gate.zeroDealloc r n) ψ := by
  rw [LowerGateClass.evalL_zeroDealloc_id, ExtensionSemantics.eval_zeroDealloc]

theorem evalL_signDealloc
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (r : ExtReg)
    (n : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.signDealloc r n) ψ =
      qs.eval (Gate.signDealloc r n) ψ :=
  LowerGateGateBridge.evalL_signDealloc qs r n ψ

theorem evalL_radixReverse
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (r : Reg)
    (m : ℕ)
    (ψ : qs.State) :
    LowerGateClass.evalL (qs := qs) (LowGate.RadixReverse r m) ψ =
      qs.eval (Gate.RadixReverse r m) ψ :=
  LowerGateGateBridge.evalL_radixReverse qs r m ψ

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [GateSemanticsCore qs]
variable [PhaseSemantics qs]
variable [LowerGateClass qs]

end LowerGateClass

end Shor
