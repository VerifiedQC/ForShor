import ForShor.ShorVerification.Model.Standard.Gates
import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics

/-!
# `evalLG` and `LowerGateClass`

Item 8 of the original construction plan: the same shape as `Gates.lean` over `LowGate`. The
primitives are a subset of the high-level ones plus `LowGate.Phase`, which is a
`diagLift`. No new mathematics.
-/

namespace Shor
namespace Model

/-- The model's low-level evaluator. -/
noncomputable def evalLG : LowGate → (State ≃ₗᵢ[ℂ] State)
  | LowGate.id => LinearIsometryEquiv.refl ℂ State
  | LowGate.seq U V => (evalLG U).trans (evalLG V)
  | LowGate.adj U => (evalLG U).symm
  | LowGate.H q => hadamardLift q
  | LowGate.X q => permLift (xPerm q)
  | LowGate.Phase q θ => diagLift (lowPhaseDiag q θ) (lowPhaseDiag_norm q θ)
  | LowGate.CNOT c t => permLift (cnotPerm c t)
  | LowGate.Toffoli c₁ c₂ t => permLift (toffoliPerm c₁ c₂ t)
  | LowGate.ShiftL r n => permLift (shiftLPerm r n)
  | LowGate.ShiftR r n => permLift (shiftRPerm r n)
  | LowGate.Negate r => permLift (negatePerm r)
  | LowGate.AddScaled dst src neg sh => permLift (addScaledPerm dst src neg sh)
  | LowGate.zeroExtend _ _ => LinearIsometryEquiv.refl ℂ State
  | LowGate.signExtend r n => permLift (signExtendPerm r n)
  | LowGate.zeroDealloc _ _ => LinearIsometryEquiv.refl ℂ State
  | LowGate.signDealloc r n => permLift (signExtendPerm r n)
  | LowGate.RadixReverse r m => permLift (radixReversePerm r m)

/-- **The lowered gate semantics.** -/
noncomputable instance instLowerGateClass : LowerGateClass qs where
  evalL L ψ := evalLG L ψ
  evalL_id _ := rfl
  evalL_seq _ _ _ := rfl
  evalL_add L ψ φ := map_add _ _ _
  evalL_smul L a ψ := map_smul _ _ _
  evalL_adj_apply L ψ := (evalLG L).symm_apply_apply ψ
  evalL_H_ket q b := by
    show hadamardLift q (ket b) = _
    rw [hadamardLift_ket]
    rfl
  evalL_X_ket q b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_Phase_ket q θ b := by
    show diagLift _ _ (ket b) = _
    rw [diagLift_ket, lowPhaseDiag]
    by_cases h : b q
    · rw [ite_eq_left h, ite_eq_left (show RegEncoding.bit q b = true from h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (RegEncoding.bit q b = true) from h), one_smul]
      rfl
  evalL_shiftL_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_shiftR_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_negate_ket_total r b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_addScaled_ket_total dst src neg sh b := by
    show permLift _ (ket b) = _
    rw [permLift_ket, addScaledPerm_apply]
    rfl
  evalL_CNOT_ket ctrl target b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_Toffoli_ket c₁ c₂ target b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_zeroExtend_id _ _ _ := rfl
  evalL_zeroDealloc_id _ _ _ := rfl
  evalL_signExtend_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_signDealloc_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  evalL_radixReverse_ket_total r m b := by
    show permLift _ (ket b) = _
    rw [permLift_ket, radixReversePerm_apply]
    rfl

end Model
end Shor
