import FastMultiplication.ShorVerification.Model.Standard.Blocks

/-!
# `evalG` and `GateSemanticsFacts`

Item 7 of the original construction plan. `Gate.adj` is a free constructor, so the model is
free to *define* its evaluation as the inverse: `evalG` lands in
`State ≃ₗᵢ[ℂ] State`, and all the generic laws of `GateSemanticsCore` become
one-liners from the `LinearIsometryEquiv` API.
-/

namespace Shor
namespace Model

/-! ## Named permutations, with their basis actions -/

@[simp] theorem xPerm_apply (q : ℕ) (b : ModelBasis) : xPerm q b = xBasis q b := rfl

@[simp] theorem cnotPerm_apply (ctrl target : ℕ) (b : ModelBasis) :
    cnotPerm ctrl target b = cnotBasis (Basis := ModelBasis) ctrl target b := rfl

@[simp] theorem toffoliPerm_apply (c₁ c₂ target : ℕ) (b : ModelBasis) :
    toffoliPerm c₁ c₂ target b = toffoliBasis (Basis := ModelBasis) c₁ c₂ target b := rfl

@[simp] theorem cmpGeConstPerm_apply (N : ℕ) (data : Reg) (flag : ℕ) (b : ModelBasis) :
    cmpGeConstPerm N data flag b = cmpGeConstBasis (Basis := ModelBasis) N data flag b := rfl

@[simp] theorem negatePerm_apply (r : ExtReg) (b : ModelBasis) :
    negatePerm r b = negateBasis (Basis := ModelBasis) r b := rfl

@[simp] theorem signExtendPerm_apply (r : ExtReg) (n : ℕ) (b : ModelBasis) :
    signExtendPerm r n b = signExtendBasis (Basis := ModelBasis) r n b := rfl

/-! ## The evaluator -/

/-- The model's evaluator. Every primitive gate is one of the three lifts from
`Lift.lean`; `adj` is the inverse and `seq` the composite. -/
noncomputable def evalG : Gate → (State ≃ₗᵢ[ℂ] State)
  | Gate.id => LinearIsometryEquiv.refl ℂ State
  | Gate.seq U V => (evalG U).trans (evalG V)
  | Gate.adj U => (evalG U).symm
  | Gate.H q => hadamardLift q
  | Gate.X q => permLift (xPerm q)
  | Gate.CNOT c t => permLift (cnotPerm c t)
  | Gate.Toffoli c₁ c₂ t => permLift (toffoliPerm c₁ c₂ t)
  | Gate.QFT e => qftLift e
  | Gate.RadixReverse r m => permLift (radixReversePerm r m)
  | Gate.SignedPhaseProd phi x z =>
      diagLift (phaseProdDiag phi x z) (phaseProdDiag_norm phi x z)
  | Gate.CSignedPhaseProd ctrl phi x z =>
      diagLift (cPhaseProdDiag ctrl phi x z) (cPhaseProdDiag_norm ctrl phi x z)
  | Gate.CmpGeConst N data _scratch flag => permLift (cmpGeConstPerm N data.active flag)
  | Gate.CSubConst N data _scratch flag => permLift (csubConstPerm N data.active flag)
  | Gate.ShiftL r n => permLift (shiftLPerm r n)
  | Gate.ShiftR r n => permLift (shiftRPerm r n)
  | Gate.Negate r => permLift (negatePerm r)
  | Gate.AddScaled dst src neg sh => permLift (addScaledPerm dst src neg sh)
  | Gate.zeroExtend _ _ => LinearIsometryEquiv.refl ℂ State
  | Gate.signExtend r n => permLift (signExtendPerm r n)
  | Gate.zeroDealloc _ _ => LinearIsometryEquiv.refl ℂ State
  | Gate.signDealloc r n => permLift (signExtendPerm r n)
  | Gate.idealCtrlModMul c N data ctrl => permLift (idealCtrlModMulPerm c N data ctrl)

/-- **The bundled gate semantics.** Every generic law is `LinearIsometryEquiv`
API; every `*_ket` law is the corresponding lift's ket equation. -/
noncomputable instance instGateSemanticsFacts : GateSemanticsFacts qs where
  eval U ψ := evalG U ψ
  eval_id _ := rfl
  eval_seq _ _ _ := rfl
  inner_preserved U ψ φ := (evalG U).inner_map_map ψ φ
  eval_add U ψ φ := map_add _ _ _
  eval_smul U a ψ := map_smul _ _ _
  eval_adj_apply U ψ := (evalG U).symm_apply_apply ψ
  eval_QFT_ket e b := by
    show qftLift e (ket b) = _
    rw [qftLift_ket]
    rfl
  eval_SignedPhaseProd_ket phi x z b := by
    show diagLift _ _ (ket b) = _
    rw [diagLift_ket]
    rfl
  eval_CSignedPhaseProd_ket ctrl phi x z b := by
    show diagLift _ _ (ket b) = _
    rw [diagLift_ket, cPhaseProdDiag]
    by_cases h : b ctrl
    · rw [if_pos h, if_pos (show RegEncoding.bit ctrl b = true from h)]
      rfl
    · rw [if_neg h, if_neg (show ¬ (RegEncoding.bit ctrl b = true) from h), one_smul]
      rfl
  eval_zeroExtend _ _ _ := rfl
  eval_zeroDealloc _ _ _ := rfl
  eval_signExtend_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_signDealloc_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_ShiftL_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_ShiftR_ket_total r n b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_Negate_ket_total r b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_AddScaled_ket_total dst src neg sh b := by
    show permLift _ (ket b) = _
    rw [permLift_ket, addScaledPerm_apply]
    rfl
  eval_CmpGeConst_ket N data scratch flag b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_CSubConst_ket N data scratch flag b := by
    show permLift _ (ket b) = _
    rw [permLift_ket, csubConstPerm_apply]
    rfl
  eval_RadixReverse_ket_total r m b := by
    show permLift _ (ket b) = _
    rw [permLift_ket, radixReversePerm_apply]
    rfl
  eval_H_ket q b := by
    show hadamardLift q (ket b) = _
    rw [hadamardLift_ket]
    rfl
  eval_X_ket q b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_CNOT_ket ctrl target b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_Toffoli_ket c₁ c₂ target b := by
    show permLift _ (ket b) = _
    rw [permLift_ket]
    rfl
  eval_idealCtrlModMul_ket_exact c N data ctrl b hN hNA hcop hctrl hx := by
    show permLift _ (ket b) = _
    rw [permLift_ket, idealCtrlModMulPerm_apply,
      idealCtrlModMulBasis_of_guard hN hNA hcop hctrl hx]
    rfl

end Model
end Shor
