import FastMultiplication.ShorVerification.Model.QuantumLib.Denote

/-!
# Transfer: `evalL` on the embedded subspace *is* `denote`

For every low gate `C` whose qubits all lie below `dim`,

```
evalLG C (ι dim v) = ι dim (denote dim C * v)
```

The primitive cases all go through `Embed.transfer_of_ket`: it is enough to
check each gate on a ket, where `Standard/Lift.lean`'s `permLift_ket`,
`diagLift_ket` and `Standard/Blocks.lean`'s `hadamardLift_ket` give the answer
directly. The `adj` case is where unitarity of `denote` is
used: `evalLG (†U)` is `(evalLG U).symm`, and the two agree precisely because
`denote dim U` is unitary.
-/

namespace Shor
namespace Model
namespace QuantumLib

open Matrix

/-! ## Single-qubit writes as `Function.update` -/

theorem mWriteNat_qubitReg_zero (q : ℕ) (b : ModelBasis) :
    mWriteNat (qubitReg q) 0 b = Function.update b q false :=
  mWriteNat_qubitReg_bool q false b

theorem mWriteNat_qubitReg_one (q : ℕ) (b : ModelBasis) :
    mWriteNat (qubitReg q) 1 b = Function.update b q true :=
  mWriteNat_qubitReg_bool q true b

/-! ## The three lifts, on a ket -/

theorem permLift_ket_transfer {dim : ℕ} {σ : Equiv.Perm ModelBasis} (h : BelowStable dim σ)
    (k : Fin (2 ^ dim)) :
    permLift σ (ket (idxBasis dim k)) = ι dim (permMatrix dim σ * e dim k) := by
  rw [permLift_ket, ι_mul_e, Finset.sum_eq_single (permIdx dim σ k)]
  · rw [permMatrix, ite_eq_left rfl, one_smul, permIdx,
      idxBasis_basisIdx (h.fwd _ (idxBasis_below dim k))]
  · intro k' _ hk'
    rw [permMatrix, ite_eq_right hk', zero_smul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

theorem diagLift_ket_transfer {dim : ℕ} (φ : ModelBasis → ℂ) (hφ : ∀ b, ‖φ b‖ = 1)
    (k : Fin (2 ^ dim)) :
    diagLift φ hφ (ket (idxBasis dim k)) = ι dim (diagMatrix dim φ * e dim k) := by
  rw [diagLift_ket, ι_mul_e, Finset.sum_eq_single k]
  · rw [diagMatrix, ite_eq_left rfl]
  · intro k' _ hk'
    rw [diagMatrix, ite_eq_right hk', zero_smul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

theorem hadamardLift_ket_transfer {dim q : ℕ} (hq : q < dim) (k : Fin (2 ^ dim)) :
    hadamardLift q (ket (idxBasis dim k)) = ι dim (hMatrix dim q * e dim k) := by
  rw [hadamardLift_ket, ι_mul_e,
    Finset.sum_eq_add_of_mem (bitIdx dim q false k) (bitIdx dim q true k)
      (Finset.mem_univ _) (Finset.mem_univ _) (bitIdx_ne hq k)
      (fun y _ hy => by rw [hMatrix_eq_zero hq hy.1 hy.2, zero_smul]),
    hMatrix_false hq rfl, hMatrix_true hq rfl,
    mWriteNat_qubitReg_zero, mWriteNat_qubitReg_one,
    ← idxBasis_bitIdx hq false k, ← idxBasis_bitIdx hq true k, smul_add, smul_smul]
  rfl

/-! ## The induction -/

theorem transfer {dim : ℕ} : ∀ (C : LowGate), maxQubit C ≤ dim →
    ∀ v : CVector (2 ^ dim), evalLG C (ι dim v) = ι dim (denote dim C * v)
  | LowGate.id, _, v => by
      show ι dim v = _
      rw [show denote dim LowGate.id = 1 from rfl, Matrix.one_mul]
  | LowGate.seq U V, h, v => by
      show evalLG V (evalLG U (ι dim v)) = _
      rw [transfer U (le_trans (le_max_left _ _) h) v,
        transfer V (le_trans (le_max_right _ _) h),
        show denote dim (LowGate.seq U V) = denote dim V * denote dim U from rfl,
        Matrix.mul_assoc]
  | LowGate.adj U, h, v => by
      have hU : denote dim U ∈ Matrix.unitaryGroup (Fin (2 ^ dim)) ℂ := denote_unitary U h
      have hmul : denote dim U * (denote dim U)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
      show (evalLG U).symm (ι dim v) = ι dim ((denote dim U)ᴴ * v)
      apply (evalLG U).injective
      rw [LinearIsometryEquiv.apply_symm_apply, transfer U h, ← Matrix.mul_assoc, hmul,
        Matrix.one_mul]
  | LowGate.H q, h, v =>
      transfer_of_ket _ _ (hadamardLift_ket_transfer (by simpa [maxQubit] using h)) v
  | LowGate.X q, h, v =>
      transfer_of_ket _ _
        (permLift_ket_transfer (belowStable_xPerm (by simpa [maxQubit] using h))) v
  | LowGate.Phase q θ, _, v =>
      transfer_of_ket _ _ (diagLift_ket_transfer (lowPhaseDiag q θ) (lowPhaseDiag_norm q θ)) v
  | LowGate.CNOT c t, h, v =>
      transfer_of_ket _ _
        (permLift_ket_transfer (belowStable_cnotPerm (by simp only [maxQubit] at h; omega))) v
  | LowGate.Toffoli c₁ c₂ t, h, v =>
      transfer_of_ket _ _
        (permLift_ket_transfer (belowStable_toffoliPerm (by simp only [maxQubit] at h; omega))) v
  | LowGate.ShiftL r n, h, v =>
      transfer_of_ket _ _ (permLift_ket_transfer (belowStable_shiftLPerm (active_below h) n)) v
  | LowGate.ShiftR r n, h, v =>
      transfer_of_ket _ _ (permLift_ket_transfer (belowStable_shiftRPerm (active_below h) n)) v
  | LowGate.Negate r, h, v =>
      transfer_of_ket _ _ (permLift_ket_transfer (belowStable_negatePerm (active_below h))) v
  | LowGate.AddScaled dst src neg sh, h, v =>
      transfer_of_ket _ _ (permLift_ket_transfer (belowStable_addScaledPerm
        (active_below (le_trans (le_max_left _ _) h)) neg sh)) v
  | LowGate.zeroExtend r n, _, v => by
      show ι dim v = _
      rw [show denote dim (LowGate.zeroExtend r n) = 1 from rfl, Matrix.one_mul]
  | LowGate.signExtend r n, h, v =>
      transfer_of_ket _ _
        (permLift_ket_transfer (belowStable_signExtendPerm (newBits_below h))) v
  | LowGate.zeroDealloc r n, _, v => by
      show ι dim v = _
      rw [show denote dim (LowGate.zeroDealloc r n) = 1 from rfl, Matrix.one_mul]
  | LowGate.signDealloc r n, h, v =>
      transfer_of_ket _ _
        (permLift_ket_transfer (belowStable_signExtendPerm (newBits_below h))) v
  | LowGate.RadixReverse r m, h, v =>
      transfer_of_ket _ _
        (permLift_ket_transfer (belowStable_radixReversePerm (reg_below h) m)) v

/-- The transfer theorem in the form the headline statements use: the
development's `evalL` on the embedded all-zeros input is matrix action. -/
theorem evalL_ι {dim : ℕ} (C : LowGate) (h : maxQubit C ≤ dim) (v : CVector (2 ^ dim)) :
    LowerGateClass.evalL (qs := qs) C (ι dim v) = ι dim (denote dim C * v) :=
  transfer C h v

end QuantumLib
end Model
end Shor
