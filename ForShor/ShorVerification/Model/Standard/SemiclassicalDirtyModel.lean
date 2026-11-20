import ForShor.ShorVerification.Implementation.Readout.LocalityDirty
import ForShor.ShorVerification.Model.Standard.LowGates

/-!
# Dirty reserves in the standard model

Instances of `Implementation/Readout/LocalityDirty.lean` at `Model.qs` (basis `ℕ → Bool`), with
concrete registers and basis states, showing that the hypotheses of the dirty-reserve results
can be met and that the dirty values really differ from the clean ones.

* `model_zeroExtend_dirty`: register `dReg` (active `[0]`, reserve `[1]`), reserve qubit set,
  active qubit clear. After zero extension the grown register reads `-2` (not the clean `0`),
  and D1's formula gives the same number.
* `model_signExtend_dirty`: active qubit set (the register reads `-1`), reserve qubit set. Sign
  extension complements the reserve qubit; the grown register reads `+1` (not the clean `-1`),
  as D1's formula says (`-1 - 2 * (-1)`).
* `model_grow_zero_formula_false`: D1's zero-extension formula WITHOUT the hypothesis `n ≥ 1` is
  false: at `n = 0` with the active qubit of `dReg` set, the register reads `-1` while the
  formula gives `1`.
* `model_unit_dirty_*`: N1 at a concrete workspace (`data` = `[0]` + reserve `[1]`, `scratch` =
  `[2, 3]` + reserve `[4]`, flag `5`, `N = 1`) and the basis state with only `u = 4` set: the
  lowered comparator and `Gate.CmpGeConst` disagree there, while the high-level gate commutes with
  `X 4`.
* `model_unit_dirty_needs_clean_data_reserve`: N1 as first drafted (without a clean data reserve
  qubit) is FALSE: with the data reserve qubit also set, the lowered and high-level comparators
  agree on that ket.
* `model_lowered_qft_reads_pool`: N2 at `Model.qs` and the no-table policy.
* `model_lowered_qft_differs_on_dirty_pool`: N2 in ket form at `Model.qs`.
* `model_toggle_closed_eval`: the closed-form toggle condition evaluated on a concrete ket.
* `model_stop_signed`: D2 at `Model.qs` (no-table policy, any operands, any state).
-/

namespace Shor
namespace Model

open Dirty Readout

/-! ## D1 -/

/-- Active qubit `[0]`, reserve qubit `[1]`. -/
def dReg : ExtReg := ⟨⟨[0], by simp⟩, ⟨[1], by simp⟩, by simp [Shor.Disjoint]⟩

/-- Only the reserve qubit `1` is set. -/
def reserveSetBasis : ModelBasis := fun q => decide (q = 1)

/-- Qubits `0` and `1` are set. -/
def bothSetBasis : ModelBasis := fun q => decide (q = 0 ∨ q = 1)

/-- Only qubit `0` is set. -/
def activeSetBasis : ModelBasis := fun q => decide (q = 0)

/-- **D1 (zero extension) at the model.** The dirty reserve bit makes the grown register read `-2`
instead of the clean value `0`; `extToInt_grow_dirty` predicts exactly this value. -/
theorem model_zeroExtend_dirty :
    extToInt (Basis := ModelBasis) (dReg.grow 1) reserveSetBasis = -2 ∧
      extToInt (Basis := ModelBasis) dReg reserveSetBasis = 0 ∧
      extToInt (Basis := ModelBasis) (dReg.grow 1) reserveSetBasis
        = (dReg.toNat reserveSetBasis : ℤ) + 2 ^ dReg.width *
            tcDecodeWidth 1 (RegEncoding.toNat (dReg.newBits 1) reserveSetBasis) :=
  ⟨by decide, by decide, extToInt_grow_dirty dReg 1 reserveSetBasis (by unfold ExtReg.CanGrow ExtReg.capacity; decide) (by decide)⟩

/-- **D1 (sign extension) at the model.** The register reads `-1`; with the reserve bit dirty,
sign extension complements it to `0` and the grown register reads `+1`, not `-1`;
`extToInt_grow_signExtendBasis_dirty` predicts exactly this value. -/
theorem model_signExtend_dirty :
    extToInt (Basis := ModelBasis) dReg bothSetBasis = -1 ∧
      extToInt (Basis := ModelBasis) (dReg.grow 1) (signExtendBasis dReg 1 bothSetBasis) = 1 ∧
      extToInt (Basis := ModelBasis) (dReg.grow 1) (signExtendBasis dReg 1 bothSetBasis)
        = extToInt dReg bothSetBasis
          + (if extToInt dReg bothSetBasis < 0 then (-1 : ℤ) else 1) * 2 ^ dReg.width *
            tcDecodeWidth 1 (RegEncoding.toNat (dReg.newBits 1) bothSetBasis) :=
  ⟨by decide, by decide, extToInt_grow_signExtendBasis_dirty dReg 1 bothSetBasis (by unfold ExtReg.CanGrow ExtReg.capacity; decide)⟩

/-- **The zero-extension formula needs `n ≥ 1`.** Without it the formula is false: at `n = 0`,
`dReg` with its active qubit set reads `-1`, while `r.toNat b + 2^w * tcDecodeWidth 0 _ = 1`. -/
theorem model_grow_zero_formula_false :
    ¬ ∀ (r : ExtReg) (n : ℕ) (b : ModelBasis), r.CanGrow n →
      extToInt (r.grow n) b
        = (r.toNat b : ℤ) + 2 ^ r.width * tcDecodeWidth n (RegEncoding.toNat (r.newBits n) b) :=
  fun h => absurd (h dReg 0 activeSetBasis (by unfold ExtReg.CanGrow ExtReg.capacity; decide)) (by decide)

/-! ## N1 -/

/-- `data`: active `[0]`, reserve `[1]`. -/
def n1Data : ExtReg := dReg

/-- `scratch`: active `[2, 3]`, reserve `[4]`. -/
def n1Scratch : ExtReg := ⟨⟨[2, 3], by simp⟩, ⟨[4], by simp⟩, by simp [Shor.Disjoint]⟩

/-- The static workspace record holds for `N = 1`, `data = n1Data`, `scratch = n1Scratch`,
flag `5`. -/
theorem n1Workspace : ConstArithmeticWorkspace 1 n1Data n1Scratch 5 where
  data_can_grow := by unfold ExtReg.CanGrow ExtReg.capacity; decide
  scratch_can_grow := by unfold ExtReg.CanGrow ExtReg.capacity; decide
  data_scratch_disjoint := by
    simp [ExtReg.OwnedDisjoint, ExtReg.ownedQubits, n1Data, dReg, n1Scratch]
  flag_not_data := by decide
  flag_not_scratch := by decide
  scratch_positive := by decide
  constant_fits := by decide
  data_width_fits := by decide

/-- Only the unit qubit `u = 4` is set. -/
def unitSetBasis : ModelBasis := fun q => decide (q = 4)

/-- The unit qubit of `n1Scratch` is qubit `4`. -/
theorem n1_unit_eq : constArithmeticUnitQubit n1Scratch n1Workspace.scratch_can_grow = 4 := by
  decide

/-- **N1 at the model.** The hypotheses of `dirty_unit_breaks_comparator` hold on `unitSetBasis`
(dirty `u`, everything else `0`, `data = 0 < N = 1`); hence the high-level comparator commutes with
`X 4` while the lowered comparator and the high-level one disagree on `|unitSetBasis⟩`. -/
theorem model_unit_dirty_breaks_comparator :
    CommX qs (Gate.CmpGeConst 1 n1Data n1Scratch 5) 4 ∧
      LowerGateClass.evalL (lowerCmpGeConst 1 n1Data n1Scratch 5 n1Workspace)
          (qs.ket unitSetBasis)
        ≠ qs.eval (Gate.CmpGeConst 1 n1Data n1Scratch 5) (qs.ket unitSetBasis) := by
  have h := dirty_unit_breaks_comparator (qs := qs) 1 n1Data n1Scratch 5 n1Workspace unitSetBasis
    (by rw [n1_unit_eq]; decide) (by decide) (by unfold ExtReg.FreshFor FreshZero; decide)
    (by decide)
  rw [n1_unit_eq] at h
  exact h

/-- **N1 at the model, the lowered output.** The lowered comparator flips the flag `5` on
`|unitSetBasis⟩` (D3 closed form with the toggle evaluated). -/
theorem model_unit_dirty_lowered_flips_flag :
    LowerGateClass.evalL (lowerCmpGeConst 1 n1Data n1Scratch 5 n1Workspace)
        (qs.ket unitSetBasis) = qs.ket (flipBit 5 unitSetBasis) := by
  rw [dirty_comparator]
  have ht : cmpDirtyToggle 1 n1Data n1Scratch 5 n1Workspace unitSetBasis = true := by
    rw [cmpDirtyToggle_iff, extToInt_cmpPrepBasis_of_unit_set _ _ _ _ (by rw [n1_unit_eq]; decide)]
    decide
  rw [ht]; rfl

/-- `u` and the data reserve qubit `1` are set. -/
def unitAndDataReserveSetBasis : ModelBasis := fun q => decide (q = 1 ∨ q = 4)

/-- **N1 needs the clean data-reserve hypothesis.** The scope draft stated N1 with hypotheses
`u = 1`, `scratch = 0`, `data < N` only. That version is FALSE: on `unitAndDataReserveSetBasis`
(`u = 1`, `scratch = 0`, `data = 0 < N = 1`, but the data reserve qubit `1` also set) the grown
data register reads `-2`, the sum is negative, the lowered comparator does NOT toggle the flag,
and it agrees with `Gate.CmpGeConst` on that ket. Hence the hypothesis `data.FreshFor 1 b` of
`lowerCmpGeConst_ne_of_unit_dirty` cannot simply be dropped. -/
theorem model_unit_dirty_needs_clean_data_reserve :
    RegEncoding.bit (constArithmeticUnitQubit n1Scratch n1Workspace.scratch_can_grow)
        unitAndDataReserveSetBasis = true ∧
      extToInt (Basis := ModelBasis) n1Scratch unitAndDataReserveSetBasis = 0 ∧
      RegEncoding.toNat (Basis := ModelBasis) n1Data.active unitAndDataReserveSetBasis < 1 ∧
      LowerGateClass.evalL (lowerCmpGeConst 1 n1Data n1Scratch 5 n1Workspace)
          (qs.ket unitAndDataReserveSetBasis)
        = qs.eval (Gate.CmpGeConst 1 n1Data n1Scratch 5) (qs.ket unitAndDataReserveSetBasis) := by
  refine ⟨by rw [n1_unit_eq]; decide, by decide, by decide, ?_⟩
  rw [dirty_comparator, ModularArithmeticSemantics.eval_CmpGeConst_ket]
  have ht : cmpDirtyToggle 1 n1Data n1Scratch 5 n1Workspace unitAndDataReserveSetBasis = false := by
    rw [← Bool.not_eq_true, cmpDirtyToggle_iff,
      extToInt_cmpPrepBasis_of_unit_set _ _ _ _ (by rw [n1_unit_eq]; decide)]
    decide
  rw [ht]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  symm
  apply RegEncoding.basis_ext
  intro q
  by_cases hq : q = 5
  · subst hq; decide
  · have hq' : q ∉ (qubitReg 5).qubits := by simpa [qubitReg, Reg.singleton] using hq
    simp only [cmpGeConstBasis, show (5 : ℕ) ∉ n1Data.active.qubits by decide, ↓reduceIte]
    exact RegEncoding.bit_writeNat_out _ _ _ _ hq'

/-! ## N2, D2 -/

/-- **N2 at the model.** The high-level QFT of `n2Reg` commutes with `X 2`; the lowered QFT at
the no-table policy does not. -/
theorem model_lowered_qft_reads_pool :
    CommX qs (Gate.QFT n2Reg) 2 ∧
      ¬ CommXL qs (Policy.lowerQFT noTablePolicy n2Reg (n2Reg_reserveOK _ rfl)) 2 :=
  (lowered_qft_reads_pool noTablePolicy rfl _).2

/-- **N2 at the model, ket level.** Some basis ket with a dirty pool qubit is sent to different
states by the lowered QFT (no-table policy) and by `Gate.QFT n2Reg`. -/
theorem model_lowered_qft_differs_on_dirty_pool :
    ∃ b : qs.Basis, (RegEncoding.bit 2 b = true ∨ RegEncoding.bit 3 b = true) ∧
      LowerGateClass.evalL (Policy.lowerQFT noTablePolicy n2Reg (n2Reg_reserveOK _ rfl))
          (qs.ket b) ≠ qs.eval (Gate.QFT n2Reg) (qs.ket b) :=
  lowered_qft_differs_on_dirty_pool noTablePolicy rfl _

/-- **D3 closed form at the model.** On `unitAndDataReserveSetBasis` the closed-form toggle
condition evaluates to `false` (the sum is `0 + 0 - 2 = -2`). -/
theorem model_toggle_closed_eval :
    cmpDirtyToggle 1 n1Data n1Scratch 5 n1Workspace unitAndDataReserveSetBasis = false := by
  rw [← Bool.not_eq_true, cmpDirtyToggle_iff_closed, show
    RegEncoding.bit (constArithmeticUnitQubit n1Scratch n1Workspace.scratch_can_grow)
      unitAndDataReserveSetBasis = true by rw [n1_unit_eq]; decide]
  decide

/-- **D2 at the model.** At the no-table policy the lowered signed phase product equals the
high-level gate on every state. -/
theorem model_stop_signed (phi : Angle) (x z : ExtReg) (ψ : qs.State) :
    LowerGateClass.evalL (Policy.lowerSignedPhaseProd noTablePolicy phi x z) ψ
      = qs.eval (Gate.SignedPhaseProd phi x z) ψ :=
  dirty_stop_signed noTablePolicy phi x z (choose_none_of_bands_nil _ rfl _) ψ

end Model
end Shor

#print axioms Shor.Model.model_zeroExtend_dirty
#print axioms Shor.Model.model_signExtend_dirty
#print axioms Shor.Model.model_grow_zero_formula_false
#print axioms Shor.Model.n1Workspace
#print axioms Shor.Model.model_unit_dirty_breaks_comparator
#print axioms Shor.Model.model_unit_dirty_lowered_flips_flag
#print axioms Shor.Model.model_unit_dirty_needs_clean_data_reserve
#print axioms Shor.Model.model_lowered_qft_reads_pool
#print axioms Shor.Model.model_stop_signed
#print axioms Shor.Model.model_lowered_qft_differs_on_dirty_pool
#print axioms Shor.Model.model_toggle_closed_eval
