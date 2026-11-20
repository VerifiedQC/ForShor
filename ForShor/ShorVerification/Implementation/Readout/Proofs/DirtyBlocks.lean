import ForShor.ShorVerification.Implementation.Readout.Proofs.DirtyBasis
import ForShor.ShorVerification.Implementation.Readout.Proofs.Basic
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.NaiveLeaf
import ForShor.ShorVerification.Implementation.QFT.Statement
import ForShor.ShorVerification.Implementation.Compiler.Proofs.ConstArithmetic
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowLocality
import ForShor.ShorVerification.Implementation.QFT.Main

/-!
# Dirty reserves: lowered blocks on arbitrary input (low-gate level)

What the LOWERED blocks do when their reserve / workspace qubits hold arbitrary values. Every
statement here is about `LowerGateClass.evalL` on EVERY basis ket or EVERY state, with no
cleanliness hypothesis.

* D2 (`Policy.lowerSignedPhaseProd_eval_of_stop`, `Policy.lowerCSignedPhaseProd_eval_of_stop`,
  `Policy.phaseProdUsing_eval_of_stop`): at a node where the policy has no table
  (`P.choose (phaseInputSize x z) = none`) the lowered signed phase product IS the naive leaf,
  and it equals the high-level gate on EVERY state. For `PhaseProdUsing` this includes states
  whose two sign-extension qubits (the first reserve qubit of each operand) are dirty: the
  high-level macro reads those qubits too, through the same zero extension.
  "Equal on every state" does NOT mean "harmless on dirty input": `Gate.PhaseProdUsing`
  zero-extends INTO the reserve qubit and `Gate.SignedPhaseProd` reads it, so on dirty input
  both sides compute the same, WRONG unsigned phase (the operand value is shifted as in D1).
  D2 says only that the lowering adds no further error at a stopping node.
* D3 (`evalL_lowerCmpGeConst_ket_dirty`, `evalL_lowerCSubConst_ket_dirty`): the lowered
  constant comparator and controlled constant subtraction on EVERY basis ket. Every qubit except
  the flag (comparator) / `data.active` (subtraction) is restored, on any input; the flag is
  toggled iff `cmpDirtyToggle`, and `data` receives `csubDirtyValue`. Both are given in closed
  form in terms of input values only by `cmpDirtyToggle_iff_closed` and
  `csubDirtyValue_eq_closed` (`Proofs/DirtyBasis.lean`). The clean case is recovered
  (`cmpDirtyToggle_of_clean`, `csubDirty_of_clean`) from the existing clean theorems
  `evalL_lowerCmpGeConst_ket`, `evalL_lowerCSubConst_ket`.
* N1 (`lowerCmpGeConst_ne_of_unit_dirty`): with the unit qubit `u = scratch.newBits 1`[0]
  reading `1` (everything else clean, `data < N`), the lowered comparator toggles the flag while
  `Gate.CmpGeConst` does not: the two differ on that ket.
* N2 (`lowerQFT_not_commXL_pool`): at any policy with no table (`P.bands = []`) the lowered QFT
  of the width-2 register `n2Reg` (active `[0, 1]`, reserve `[2, 3]`) does NOT commute with `X` on
  qubit `2`, the first qubit of its x-side workspace pool (`qftXWork_n2Reg`). The lowered
  twiddle `PhaseProdUsing` reads that pool qubit as the sign bit of its x operand; the
  high-level `Gate.QFT` reads only `r.active` (`commX_QFT`), so the lowered circuit reads a
  reserve qubit the high-level circuit ignores. Proof: peel off the two Hadamards and the radix
  reversal (`commXL_of_commXL_seq4`), then the remaining phase block is diagonal with phases
  `1` and `exp(-iπ) = -1` on `|q1 = 1⟩` and on the same ket with qubit `2` flipped
  (`phase_flip_eq_of_commXL`).
  Ket-level form (`lowerQFT_ne_QFT_dirty_pool`): some basis ket with a dirty pool qubit (`2` or
  `3`) is mapped to different states by the lowered QFT and by `Gate.QFT n2Reg` (on kets with
  both pool qubits clean they agree, by the existing `Policy.lowerQFT_correct`).
-/

namespace Shor
namespace Dirty

open Readout

section Linear

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsCore qs] [LowerGateClass qs]

/-- A low gate and a high-level gate that agree on every basis ket agree on every state. -/
theorem evalL_eq_eval_of_ket (L : LowGate) (U : Gate)
    (h : ∀ b, LowerGateClass.evalL (qs := qs) L (qs.ket b) = qs.eval U (qs.ket b))
    (ψ : qs.State) : LowerGateClass.evalL (qs := qs) L ψ = qs.eval U ψ := by
  have := linearMap_ext_ket (lowL (qs := qs) L) (gateL U) (fun b => by simpa using h b) ψ
  simpa using this

end Linear

/-! ## D2: a stopping node is lowered exactly, on every state -/

/-- At a node where the policy has no table, the lowered signed phase product is the naive
leaf circuit. -/
theorem Policy.lowerSignedPhaseProd_eq_naive_of_stop (P : ShorLoweringPolicy) (phi : Angle)
    (x z : ExtReg) (h : P.choose (phaseInputSize x z) = none) :
    Policy.lowerSignedPhaseProd P phi x z = LowGate.Naive_SignedPhaseProd phi x z := by
  unfold Policy.lowerSignedPhaseProd Policy.signedPlan
  suffices hs : ∀ (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o), o = none →
      lowerGateRec (Policy.signedPlanOf P phi x z (phaseInputSize x z) o ho)
        = LowGate.Naive_SignedPhaseProd phi x z from hs _ rfl h
  rintro o ho rfl
  rw [Policy.signedPlanOf]; rfl

/-- The controlled form. -/
theorem Policy.lowerCSignedPhaseProd_eq_naive_of_stop (P : ShorLoweringPolicy) (ctrl : ℕ)
    (phi : Angle) (x z : ExtReg) (h : P.choose (phaseInputSize x z) = none) :
    Policy.lowerCSignedPhaseProd P ctrl phi x z = LowGate.Naive_CSignedPhaseProd ctrl phi x z := by
  unfold Policy.lowerCSignedPhaseProd Policy.cSignedPlan
  suffices hs : ∀ (o : Option ToomCookTable) (ho : P.choose (phaseInputSize x z) = o), o = none →
      lowerGateRec (Policy.cSignedPlanOf P ctrl phi x z (phaseInputSize x z) o ho)
        = LowGate.Naive_CSignedPhaseProd ctrl phi x z from hs _ rfl h
  rintro o ho rfl
  rw [Policy.cSignedPlanOf]; rfl

section D2

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]

/-- **D2: a stopping node is lowered exactly on EVERY state.** If the policy `P` has no table at
the node's input width (`P.choose (phaseInputSize x z) = none`), the lowered signed phase product
equals the high-level `Gate.SignedPhaseProd phi x z` on every state `ψ`: no cleanliness, no
admissibility, no workspace condition. Not claimed: anything at a node where a table is
chosen (there the lowering writes into reserve qubits). -/
theorem Policy.lowerSignedPhaseProd_eval_of_stop (P : ShorLoweringPolicy) (phi : Angle)
    (x z : ExtReg) (h : P.choose (phaseInputSize x z) = none) (ψ : qs.State) :
    LowerGateClass.evalL (Policy.lowerSignedPhaseProd P phi x z) ψ
      = qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
  rw [Policy.lowerSignedPhaseProd_eq_naive_of_stop P phi x z h]
  refine evalL_eq_eval_of_ket _ _ (fun b => ?_) ψ
  rw [LowerGateClass.evalL_naive_signedPhaseProd_ket, PhaseSemantics.eval_SignedPhaseProd_ket]

/-- **D2, controlled.** Same hypothesis (no table at the node's width); the lowered controlled
signed phase product equals `Gate.CSignedPhaseProd ctrl phi x z` on every state. -/
theorem Policy.lowerCSignedPhaseProd_eval_of_stop (P : ShorLoweringPolicy) (ctrl : ℕ)
    (phi : Angle) (x z : ExtReg) (h : P.choose (phaseInputSize x z) = none) (ψ : qs.State) :
    LowerGateClass.evalL (Policy.lowerCSignedPhaseProd P ctrl phi x z) ψ
      = qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
  rw [Policy.lowerCSignedPhaseProd_eq_naive_of_stop P ctrl phi x z h]
  refine evalL_eq_eval_of_ket _ _ (fun b => ?_) ψ
  rw [LowerGateClass.evalL_naive_csignedPhaseProd_ket, PhaseSemantics.eval_CSignedPhaseProd_ket]

/-- **D2 for the unsigned macro `PhaseProdUsing`.** If the policy has no table at the width of
the two grown operands, the lowered macro (zero-extend both operands by one reserve qubit,
lowered signed product, deallocate) equals the high-level `Gate.PhaseProdUsing phi x z ws` on
every state, in particular on states whose two sign-extension reserve qubits are dirty. -/
theorem Policy.phaseProdUsing_eval_of_stop (P : ShorLoweringPolicy) (phi : Angle) {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (h : P.choose (phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1)) = none) (ψ : qs.State) :
    LowerGateClass.evalL (lowerGateRec (Policy.phaseProdUsingPlan P phi ws)) ψ
      = qs.eval (Gate.PhaseProdUsing phi x z ws) ψ := by
  have hplan :
      lowerGateRec (Policy.phaseProdUsingPlan P phi ws)
        = LowGate.seq (LowGate.zeroExtend ws.xExt 1)
            (LowGate.seq (LowGate.zeroExtend ws.zExt 1)
              (LowGate.seq (Policy.lowerSignedPhaseProd P phi (ws.xExt.grow 1) (ws.zExt.grow 1))
                (LowGate.seq (LowGate.zeroDealloc ws.zExt 1) (LowGate.zeroDealloc ws.xExt 1)))) :=
    rfl
  rw [hplan]
  simp only [Gate.PhaseProdUsing, LowerGateClass.evalL_seq, GateSemanticsCore.eval_seq,
    LowerGateClass.evalL_zeroExtend_id, LowerGateClass.evalL_zeroDealloc_id,
    ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_zeroDealloc]
  exact Policy.lowerSignedPhaseProd_eval_of_stop P phi _ _ h ψ

end D2

/-! ## D3: the lowered constant arithmetic on every basis ket -/

section D3

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- The lowered copy realises `copyBitsBasis` on every basis ket. -/
theorem evalL_lowerCopyBitPowers_ket (dst : ExtReg) (ctrl : ℕ) (bits : List ℕ) (b : qs.Basis) :
    LowerGateClass.evalL (lowerCopyBitPowers dst ctrl bits) (qs.ket b)
      = qs.ket (copyBitsBasis dst ctrl bits b) := by
  induction bits generalizing b with
  | nil => simp [lowerCopyBitPowers, copyBitsBasis, LowerGateClass.evalL_id]
  | cons i bits ih =>
      by_cases hi : i < dst.width
      · rw [copyBitsBasis_cons_of_lt _ _ _ _ _ hi]
        simp only [lowerCopyBitPowers, hi, ↓reduceDIte, LowerGateClass.evalL_seq,
          LowerGateClass.evalL_CNOT_ket]
        exact ih _
      · rw [copyBitsBasis_cons_of_not_lt _ _ _ _ _ hi]
        simp only [lowerCopyBitPowers, hi, ↓reduceDIte]
        exact ih _

/-- The lowered preparation realises `cmpPrepBasis` on every basis ket. -/
theorem evalL_lowerPrepareNegConst_ket_dirty (N : ℕ) (scratch : ExtReg)
    (hcap : scratch.CanGrow 1) (b : qs.Basis) :
    LowerGateClass.evalL (lowerPrepareNegConst N scratch hcap) (qs.ket b)
      = qs.ket (cmpPrepBasis N scratch hcap b) := by
  simp only [lowerPrepareNegConst, lowerCopyConstFromUnit, LowerGateClass.evalL_seq,
    LowerGateClass.evalL_X_ket]
  rw [evalL_lowerCopyBitPowers_ket, LowerGateClass.evalL_negate_ket_total]
  rfl

/-- A compute / act / uncompute sandwich `A ;; D ;; M ;; †D ;; †A` sends `|b⟩` to `|b'⟩` as
soon as `M` maps the computed state of `b` to the computed state of `b'`. -/
theorem evalL_sandwich5 (A D M : LowGate) (b b' : qs.Basis)
    (hk : LowerGateClass.evalL M (LowerGateClass.evalL D (LowerGateClass.evalL A (qs.ket b)))
      = LowerGateClass.evalL D (LowerGateClass.evalL A (qs.ket b'))) :
    LowerGateClass.evalL (A ;; D ;; M ;; †D ;; †A) (qs.ket b) = qs.ket b' := by
  simp only [LowerGateClass.evalL_seq]
  rw [hk, LowerGateClass.evalL_adj_apply, LowerGateClass.evalL_adj_apply]

/-- The three-part sandwich `A ;; M ;; †A`. -/
theorem evalL_sandwich3 (A M : LowGate) (b b' : qs.Basis)
    (hk : LowerGateClass.evalL M (LowerGateClass.evalL A (qs.ket b))
      = LowerGateClass.evalL A (qs.ket b')) :
    LowerGateClass.evalL (A ;; M ;; †A) (qs.ket b) = qs.ket b' := by
  simp only [LowerGateClass.evalL_seq]
  rw [hk, LowerGateClass.evalL_adj_apply]

/-- **D3, comparator, any input.** Under the static workspace record only (no cleanliness),
the lowered comparator maps every basis ket `|b⟩` to `|b⟩` with the flag toggled iff
`cmpDirtyToggle` holds: every other qubit (including `u`, `scratch`, the dirty reserve qubit of
`data`) is restored. `cmpDirtyToggle_iff` says when the toggle happens. -/
theorem evalL_lowerCmpGeConst_ket_dirty (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis) :
    LowerGateClass.evalL (lowerCmpGeConst N data scratch flag h) (qs.ket b)
      = qs.ket (if cmpDirtyToggle N data scratch flag h b then flipBit flag b else b) := by
  have hdiff : ∀ c : qs.Basis,
      LowerGateClass.evalL (LowGate.zeroExtend data 1 ;;
        LowGate.AddScaled scratch (data.grow 1) false 0 ;; LowGate.zeroDealloc data 1) (qs.ket c)
        = qs.ket (addScaledBasis scratch (data.grow 1) false 0 c) := fun c => by
    simp only [LowerGateClass.evalL_seq, LowerGateClass.evalL_zeroExtend_id,
      LowerGateClass.evalL_addScaled_ket_total, LowerGateClass.evalL_zeroDealloc_id]
  have hmid : ∀ sg, sg ∈ scratch.active.qubits → ∀ c : qs.Basis,
      LowerGateClass.evalL (LowGate.X flag ;; LowGate.CNOT sg flag) (qs.ket c)
        = qs.ket (if RegEncoding.bit sg c then c else flipBit flag c) := fun sg hsg c => by
    have hsf : sg ≠ flag := fun e => not_mem_active h.flag_not_scratch (e ▸ hsg)
    rw [LowerGateClass.evalL_seq, LowerGateClass.evalL_X_ket]
    change LowerGateClass.evalL (LowGate.CNOT _ flag) (qs.ket (flipBit flag c)) = _
    rw [LowerGateClass.evalL_CNOT_ket]
    unfold cnotBasis
    simp only [hsf, ↓reduceIte, bit_flipBit_ne hsf]
    by_cases hc : RegEncoding.bit sg c
    · simp only [hc, ↓reduceIte]
      exact congrArg qs.ket (flipBit_flipBit flag c)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
  unfold lowerCmpGeConst
  dsimp only
  apply evalL_sandwich5
  rw [evalL_lowerPrepareNegConst_ket_dirty, hdiff, hmid _ (reg_get_mem _ _),
    evalL_lowerPrepareNegConst_ket_dirty, hdiff]
  change qs.ket (if RegEncoding.bit (cmpSignQubit scratch h.scratch_positive)
        (cmpDiffBasis N data scratch h.scratch_can_grow b) = true
      then cmpDiffBasis N data scratch h.scratch_can_grow b
      else flipBit flag (cmpDiffBasis N data scratch h.scratch_can_grow b))
    = qs.ket (cmpDiffBasis N data scratch h.scratch_can_grow
        (if cmpDirtyToggle N data scratch flag h b = true then flipBit flag b else b))
  unfold cmpDirtyToggle
  cases hc : RegEncoding.bit (cmpSignQubit scratch h.scratch_positive)
      (cmpDiffBasis N data scratch h.scratch_can_grow b)
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    rw [cmpDiffBasis_flipBit N data scratch flag h]
  · simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]

/-- **D3, controlled subtraction, any input.** Under the static workspace record only, the
lowered controlled subtraction maps every basis ket `|b⟩` to `|b⟩` with `data.active`
overwritten by `csubDirtyValue` (= `data + p` mod `2^(data.width)`, `p` the value `scratch` holds
after the compute part); every other qubit is restored. -/
theorem evalL_lowerCSubConst_ket_dirty (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis) :
    LowerGateClass.evalL (lowerCSubConst N data scratch flag h) (qs.ket b)
      = qs.ket (RegEncoding.writeNat data.active
          (csubDirtyValue N data scratch flag h.scratch_can_grow b) b) := by
  have hprep : ∀ c : qs.Basis,
      LowerGateClass.evalL (LowGate.CNOT flag (constArithmeticUnitQubit scratch h.scratch_can_grow) ;;
        lowerCopyConstFromUnit N scratch (constArithmeticUnitQubit scratch h.scratch_can_grow) ;;
        LowGate.Negate scratch) (qs.ket c)
        = qs.ket (csubPrepBasis N scratch flag h.scratch_can_grow c) := fun c => by
    simp only [lowerCopyConstFromUnit, LowerGateClass.evalL_seq, LowerGateClass.evalL_CNOT_ket]
    rw [evalL_lowerCopyBitPowers_ket, LowerGateClass.evalL_negate_ket_total]
    rfl
  have hDS : ExtReg.ActiveDisjoint data scratch := ws_data_scratch_active h
  unfold lowerCSubConst
  dsimp only
  apply evalL_sandwich3
  rw [hprep, hprep, LowerGateClass.evalL_addScaled_ket_total, addScaledBasis_eq _ _ _ _ _ hDS,
    csubPrepBasis_writeNat N data scratch flag h]
  simp only [addScaledValue, extToInt_data_csubPrepBasis N data scratch flag h, csubDirtyValue]
  simp

/-- **Clean case recovered (comparator).** On clean workspace (`ConstArithmeticCleanBasis`) the
dirty toggle is the comparison `N ≤ data`. -/
theorem cmpDirtyToggle_of_clean (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis)
    (hclean : ConstArithmeticCleanBasis data scratch b) :
    cmpDirtyToggle N data scratch flag h b = decide (N ≤ RegEncoding.toNat data.active b) := by
  have he := (evalL_lowerCmpGeConst_ket_dirty (qs := qs) N data scratch flag h b).symm.trans
    (evalL_lowerCmpGeConst_ket N data scratch flag h b hclean)
  have hb := congrArg (RegEncoding.bit flag) (qs.ket_inj he)
  have hfd : flag ∉ data.active.qubits := not_mem_active h.flag_not_data
  simp only [cmpGeConstBasis, hfd, ↓reduceIte] at hb
  rw [bit_writeNat_qubitReg _ _ _ (by split_ifs <;> omega)] at hb
  cases ht : cmpDirtyToggle N data scratch flag h b <;>
    cases hf : RegEncoding.bit flag b <;>
    by_cases hN : N ≤ RegEncoding.toNat data.active b <;>
    simp_all [bit_flipBit_self]

/-- **Clean case recovered (subtraction).** On clean workspace the dirty closed form is the
high-level basis map `csubConstBasis`. -/
theorem csubDirty_of_clean (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis)
    (hclean : CSubConstCleanBasis N data scratch flag b) :
    RegEncoding.writeNat data.active (csubDirtyValue N data scratch flag h.scratch_can_grow b) b
      = csubConstBasis N data.active flag b := by
  exact qs.ket_inj ((evalL_lowerCSubConst_ket_dirty (qs := qs) N data scratch flag h b).symm.trans
    (evalL_lowerCSubConst_ket N data scratch flag h b hclean))

end D3

/-! ## N1: a dirty unit qubit breaks the lowered comparator -/

section N1

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]

/-- **N1 (proved negative).** Lowering correctness of the constant comparator FAILS when the
unit qubit `u` (the first reserve qubit of `scratch`, `constArithmeticUnitQubit`) is dirty.
Hypotheses: the static workspace record; a basis state `b` with `u` reading `1`, `scratch`
reading `0`, the reserve qubit of `data` clean, and `data < N`. Then the lowered circuit
toggles the flag (its prep clears `u`, copies nothing, and `0 + data ≥ 0`), while
`Gate.CmpGeConst` leaves the flag alone (`data < N`); the two output kets differ. -/
theorem lowerCmpGeConst_ne_of_unit_dirty (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) (b : qs.Basis)
    (hu : RegEncoding.bit (constArithmeticUnitQubit scratch h.scratch_can_grow) b = true)
    (hs : extToInt scratch b = 0) (hd : data.FreshFor 1 b)
    (hlt : RegEncoding.toNat data.active b < N) :
    LowerGateClass.evalL (lowerCmpGeConst N data scratch flag h) (qs.ket b)
      ≠ qs.eval (Gate.CmpGeConst N data scratch flag) (qs.ket b) := by
  have hfd : flag ∉ data.active.qubits := not_mem_active h.flag_not_data
  -- the lowered circuit toggles the flag
  have hw := h.scratch_positive
  have hdata : extToInt (data.grow 1) b = (RegEncoding.toNat data.active b : ℤ) := by
    rw [extToInt_grow_dirty data 1 b h.data_can_grow (by omega)]
    have h0 : RegEncoding.toNat (data.newBits 1) b = 0 := hd
    simp [h0, tcDecodeWidth, ExtReg.toNat]
  have hdlt : RegEncoding.toNat data.active b < 2 ^ (scratch.width - 1) := by
    have := RegEncoding.toNat_lt_ASize data.active b
    rw [ASize] at this
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) h.data_width_fits)
  have hfit : FitsSignedWidth scratch.width (RegEncoding.toNat data.active b : ℤ) := by
    refine ⟨hw, ?_, ?_⟩
    · simp only [signedMin]; push_cast; have : (0:ℤ) ≤ (2:ℤ) ^ (scratch.width - 1) := by positivity
      omega
    · simp only [signedMax]; exact_mod_cast hdlt
  have hzero : FitsSignedWidth scratch.width 0 := by
    refine ⟨hw, ?_, ?_⟩
    · simp only [signedMin]; push_cast; have : (0:ℤ) ≤ (2:ℤ) ^ (scratch.width - 1) := by positivity
      omega
    · simp only [signedMax]; positivity
  have htog : cmpDirtyToggle N data scratch flag h b = true := by
    rw [cmpDirtyToggle_iff, extToInt_cmpPrepBasis_of_unit_set N scratch _ b hu, hs, hdata,
      neg_zero, tcWrapInt_eq_of_fits hw hzero, zero_add, tcWrapInt_eq_of_fits hw hfit]
    positivity
  rw [evalL_lowerCmpGeConst_ket_dirty, htog, ModularArithmeticSemantics.eval_CmpGeConst_ket]
  intro he
  have hb := congrArg (RegEncoding.bit flag) (qs.ket_inj he)
  simp only [↓reduceIte, cmpGeConstBasis, hfd, Nat.not_le.mpr hlt, bit_flipBit_self] at hb
  rw [bit_writeNat_qubitReg _ _ _ (by split_ifs <;> omega)] at hb
  cases hf : RegEncoding.bit flag b <;> simp_all

end N1

/-! ## N2: the lowered QFT reads a reserve qubit -/

/-- A width-2 register: active qubits `[0, 1]`, reserve qubits `[2, 3]`. -/
def n2Reg : ExtReg := ⟨⟨[0, 1], by simp⟩, ⟨[2, 3], by simp⟩, by simp [Shor.Disjoint]⟩

/-- A policy with no bands has no table at any width. -/
theorem choose_none_of_bands_nil (P : ShorLoweringPolicy) (hP : P.bands = []) (n : ℕ) :
    P.choose n = none := by
  simp [ShorLoweringPolicy.choose, hP]

/-- A policy with no bands needs no phase-product reserve. -/
theorem reserveNeed_of_bands_nil (P : ShorLoweringPolicy) (hP : P.bands = []) (a c : ℕ) :
    Policy.reserveNeed P a c = (0, 0) := by
  rw [Policy.reserveNeed]
  simp [choose_none_of_bands_nil P hP]

/-- A width-2 QFT at a no-table policy needs one pool qubit on each side. -/
theorem qftWorkspaceNeed_two_of_bands_nil (P : ShorLoweringPolicy) (hP : P.bands = []) :
    Policy.qftWorkspaceNeed P 2 = (1, 1) := by
  simp [Policy.qftWorkspaceNeed, qftWorkspaceNeedOf, reserveNeed_of_bands_nil P hP]

/-- `n2Reg` satisfies the QFT reserve condition at every no-table policy, so N2 is not vacuous. -/
theorem n2Reg_reserveOK (P : ShorLoweringPolicy) (hP : P.bands = []) :
    Policy.QFTReserveOK P n2Reg := by
  constructor
  rw [show n2Reg.width = 2 from rfl, qftWorkspaceNeed_two_of_bands_nil P hP]
  decide

/-- The x-side pool of `n2Reg` is the qubit `2` (the first reserve qubit). -/
theorem qftXWork_n2Reg (P : ShorLoweringPolicy) (hP : P.bands = []) :
    (Policy.qftXWork P n2Reg).qubits = [2] := by
  show (n2Reg.reserve.take (Policy.qftWorkspaceNeed P n2Reg.width).1).qubits = [2]
  rw [show n2Reg.width = 2 from rfl, qftWorkspaceNeed_two_of_bands_nil P hP]
  rfl

/-- The z-side pool of `n2Reg` is the qubit `3`. -/
theorem qftZWork_n2Reg (P : ShorLoweringPolicy) (hP : P.bands = []) :
    (Policy.qftZWork P n2Reg).qubits = [3] := by
  show ((n2Reg.reserve.drop (Policy.qftWorkspaceNeed P n2Reg.width).1).take (Policy.qftWorkspaceNeed P n2Reg.width).2).qubits = [3]
  rw [show n2Reg.width = 2 from rfl, qftWorkspaceNeed_two_of_bands_nil P hP]
  rfl


/-- A register with exactly one qubit `q` reads `1` iff `q` is set. -/
theorem toNat_of_qubits_eq_singleton {B : Type*} [RegEncoding B] (R : Reg) {q : ℕ}
    (hR : R.qubits = [q]) (b : B) :
    RegEncoding.toNat R b = if RegEncoding.bit q b then 1 else 0 := by
  have hsz : regSize R = 1 := by simp [regSize, Reg.width, hR]
  have hlt : RegEncoding.toNat R b < 2 := by
    have := RegEncoding.toNat_lt_ASize R b; rwa [ASize, hsz] at this
  have hbit := RegEncoding.bit_eq_testBit_toNat R b ⟨0, by omega⟩
  have hget : R.get ⟨0, by simp [Reg.width, hR]⟩ = q := by simp [Reg.get, hR]
  erw [hget] at hbit
  rw [hbit]
  interval_cases RegEncoding.toNat R b <;> simp

/-- A one-qubit QFT plan lowers to one Hadamard. -/
theorem lowerQFTPlan_qftPlan_one (P : ShorLoweringPolicy) (r xW zW : Reg)
    (hw : Policy.QFTWorkspaceOK P r xW zW) (hone : regSize r = 1) :
    lowerQFTPlan (Policy.qftPlan P r xW zW hw) = LowGate.H (r.lowQubit (by omega)) := by
  rw [Policy.qftPlan]
  simp only [hone, ↓reduceDIte]
  rfl

section N2
variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs]

/-- A one-qubit lowered QFT commutes with `X` on any qubit outside its register. -/
theorem commXL_qftPlan_one (P : ShorLoweringPolicy) (r xW zW : Reg)
    (hw : Policy.QFTWorkspaceOK P r xW zW) (hone : regSize r = 1) {q : ℕ} (hq : q ∉ r.qubits) :
    CommXL qs (lowerQFTPlan (Policy.qftPlan P r xW zW hw)) q := by
  rw [lowerQFTPlan_qftPlan_one P r xW zW hw hone]
  exact commXL_H fun e => hq (e ▸ List.get_mem _ _)

/-- If a sandwich `A ;; D ;; B ;; C` commutes with `X q` and `A`, `B`, `C` do, then `D` does. -/
theorem commXL_of_commXL_seq4 {A D B C : LowGate} {q : ℕ}
    (h : CommXL qs (A ;; D ;; B ;; C) q) (hA : CommXL qs A q) (hB : CommXL qs B q)
    (hC : CommXL qs C q) : CommXL qs D q := by
  intro ψ
  have hinjC : Function.Injective (LowerGateClass.evalL (qs := qs) C) := fun a c e => by
    have := congrArg (LowerGateClass.evalL (qs := qs) (LowGate.adj C)) e
    rwa [LowerGateClass.evalL_adj_apply, LowerGateClass.evalL_adj_apply] at this
  have hinjB : Function.Injective (LowerGateClass.evalL (qs := qs) B) := fun a c e => by
    have := congrArg (LowerGateClass.evalL (qs := qs) (LowGate.adj B)) e
    rwa [LowerGateClass.evalL_adj_apply, LowerGateClass.evalL_adj_apply] at this
  set φ := LowerGateClass.evalL (qs := qs) (LowGate.adj A) ψ
  have hψ : LowerGateClass.evalL (qs := qs) A φ = ψ := evalL_apply_adj A ψ
  have h1 := h φ
  simp only [LowerGateClass.evalL_seq] at h1
  rw [hA, hψ, ← hC, ← hB] at h1
  exact hinjB (hinjC h1)

/-- A diagonal low gate that commutes with `X q` has a phase invariant under flipping `q`. -/
theorem phase_flip_eq_of_commXL {L : LowGate} {q : ℕ} (c : qs.Basis → ℂ)
    (hL : ∀ b, LowerGateClass.evalL L (qs.ket b) = c b • qs.ket b)
    (h : CommXL qs L q) (b : qs.Basis) : c (flipBit q b) = c b := by
  have e := h (qs.ket b)
  rw [evalL_X_ket_flipBit, hL, hL, LowerGateClass.evalL_smul, evalL_X_ket_flipBit] at e
  have e2 : (c (flipBit q b) - c b) • qs.ket (flipBit q b) = 0 := by rw [sub_smul, e, sub_self]
  rcases smul_eq_zero.mp e2 with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (qs.ket_ne_zero _)

/-- **N2 (proved negative).** At any policy with no table (`P.bands = []`), the lowered QFT of the
width-2 register `n2Reg` (active `[0, 1]`, reserve `[2, 3]`) does NOT commute with `X` on qubit
`2`, the first qubit of its x-side pool `Policy.qftXWork P n2Reg` (`qftXWork_n2Reg`). The
reserve condition `h` is satisfiable (`n2Reg_reserveOK`). Contrast: the high-level `Gate.QFT`
commutes with `X` on every qubit outside `r.active` (`commX_QFT`). Not claimed here: the same
for other widths, other pool qubits, or policies with tables (expected, not proved). -/
theorem lowerQFT_not_commXL_pool (P : ShorLoweringPolicy) (hP : P.bands = [])
    (h : Policy.QFTReserveOK P n2Reg) : ¬ CommXL qs (Policy.lowerQFT P n2Reg h) 2 := by
  intro hc
  have hw := h.explicitWorkspace
  have hlarge : 2 ≤ regSize n2Reg.active := by decide
  set ws := hw.phaseWorkspace hlarge with hws
  have hp : Policy.lowerQFT P n2Reg h
      = (lowerQFTPlan (Policy.qftPlan P (rightReg n2Reg.active) _ _ (hw.right hlarge)) ;;
          lowerGateRec (Policy.phaseProdUsingPlan P (qftPhi (regSize n2Reg.active)) ws) ;;
          lowerQFTPlan (Policy.qftPlan P (leftReg n2Reg.active) _ _ (hw.left hlarge)) ;;
          LowGate.RadixReverse n2Reg.active (regSize n2Reg.active / 2)) := by
    unfold Policy.lowerQFT Policy.reserveQftPlan
    rw [Policy.qftPlan]
    simp only [show regSize n2Reg.active ≠ 0 by decide, show regSize n2Reg.active ≠ 1 by decide,
      ↓reduceDIte]
    rfl
  rw [hp] at hc
  have hD := commXL_of_commXL_seq4 hc (commXL_qftPlan_one _ _ _ _ _ (by decide) (by decide))
    (commXL_qftPlan_one _ _ _ _ _ (by decide) (by decide)) (lowGate_commX _ (by decide))
  have hstop : P.choose (phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1)) = none :=
    choose_none_of_bands_nil P hP _
  have hPh : lowerGateRec (Policy.phaseProdUsingPlan P (qftPhi (regSize n2Reg.active)) ws)
      = (LowGate.zeroExtend ws.xExt 1 ;; LowGate.zeroExtend ws.zExt 1 ;;
          LowGate.Naive_SignedPhaseProd (qftPhi (regSize n2Reg.active)) (ws.xExt.grow 1)
            (ws.zExt.grow 1) ;;
          LowGate.zeroDealloc ws.zExt 1 ;; LowGate.zeroDealloc ws.xExt 1) := by
    rw [← Policy.lowerSignedPhaseProd_eq_naive_of_stop P _ _ _ hstop]; rfl
  rw [hPh] at hD
  let c : qs.Basis → ℂ := fun b => Complex.exp
    (((Angle.toReal (qftPhi (regSize n2Reg.active)) : ℝ) : ℂ) * Complex.I *
      (((extToInt (ws.xExt.grow 1) b : ℤ) : ℂ) * (((extToInt (ws.zExt.grow 1) b : ℤ) : ℂ))))
  have hdiag : ∀ b, LowerGateClass.evalL (LowGate.zeroExtend ws.xExt 1 ;;
      LowGate.zeroExtend ws.zExt 1 ;;
      LowGate.Naive_SignedPhaseProd (qftPhi (regSize n2Reg.active)) (ws.xExt.grow 1)
        (ws.zExt.grow 1) ;;
      LowGate.zeroDealloc ws.zExt 1 ;; LowGate.zeroDealloc ws.xExt 1) (qs.ket b) = c b • qs.ket b :=
    fun b => by
      simp only [LowerGateClass.evalL_seq, LowerGateClass.evalL_zeroExtend_id,
        LowerGateClass.evalL_zeroDealloc_id, LowerGateClass.evalL_naive_signedPhaseProd_ket, c]
  have hX : ∀ b : qs.Basis, extToInt (ws.xExt.grow 1) b
      = (if RegEncoding.bit 0 b then 1 else 0) + 2 * tcDecodeWidth 1 (if RegEncoding.bit 2 b then 1 else 0) := by
    intro b
    rw [extToInt_grow_dirty _ 1 b (by simp) (by omega)]
    rw [show ws.xExt.width = 1 from (show regSize (leftReg n2Reg.active) = 1 by decide),
      ExtReg.toNat,
      toNat_of_qubits_eq_singleton ws.xExt.active (q := 0)
        (show (leftReg n2Reg.active).qubits = [0] by decide),
      toNat_of_qubits_eq_singleton (ws.xExt.newBits 1) (q := 2)
        (by show ((Policy.qftXWork P n2Reg).take 1).qubits = [2]
            simp [Reg.take, qftXWork_n2Reg P hP])]
    push_cast; split_ifs <;> simp
  have hZ : ∀ b : qs.Basis, extToInt (ws.zExt.grow 1) b
      = (if RegEncoding.bit 1 b then 1 else 0) + 2 * tcDecodeWidth 1 (if RegEncoding.bit 3 b then 1 else 0) := by
    intro b
    rw [extToInt_grow_dirty _ 1 b (by simp) (by omega)]
    rw [show ws.zExt.width = 1 from (show regSize (rightReg n2Reg.active) = 1 by decide),
      ExtReg.toNat,
      toNat_of_qubits_eq_singleton ws.zExt.active (q := 1)
        (show (rightReg n2Reg.active).qubits = [1] by decide),
      toNat_of_qubits_eq_singleton (ws.zExt.newBits 1) (q := 3)
        (by show ((Policy.qftZWork P n2Reg).take 1).qubits = [3]
            simp [Reg.take, qftZWork_n2Reg P hP])]
    push_cast; split_ifs <;> simp
  have key := phase_flip_eq_of_commXL c hdiag hD (flipBit 1 RegEncoding.zero)
  simp only [c, hX, hZ, bit_flipBit, RegEncoding.bit_zero] at key
  norm_num [tcDecodeWidth, Angle.toReal, qftPhi, show regSize n2Reg.active = 2 from rfl] at key
  rw [show -(1 / 2 * (Real.pi : ℂ) * Complex.I * 2) = -((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_neg, Complex.exp_pi_mul_I] at key
  norm_num at key

end N2

section N2ket

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]

/-- **N2, ket-level form.** At any policy with no table and the register `n2Reg`, there is a
basis ket with a dirty pool qubit (qubit `2` or qubit `3` set) on which the lowered QFT and the
high-level `Gate.QFT n2Reg` give different states. (On kets with both pool qubits clean they
agree: `Policy.lowerQFT_correct`.) Not claimed: which of the two pool qubits must be dirty; in
particular a witness with ONLY qubit `2` dirty is not exhibited. -/
theorem lowerQFT_ne_QFT_dirty_pool (P : ShorLoweringPolicy) (hP : P.bands = [])
    (h : Policy.QFTReserveOK P n2Reg) :
    ∃ b : qs.Basis, (RegEncoding.bit 2 b = true ∨ RegEncoding.bit 3 b = true) ∧
      LowerGateClass.evalL (Policy.lowerQFT P n2Reg h) (qs.ket b)
        ≠ qs.eval (Gate.QFT n2Reg) (qs.ket b) := by
  by_contra hne
  push Not at hne
  have hAdm : P.Admissible := fun b hb => by simp [hP] at hb
  have hall : ∀ b : qs.Basis, LowerGateClass.evalL (Policy.lowerQFT P n2Reg h) (qs.ket b)
      = qs.eval (Gate.QFT n2Reg) (qs.ket b) := by
    intro b
    by_cases hd : RegEncoding.bit 2 b = true ∨ RegEncoding.bit 3 b = true
    · exact hne b hd
    · push Not at hd
      have h2 : RegEncoding.bit 2 b = false := by simpa using hd.1
      have h3 : RegEncoding.bit 3 b = false := by simpa using hd.2
      have hx : FreshZero (Policy.qftXWork P n2Reg) b := by
        unfold FreshZero
        rw [toNat_of_qubits_eq_singleton _ (qftXWork_n2Reg P hP) b, h2]; rfl
      have hz : FreshZero (Policy.qftZWork P n2Reg) b := by
        unfold FreshZero
        rw [toNat_of_qubits_eq_singleton _ (qftZWork_n2Reg P hP) b, h3]; rfl
      exact Policy.lowerQFT_correct qs P n2Reg (qs.ket b) ⟨h, CleanClosure.ket b ⟨hx, hz⟩⟩ hAdm
  have hstate := evalL_eq_eval_of_ket (qs := qs) _ _ hall
  have hX : ∀ ψ : qs.State, LowerGateClass.evalL (LowGate.X 2) ψ = qs.eval (Gate.X 2) ψ :=
    evalL_eq_eval_of_ket _ _ fun b => by rw [evalL_X_ket_flipBit, eval_X_ket_flipBit]
  apply lowerQFT_not_commXL_pool (qs := qs) P hP h
  intro ψ
  calc LowerGateClass.evalL (Policy.lowerQFT P n2Reg h) (LowerGateClass.evalL (LowGate.X 2) ψ)
      = qs.eval (Gate.QFT n2Reg) (qs.eval (Gate.X 2) ψ) := by rw [hstate, hX]
    _ = qs.eval (Gate.X 2) (qs.eval (Gate.QFT n2Reg) ψ) := commX_QFT (by decide) ψ
    _ = LowerGateClass.evalL (LowGate.X 2) (LowerGateClass.evalL (Policy.lowerQFT P n2Reg h) ψ) := by
        rw [hstate, hX]

end N2ket

end Dirty
end Shor
