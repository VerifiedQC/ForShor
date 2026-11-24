import ForShor.ShorVerification.Implementation.Readout.Proofs.Locality

/-!
# Readout: unnamed qubits are spectators (commutation with Z projectors)

`Proofs/Locality.lean` shows that a program commutes with `X q` on every qubit `q` it does
not name. Here the second half of the spectator statement: it also commutes with the Z-basis
Born projectors `measProj (qubitReg q) o` of such a qubit. Together they say the program acts
as `(something) ⊗ 1` on qubit `q` in the computational basis, in the only form the abstract
classes can express it.

* `gate_commP`: a gate with no `idealCtrlModMul` node and `q ∉ U.qubitSupport` commutes with
  `measProj (qubitReg q) o`, on every state. Per constructor: every basis map writes only
  registers that do not contain `q`, so it keeps bit `q` (`bit_cnotBasis_of_ne`, …); `H`, `QFT`
  produce kets that keep bit `q`; the phase products are diagonal (they commute with every
  Z projector, whatever qubits they name); `adj` by invertibility.
* `MGate.eval_commProj`: the same for `MGate` programs, branch by branch (Born projectors of
  two one-qubit registers commute, `measProj_commProj`; the phase of `ffPhase` is diagonal;
  the reset `X p`, `p ≠ q`, keeps bit `q`).
* Linearity of the branching semantics: `MGate.eval_add`, `MGate.eval_smul`.
* Corollaries for a start state `ψ₀`:
  - `MGate.recordProb_decomp`: the record probabilities of `ψ₀` are the sum over `o ∈ {0,1}`
    of those of `measProj (qubitReg q) o ψ₀` (orthogonal pieces);
  - `MGate.recordProb_superpose`: for ANY `α β : ℂ` and ANY basis state `b`, starting in
    `α|b⟩ + β|b with q flipped⟩` gives every record the probability
    `(‖α‖² + ‖β‖²) · (its probability from |b⟩)`. Normalised (`‖α‖² + ‖β‖² = 1`): the record
    distribution does not see a spectator in superposition (`MGate.recordProb_superpose_unit`).

Hypotheses throughout: `P.NoIdeal` and `q ∉ P.qubitSupport`, as in `Proofs/Locality.lean` (the ideal multiplier's
ket law holds only on `data < N`, see `Proofs/Locality.lean`). No new axiom or class field. Adjoints need no extra law here
either: they follow from invertibility (`GateSemanticsCore.eval_apply_adj`).
-/

namespace Shor
namespace Readout

open MeasureClass

/-! ## Basis maps keep every bit they do not write -/

section Bits
variable {B : Type*} [RegEncoding B]

theorem bit_cnotBasis_of_ne {a t q : ℕ} (ht : q ≠ t) (b : B) :
    RegEncoding.bit q (cnotBasis a t b) = RegEncoding.bit q b := by
  unfold cnotBasis
  split_ifs <;> first | rfl | exact RegEncoding.bit_writeNat_out _ _ _ _ (not_mem_qubitReg.mpr ht)

theorem bit_toffoliBasis_of_ne {a a' t q : ℕ} (ht : q ≠ t) (b : B) :
    RegEncoding.bit q (toffoliBasis a a' t b) = RegEncoding.bit q b := by
  unfold toffoliBasis
  split_ifs <;> first | rfl | exact RegEncoding.bit_writeNat_out _ _ _ _ (not_mem_qubitReg.mpr ht)

theorem bit_cmpGeConstBasis_of_ne {N : ℕ} {d : Reg} {f q : ℕ} (hf : q ≠ f) (b : B) :
    RegEncoding.bit q (cmpGeConstBasis N d f b) = RegEncoding.bit q b := by
  unfold cmpGeConstBasis
  split_ifs <;> first | rfl | exact RegEncoding.bit_writeNat_out _ _ _ _ (not_mem_qubitReg.mpr hf)

theorem bit_csubConstBasis_of_not_mem {N : ℕ} {d : Reg} {f q : ℕ} (hd : q ∉ d.qubits) (b : B) :
    RegEncoding.bit q (csubConstBasis N d f b) = RegEncoding.bit q b := by
  unfold csubConstBasis
  split_ifs <;> first | rfl | exact RegEncoding.bit_writeNat_out _ _ _ _ hd

theorem bit_shiftLBasis_of_not_mem {r : ExtReg} {n q : ℕ} (h : q ∉ r.active.qubits) (b : B) :
    RegEncoding.bit q (shiftLBasis r n b) = RegEncoding.bit q b := by
  unfold shiftLBasis shiftLBasisRaw
  dsimp only
  split_ifs <;> exact RegEncoding.bit_writeNat_out _ _ _ _ h

theorem bit_shiftRBasis_of_not_mem {r : ExtReg} {n q : ℕ} (h : q ∉ r.active.qubits) (b : B) :
    RegEncoding.bit q (shiftRBasis r n b) = RegEncoding.bit q b := by
  unfold shiftRBasis shiftRBasisRaw
  split_ifs <;> exact RegEncoding.bit_writeNat_out _ _ _ _ h

theorem bit_negateBasis_of_not_mem {r : ExtReg} {q : ℕ} (h : q ∉ r.active.qubits) (b : B) :
    RegEncoding.bit q (negateBasis r b) = RegEncoding.bit q b :=
  RegEncoding.bit_writeNat_out _ _ _ _ h

theorem bit_addScaledBasis_of_not_mem {d s : ExtReg} {neg : Bool} {sh q : ℕ}
    (h : q ∉ d.active.qubits) (b : B) :
    RegEncoding.bit q (addScaledBasis d s neg sh b) = RegEncoding.bit q b := by
  unfold addScaledBasis
  split_ifs <;> first | rfl | exact RegEncoding.bit_writeNat_out _ _ _ _ h

theorem bit_signExtendBasis_of_not_mem {r : ExtReg} {n q : ℕ} (h : q ∉ r.ownedQubits) (b : B) :
    RegEncoding.bit q (signExtendBasis r n b) = RegEncoding.bit q b :=
  RegEncoding.bit_writeNat_out _ _ _ _ fun h' => not_mem_reserve h (List.mem_of_mem_take h')

theorem bit_radixReverseBasis_of_not_mem {r : Reg} {m q : ℕ} (h : q ∉ r.qubits) (b : B) :
    RegEncoding.bit q (radixReverseBasis r m b) = RegEncoding.bit q b := by
  unfold radixReverseBasis
  split_ifs <;> first | rfl | exact RegEncoding.bit_writeNat_out _ _ _ _ h

end Bits

/-! ## Gates commute with the Z projectors of every unnamed qubit -/

section Gates
variable {qs : QSemantics} [RegEncoding qs.Basis]

/-- `eval U` commutes with the Born projector `measProj (qubitReg q) o` on every state. -/
def CommP (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] [MeasureClass qs]
    (U : Gate) (q o : ℕ) : Prop :=
  ∀ ψ : qs.State, qs.eval U (measProj (qubitReg q) o ψ) = measProj (qubitReg q) o (qs.eval U ψ)

variable [GateSemanticsFacts qs] [MeasureClass qs]

omit [GateSemanticsFacts qs] in
/-- The projector on a ket whose bit `q` equals that of `b`. -/
theorem measProj_ket_keep {q o : ℕ} {x b : qs.Basis}
    (h : RegEncoding.bit q x = RegEncoding.bit q b) :
    measProj (qubitReg q) o (qs.ket x)
      = if (if RegEncoding.bit q b then 1 else 0) = o then qs.ket x else 0 := by
  rw [measProj_qubitReg_ket, h]

/-- A gate whose image of `|b⟩` lies in the bit-`q`-equals-`bit q b` subspace commutes with
`measProj (qubitReg q) o`. -/
theorem commP_of_ket {U : Gate} {q o : ℕ}
    (h : ∀ b, measProj (qubitReg q) o (qs.eval U (qs.ket b))
      = if (if RegEncoding.bit q b then 1 else 0) = o then qs.eval U (qs.ket b) else 0) :
    CommP qs U q o := by
  intro ψ
  have := linearMap_ext_ket ((gateL U).comp (measProj (qubitReg q) o).toLinearMap)
    ((measProj (qubitReg q) o).toLinearMap.comp (gateL U)) (fun b => by
      simp only [LinearMap.comp_apply, gateL_apply, ContinuousLinearMap.coe_coe]
      rw [h b, measProj_qubitReg_ket]
      split_ifs <;> simp [MGate.gate_eval_zero_state]) ψ
  simpa using this

theorem commP_of_basis {U : Gate} {q o : ℕ} (f : qs.Basis → qs.Basis)
    (hU : ∀ b, qs.eval U (qs.ket b) = qs.ket (f b))
    (hf : ∀ b, RegEncoding.bit q (f b) = RegEncoding.bit q b) : CommP qs U q o :=
  commP_of_ket fun b => by rw [hU, measProj_ket_keep (hf b)]

/-- Diagonal gates commute with every Z projector. -/
theorem commP_of_diag {U : Gate} {q o : ℕ} (s : qs.Basis → ℂ)
    (hU : ∀ b, qs.eval U (qs.ket b) = s b • qs.ket b) : CommP qs U q o :=
  commP_of_ket fun b => by
    rw [hU, map_smul, measProj_qubitReg_ket]
    split_ifs <;> simp

theorem commP_id (q o : ℕ) : CommP qs Gate.id q o := fun ψ => by
  simp only [QSemantics.eval, GateSemanticsCore.eval_id]

theorem commP_seq {U V : Gate} {q o : ℕ} (hU : CommP qs U q o) (hV : CommP qs V q o) :
    CommP qs (U ;; V) q o := fun ψ => by
  unfold CommP at hU hV
  simp only [QSemantics.eval, GateSemanticsCore.eval_seq] at hU hV ⊢
  rw [hU, hV]

theorem commP_adj {U : Gate} {q o : ℕ} (hU : CommP qs U q o) : CommP qs (Gate.adj U) q o :=
  fun ψ => by
    have h1 := gate_eval_apply_adj U ψ
    conv_lhs => rw [← h1]
    rw [← hU, QSemantics.eval, GateSemanticsCore.eval_adj_apply]

theorem commP_H {p q o : ℕ} (h : q ≠ p) : CommP qs (Gate.H p) q o := commP_of_ket fun b => by
  have hw : ∀ v, RegEncoding.bit q (RegEncoding.writeNat (qubitReg p) v b) = RegEncoding.bit q b :=
    fun v => RegEncoding.bit_writeNat_out _ _ _ _ (not_mem_qubitReg.mpr h)
  rw [HadamardSemantics.eval_H_ket, map_smul, map_add, map_smul, measProj_ket_keep (hw 0),
    measProj_ket_keep (hw 1)]
  split_ifs <;> simp

theorem commP_QFT {r : ExtReg} {q o : ℕ} (h : q ∉ r.active.qubits) : CommP qs (Gate.QFT r) q o :=
  commP_of_ket fun b => by
    have hw : ∀ v, RegEncoding.bit q (RegEncoding.writeNat r.active v b) = RegEncoding.bit q b :=
      fun v => RegEncoding.bit_writeNat_out _ _ _ _ h
    rw [QFTSemantics.eval_QFT_ket, map_smul, map_sum]
    simp only [map_smul, measProj_ket_keep (hw _)]
    split_ifs <;> simp

/-- **Per-primitive spectator law, all states.** A gate with no `idealCtrlModMul` node
commutes with the Born projectors `measProj (qubitReg q) o` of every qubit `q` it does not
name. -/
theorem gate_commP (U : Gate) (hU : U.NoIdeal) {q : ℕ} (hq : q ∉ U.qubitSupport) (o : ℕ) :
    CommP qs U q o := by
  induction U with
  | id => exact commP_id q o
  | seq U V ihU ihV =>
    simp only [Gate.qubitSupport, Set.mem_union, not_or] at hq
    exact commP_seq (ihU hU.1 hq.1) (ihV hU.2 hq.2)
  | adj U ih => exact commP_adj (ih hU hq)
  | H p => exact commP_H (by simpa [Gate.qubitSupport] using hq)
  | X p =>
    exact commP_of_basis (flipBit p) (fun b => eval_X_ket_flipBit p b)
      (bit_flipBit_ne (by simpa [Gate.qubitSupport] using hq))
  | CNOT a t =>
    simp only [Gate.qubitSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commP_of_basis _ (ClassicalReversibleSemantics.eval_CNOT_ket a t)
      (bit_cnotBasis_of_ne hq.2)
  | Toffoli a a' t =>
    simp only [Gate.qubitSupport, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
    exact commP_of_basis _ (ClassicalReversibleSemantics.eval_Toffoli_ket a a' t)
      (bit_toffoliBasis_of_ne hq.2.2)
  | QFT r => exact commP_QFT (not_mem_active (by simpa [Gate.qubitSupport] using hq))
  | RadixReverse r m =>
    exact commP_of_basis _ (RadixReverseSemantics.eval_RadixReverse_ket_total r m)
      (bit_radixReverseBasis_of_not_mem (by simpa [Gate.qubitSupport] using hq))
  | SignedPhaseProd phi x z =>
    exact commP_of_diag _ (PhaseSemantics.eval_SignedPhaseProd_ket phi x z)
  | CSignedPhaseProd ctrl phi x z =>
    refine commP_of_diag (fun b => if RegEncoding.bit ctrl b then
      Complex.exp (((Angle.toReal phi : ℝ) : ℂ) * Complex.I *
        (((extToInt x b : ℤ) : ℂ) * (((extToInt z b : ℤ) : ℂ)))) else 1) fun b => ?_
    rw [PhaseSemantics.eval_CSignedPhaseProd_ket]
    split_ifs <;> simp
  | CmpGeConst N d s f =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ModularArithmeticSemantics.eval_CmpGeConst_ket N d s f)
      (bit_cmpGeConstBasis_of_ne hq.2.2)
  | CSubConst N d s f =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ModularArithmeticSemantics.eval_CSubConst_ket N d s f)
      (bit_csubConstBasis_of_not_mem (not_mem_active hq.1))
  | ShiftL r n =>
    exact commP_of_basis _ (ArithmeticSemantics.eval_ShiftL_ket_total r n)
      (bit_shiftLBasis_of_not_mem (not_mem_active (by simpa [Gate.qubitSupport] using hq)))
  | ShiftR r n =>
    exact commP_of_basis _ (ArithmeticSemantics.eval_ShiftR_ket_total r n)
      (bit_shiftRBasis_of_not_mem (not_mem_active (by simpa [Gate.qubitSupport] using hq)))
  | Negate r =>
    exact commP_of_basis _ (ArithmeticSemantics.eval_Negate_ket_total r)
      (bit_negateBasis_of_not_mem (not_mem_active (by simpa [Gate.qubitSupport] using hq)))
  | AddScaled d s neg sh =>
    simp only [Gate.qubitSupport, Set.mem_ofPred_eq, not_or] at hq
    exact commP_of_basis _ (ArithmeticSemantics.eval_AddScaled_ket_total d s neg sh)
      (bit_addScaledBasis_of_not_mem (not_mem_active hq.1))
  | zeroExtend r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroExtend, ExtensionSemantics.eval_zeroExtend]
  | signExtend r n =>
    exact commP_of_basis _ (ExtensionSemantics.eval_signExtend_ket_total r n)
      (bit_signExtendBasis_of_not_mem (by simpa [Gate.qubitSupport] using hq))
  | zeroDealloc r n =>
    intro ψ
    rw [ExtensionSemantics.eval_zeroDealloc, ExtensionSemantics.eval_zeroDealloc]
  | signDealloc r n =>
    exact commP_of_basis _ (ExtensionSemantics.eval_signDealloc_ket_total r n)
      (bit_signExtendBasis_of_not_mem (by simpa [Gate.qubitSupport] using hq))
  | idealCtrlModMul _ _ _ _ => exact hU.elim

end Gates

/-! ## Measurement programs -/

section MGates
variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

omit [GateSemanticsFacts qs] [LowerGateClass qs] in
/-- Born projectors of two one-qubit registers commute. -/
theorem measProj_commProj (p q o o' : ℕ) (ψ : qs.State) :
    measProj (qubitReg p) o' (measProj (qubitReg q) o ψ)
      = measProj (qubitReg q) o (measProj (qubitReg p) o' ψ) := by
  have := linearMap_ext_ket
    ((measProj (qubitReg p) o').toLinearMap.comp (measProj (qubitReg q) o).toLinearMap)
    ((measProj (qubitReg q) o).toLinearMap.comp (measProj (qubitReg p) o').toLinearMap)
    (fun b => by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [measProj_qubitReg_ket q o b, measProj_qubitReg_ket p o' b]
      by_cases h1 : (if RegEncoding.bit q b then 1 else 0) = o <;>
        by_cases h2 : (if RegEncoding.bit p b then 1 else 0) = o' <;>
        simp only [h1, h2, ↓reduceIte, map_zero, measProj_qubitReg_ket]) ψ
  simpa using this

omit [GateSemanticsFacts qs] [MeasureClass qs] in
theorem evalL_Phase_ket_diag (p : ℕ) (θ : Angle) (b : qs.Basis) :
    LowerGateClass.evalL (LowGate.Phase p θ) (qs.ket b)
      = (if RegEncoding.bit p b then Complex.exp (((Angle.toReal θ : ℝ) : ℂ) * Complex.I)
          else 1) • qs.ket b := by
  rw [LowerGateClass.evalL_Phase_ket]
  split_ifs <;> simp

omit [GateSemanticsFacts qs] in
/-- The phase of `ffPhase` is diagonal, so it commutes with every Z projector. -/
theorem phase_commProj (p q o : ℕ) (θ : Angle) (ψ : qs.State) :
    LowerGateClass.evalL (LowGate.Phase p θ) (measProj (qubitReg q) o ψ)
      = measProj (qubitReg q) o (LowerGateClass.evalL (LowGate.Phase p θ) ψ) := by
  have := linearMap_ext_ket ((lowL (LowGate.Phase p θ)).comp (measProj (qubitReg q) o).toLinearMap)
    ((measProj (qubitReg q) o).toLinearMap.comp (lowL (LowGate.Phase p θ))) (fun b => by
      simp only [LinearMap.comp_apply, lowL_apply, ContinuousLinearMap.coe_coe]
      rw [measProj_qubitReg_ket]
      conv_rhs => rw [evalL_Phase_ket_diag, map_smul, measProj_qubitReg_ket]
      by_cases hc : (if RegEncoding.bit q b then 1 else 0) = o
      · simp only [hc, ↓reduceIte, evalL_Phase_ket_diag]
      · simp only [hc, ↓reduceIte, MGate.lowGate_evalL_zero_state, smul_zero]) ψ
  simpa using this

omit [LowerGateClass qs] in
/-- Both children of `measureReset p`, `p ≠ q`, commute with `measProj (qubitReg q) o`. -/
theorem measureResetBranch_commProj {p q : ℕ} (h : q ≠ p) (o : ℕ) (c : Bool) (ψ : qs.State) :
    measureResetBranch p c (measProj (qubitReg q) o ψ)
      = measProj (qubitReg q) o (measureResetBranch p c ψ) := by
  cases c
  · exact measProj_commProj p q o 0 ψ
  · simp only [measureResetBranch, ite_true]
    rw [measProj_commProj p q o 1 ψ]
    exact commP_of_basis (flipBit p) (fun b => eval_X_ket_flipBit p b) (bit_flipBit_ne h) _

/-- **Spectator law for `MGate` programs, branch by branch.** If `P.NoIdeal` and
`q ∉ P.qubitSupport`, running `P` on the branchwise projection `measProj (qubitReg q) o ψ`
gives the projection of the run on `ψ`, branch by branch. -/
theorem MGate.eval_commProj (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.qubitSupport)
    (o : ℕ) (ψ : MState qs) :
    P.eval (fun r => measProj (qubitReg q) o (ψ r))
      = fun r => measProj (qubitReg q) o (P.eval ψ r) := by
  induction P generalizing ψ with
  | unitary g =>
    funext r
    exact gate_commP g hP hq o (ψ r)
  | seq a b iha ihb =>
    simp only [MGate.qubitSupport, Set.mem_union, not_or] at hq
    simp only [MGate.eval_seq]
    rw [iha hP.1 hq.1, ihb hP.2 hq.2]
  | measureReset p =>
    have hp : q ≠ p := by simpa [MGate.qubitSupport] using hq
    funext r
    simp only [MGate.eval]
    split
    · simp
    · exact measureResetBranch_commProj hp o _ _
  | ffPhase p j =>
    funext r
    exact phase_commProj p q o _ _

/-! ### Linearity of the branching semantics -/

omit [LowerGateClass qs] in
theorem measureResetBranch_add_loc (p : ℕ) (c : Bool) (φ χ : qs.State) :
    measureResetBranch p c (φ + χ) = measureResetBranch p c φ + measureResetBranch p c χ := by
  cases c <;> simp [measureResetBranch, map_add, gate_eval_add]

omit [LowerGateClass qs] in
theorem measureResetBranch_smul_loc (p : ℕ) (c : Bool) (a : ℂ) (φ : qs.State) :
    measureResetBranch p c (a • φ) = a • measureResetBranch p c φ := by
  cases c <;> simp [measureResetBranch, map_smul, gate_eval_smul]

/-- `MGate.eval` is additive (branchwise sum of branching states). -/
theorem MGate.eval_add (P : MGate) (ψ φ : MState qs) : P.eval (ψ + φ) = P.eval ψ + P.eval φ := by
  induction P generalizing ψ φ with
  | unitary g => funext r; exact gate_eval_add g (ψ r) (φ r)
  | seq a b iha ihb => simp only [MGate.eval_seq]; rw [iha, ihb]
  | measureReset p =>
    funext r
    simp only [MGate.eval, Pi.add_apply]
    split
    · simp
    · exact measureResetBranch_add_loc p _ _ _
  | ffPhase p j => funext r; exact LowerGateClass.evalL_add _ (ψ r) (φ r)

/-- `MGate.eval` is homogeneous. -/
theorem MGate.eval_smul (P : MGate) (a : ℂ) (ψ : MState qs) : P.eval (a • ψ) = a • P.eval ψ := by
  induction P generalizing ψ with
  | unitary g => funext r; exact gate_eval_smul g a (ψ r)
  | seq a' b iha ihb => simp only [MGate.eval_seq]; rw [iha, ihb]
  | measureReset p =>
    funext r
    simp only [MGate.eval, Pi.smul_apply]
    split
    · simp
    · exact measureResetBranch_smul_loc p _ a _
  | ffPhase p j => funext r; exact LowerGateClass.evalL_smul _ a (ψ r)

omit [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
theorem MState.init_add (ψ φ : qs.State) :
    MState.init (ψ + φ) = MState.init ψ + MState.init φ := by
  funext r; unfold MState.init; split <;> simp_all

omit [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
theorem MState.init_smul (a : ℂ) (ψ : qs.State) : MState.init (a • ψ) = a • MState.init ψ := by
  funext r; unfold MState.init; split <;> simp_all

omit [GateSemanticsFacts qs] [LowerGateClass qs] in
theorem MState.init_proj (q o : ℕ) (ψ₀ : qs.State) :
    MState.init (measProj (qubitReg q) o ψ₀) = fun r => measProj (qubitReg q) o (MState.init ψ₀ r) := by
  funext r; unfold MState.init; split <;> simp

/-! ### Corollaries -/

/-- Projection of the start state is projection of every branch. -/
theorem MGate.eval_init_proj (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.qubitSupport)
    (o : ℕ) (ψ₀ : qs.State) (r : Record) :
    P.eval (MState.init (measProj (qubitReg q) o ψ₀)) r
      = measProj (qubitReg q) o (P.eval (MState.init ψ₀) r) := by
  rw [MState.init_proj, MGate.eval_commProj P hP hq]

/-- **Decomposition.** The record probabilities of a start state are the sums of those of its
two Z-projections on an unnamed qubit `q`. -/
theorem MGate.recordProb_decomp (P : MGate) (hP : P.NoIdeal) {q : ℕ} (hq : q ∉ P.qubitSupport)
    (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init ψ₀)) r
      = ∑ o ∈ Finset.range 2,
          recordProb (P.eval (MState.init (measProj (qubitReg q) o ψ₀))) r := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, recordProb,
    MGate.eval_init_proj P hP hq]
  exact (probMeas_qubitReg_zero_add_one q _).symm

/-- Scaling the start state scales every record probability by `‖a‖²`. -/
theorem MGate.recordProb_init_smul (P : MGate) (a : ℂ) (ψ₀ : qs.State) (r : Record) :
    recordProb (P.eval (MState.init (a • ψ₀))) r = ‖a‖ ^ 2 * recordProb (P.eval (MState.init ψ₀)) r := by
  rw [recordProb, recordProb, MState.init_smul, MGate.eval_smul, Pi.smul_apply, norm_smul, mul_pow]

private theorem recordProb_superpose_of_false (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.qubitSupport) (b : qs.Basis) (hb : RegEncoding.bit q b = false) (α β : ℂ)
    (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b))) r := by
  have h0 : measProj (qubitReg q) 0 (α • qs.ket b + β • qs.ket (flipBit q b)) = α • qs.ket b := by
    simp [map_add, map_smul, measProj_qubitReg_ket, bit_flipBit_self, hb]
  have h1 : measProj (qubitReg q) 1 (α • qs.ket b + β • qs.ket (flipBit q b))
      = β • qs.ket (flipBit q b) := by
    simp [map_add, map_smul, measProj_qubitReg_ket, bit_flipBit_self, hb]
  rw [MGate.recordProb_decomp P hP hq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show ((0 : ℕ) : ℕ) = 0 from rfl, h0, h1, MGate.recordProb_init_smul,
    MGate.recordProb_init_smul, MGate.recordProb_flipBit P hP hq]
  ring

/-- **Spectator in superposition.** If `P.NoIdeal` and `q ∉ P.qubitSupport`, then for ANY
basis state `b`, ANY `α β : ℂ` and every record `r`: starting in
`α|b⟩ + β|flipBit q b⟩` gives `r` the probability `(‖α‖² + ‖β‖²)` times its probability from
`|b⟩`. -/
theorem MGate.recordProb_superpose (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.qubitSupport) (b : qs.Basis) (α β : ℂ) (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = (‖α‖ ^ 2 + ‖β‖ ^ 2) * recordProb (P.eval (MState.init (qs.ket b))) r := by
  cases hb : RegEncoding.bit q b
  · exact recordProb_superpose_of_false P hP hq b hb α β r
  · set b' := flipBit q b with hb'
    have hb'0 : RegEncoding.bit q b' = false := by rw [hb', bit_flipBit_self, hb]; rfl
    have hbb : b = flipBit q b' := by rw [hb', flipBit_flipBit]
    have e : α • qs.ket b + β • qs.ket b' = β • qs.ket b' + α • qs.ket (flipBit q b') := by
      rw [← hbb, add_comm]
    rw [e, recordProb_superpose_of_false P hP hq b' hb'0 β α r, hbb,
      MGate.recordProb_flipBit P hP hq b' r]
    ring

/-- Normalised form: a spectator in any unit-norm superposition does not change the record
distribution. -/
theorem MGate.recordProb_superpose_unit (P : MGate) (hP : P.NoIdeal) {q : ℕ}
    (hq : q ∉ P.qubitSupport) (b : qs.Basis) (α β : ℂ) (hαβ : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (r : Record) :
    recordProb (P.eval (MState.init (α • qs.ket b + β • qs.ket (flipBit q b)))) r
      = recordProb (P.eval (MState.init (qs.ket b))) r := by
  rw [MGate.recordProb_superpose P hP hq b α β r, hαβ, one_mul]

end MGates

end Readout
end Shor
