import ForShor.ShorVerification.Implementation.Readout.LowLocality
import ForShor.ShorVerification.Implementation.Readout.LowLocalityNamed
import ForShor.ShorVerification.Implementation.Readout.LowLocalityBalanced

/-!
# Readout: tests of the low-gate locality theorems (abstract semantics)

* `measureReset_flip_namedL`: locality is FALSE for a qubit in the low support. The lowered
  one-step program `MLowGate.measureReset q` from a ket with bit `q = 0` gives record `[false]`
  with probability `1`; with bit `q` flipped, probability `0`. So the hypothesis
  `q ∉ P.lowSupport` cannot be dropped.
* `testReg`, `signDealloc_footprint_strict`: the footprint is strictly larger than
  `LowGate.usedQubits` at `signDealloc`: qubit `1` (the deallocated reserve qubit of a register
  with active part `[0]` and reserve `[1]`) is in `lowFootprint (signDealloc testReg 1)` but not
  in `usedQubits (signDealloc testReg 1)`. That the larger set is NEEDED (the projector on qubit
  `1` does not commute with that gate) is shown at `Model.qs` in
  `Model/Standard/SemiclassicalLowLocalityModel.lean` (`model_signDealloc_not_commProj`).
* `adj_H_commX`, `adj_signExtend_commProj`: adjoint nodes are covered with no hypothesis
  (B2 needs no new law).
* `control_mem_lowSupport`: the control `c` IS in the low support of the lowered real circuit
  once there is a round, so the locality hypothesis fails for `c`.
* `superpose_weights_neededL`: the factor `‖α‖² + ‖β‖²` of the superposed-spectator theorem
  cannot be dropped (empty program, `α = β = 1`).

Model instances are in `Model/Standard/SemiclassicalLowLocalityModel.lean` (no
`Implementation/` file imports `Model/`).
-/

namespace Shor
namespace Readout
namespace LowLocalityTests

variable {qs : QSemantics} [RegEncoding qs.Basis] [LowerGateClass qs] [MeasureClass qs]

/-- **Locality fails for a qubit of the low support.** -/
theorem measureReset_flip_namedL (q : ℕ) (b : qs.Basis) (hb : RegEncoding.bit q b = false) :
    recordProb ((MLowGate.measureReset q).eval (MState.init (qs.ket b))) [false] = 1 ∧
    recordProb ((MLowGate.measureReset q).eval (MState.init (qs.ket (flipBit q b)))) [false]
      = 0 := by
  have e : ∀ ψ : qs.State, (MLowGate.measureReset q).eval (MState.init ψ) [false]
      = MeasureClass.measProj (qubitReg q) 0 ψ := by
    intro ψ
    simp [MLowGate.eval, MState.init, measureResetBranchL]
  refine ⟨?_, ?_⟩
  · rw [recordProb, e, measProj_qubitReg_ket, hb]
    simp [ket_norm_one]
  · rw [recordProb, e, measProj_qubitReg_ket, bit_flipBit_self, hb]
    simp

/-- A register with active part `[0]` and one reserve qubit `1`. -/
def testReg : ExtReg :=
  ⟨⟨[0], by simp⟩, ⟨[1], by simp⟩, by simp [Shor.Disjoint]⟩

/-- **The footprint is strictly larger than `usedQubits` at `signDealloc`.** -/
theorem signDealloc_footprint_strict :
    1 ∈ (LowGate.signDealloc testReg 1).lowFootprint ∧
      1 ∉ (LowGate.signDealloc testReg 1).usedQubits := by
  decide

omit [MeasureClass qs] in
/-- Adjoint nodes need no hypothesis beyond the footprint. -/
theorem adj_H_commX : CommXL qs (LowGate.adj (LowGate.H 0)) 1 :=
  lowGate_commX _ (by decide)

theorem adj_signExtend_commProj (o : ℕ) :
    CommPL qs (LowGate.adj (LowGate.signExtend testReg 1)) 2 o :=
  lowGate_commProj _ (by decide) o

/-- The control is in the low support of the lowered real circuit once there is a round. -/
theorem control_mem_lowSupport (P : ShorLoweringPolicy) (a N c m : ℕ) (y work scratch : ExtReg)
    (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c (m + 1) y work scratch flag hw hs4)) :
    c ∈ (orderFindingSemiclassicalLow P a N c (m + 1) y work scratch flag hw hs4 hws).lowSupport := by
  simp [orderFindingSemiclassicalLow, orderFindingSemiclassical, readoutRounds, Policy.lowerM,
    Policy.lowerMWith, MLowGate.lowSupport]

/-- **The weights of the superposed-spectator theorem are needed.** -/
theorem superpose_weights_neededL (q : ℕ) (b : qs.Basis) :
    recordProb ((MLowGate.unitary LowGate.id).eval
        (MState.init ((1 : ℂ) • qs.ket b + (1 : ℂ) • qs.ket (flipBit q b)))) [] = 2 ∧
    recordProb ((MLowGate.unitary LowGate.id).eval (MState.init (qs.ket b))) [] = 1 := by
  have h1 : recordProb ((MLowGate.unitary LowGate.id).eval (MState.init (qs.ket b))) [] = 1 := by
    simp [recordProb, MState.init, MLowGate.eval, LowerGateClass.evalL_id, ket_norm_one]
  refine ⟨?_, h1⟩
  rw [MLowGate.recordProb_superpose (MLowGate.unitary LowGate.id)
    (by simp [MLowGate.lowSupport, LowGate.lowFootprint]) b 1 1 [], h1]
  norm_num

end LowLocalityTests
end Readout
end Shor

-- Axioms of every new theorem (expected: propext, Classical.choice, Quot.sound).
#print axioms Shor.LowGate.usedQubits_subset_lowFootprint
#print axioms Shor.LowGate.lowFootprint_eq_usedQubits
#print axioms Shor.Readout.not_mem_grow
#print axioms Shor.Readout.signExtendBasis_flipBit_grow
#print axioms Shor.Readout.bit_signExtendBasis_of_not_mem_newBits
#print axioms Shor.Readout.evalL_X_ket_flipBit
#print axioms Shor.Readout.commXL_of_ket
#print axioms Shor.Readout.commXL_of_basis
#print axioms Shor.Readout.commXL_of_diag
#print axioms Shor.Readout.commXL_of_id
#print axioms Shor.Readout.commXL_seq
#print axioms Shor.Readout.evalL_apply_adj
#print axioms Shor.Readout.commXL_adj
#print axioms Shor.Readout.commXL_H
#print axioms Shor.Readout.commXL_Phase
#print axioms Shor.Readout.lowGate_commX
#print axioms Shor.Readout.commPL_of_ket
#print axioms Shor.Readout.commPL_of_basis
#print axioms Shor.Readout.commPL_of_diag
#print axioms Shor.Readout.commPL_of_id
#print axioms Shor.Readout.commPL_seq
#print axioms Shor.Readout.commPL_adj
#print axioms Shor.Readout.commPL_H
#print axioms Shor.Readout.lowGate_commProj
#print axioms Shor.Readout.measProj_commXL
#print axioms Shor.Readout.measureResetBranchL_commX
#print axioms Shor.Readout.measureResetBranchL_commProj
#print axioms Shor.Readout.MLowGate.eval_commX
#print axioms Shor.Readout.MLowGate.eval_commProj
#print axioms Shor.Readout.inner_evalL_X
#print axioms Shor.Readout.norm_evalL_X
#print axioms Shor.Readout.MState.init_XL
#print axioms Shor.Readout.MLowGate.eval_init_X
#print axioms Shor.Readout.MLowGate.recordProb_init_X
#print axioms Shor.Readout.MLowGate.recordProb_flipBit
#print axioms Shor.Readout.MLowGate.recordProb_flipBits
#print axioms Shor.Readout.MLowGate.recordProb_of_agree
#print axioms Shor.Readout.MLowGate.eval_init_proj
#print axioms Shor.Readout.MLowGate.recordProb_decomp
#print axioms Shor.Readout.MLowGate.recordProb_init_smul
#print axioms Shor.Readout.MLowGate.recordProb_superpose
#print axioms Shor.Readout.MLowGate.recordProb_superpose_unit
#print axioms Shor.LowGate.lowFootprint_subset_used_reach
#print axioms Shor.Readout.mem_owned_of_grow'
#print axioms Shor.Readout.unit_mem_owned'
#print axioms Shor.Readout.lowFootprint_copyBitPowers
#print axioms Shor.Readout.cmpGe_lowFootprint_subset
#print axioms Shor.Readout.cSub_lowFootprint_subset
#print axioms Shor.Readout.lowerGate_lowFootprint_subset
#print axioms Shor.Readout.lowerM_lowSupport_subset
#print axioms Shor.Readout.semiclassical_lowSupport_subset
#print axioms Shor.Readout.not_mem_semiclassicalLow_lowSupport
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_init_X
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_decomp
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_superpose_direct
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_of_agree_direct
#print axioms Shor.Readout.LowLocalityTests.measureReset_flip_namedL
#print axioms Shor.Readout.LowLocalityTests.signDealloc_footprint_strict
#print axioms Shor.Readout.LowLocalityTests.adj_H_commX
#print axioms Shor.Readout.LowLocalityTests.adj_signExtend_commProj
#print axioms Shor.Readout.LowLocalityTests.control_mem_lowSupport
#print axioms Shor.Readout.LowLocalityTests.superpose_weights_neededL

-- B4 (named footprint).
#print axioms Shor.Readout.support_allocChunkGate
#print axioms Shor.Readout.support_deallocChunkGate
#print axioms Shor.Readout.support_allocationsAux
#print axioms Shor.Readout.support_deallocationsAux
#print axioms Shor.Readout.support_body
#print axioms Shor.Readout.slotsIn_init
#print axioms Shor.Readout.slotsIn_target
#print axioms Shor.Readout.support_compiledSignedPhaseGateBy
#print axioms Shor.Readout.support_controlPhaseLeaves
#print axioms Shor.Readout.mem_signedTermsAux
#print axioms Shor.Readout.foot_sequence
#print axioms Shor.Readout.foot_CPhase
#print axioms Shor.Readout.foot_CCPhase
#print axioms Shor.Readout.foot_naiveSigned
#print axioms Shor.Readout.foot_naiveCSigned
#print axioms Shor.Readout.lowerGateRec_lowFootprint
#print axioms Shor.Readout.support_PhaseProdUsing
#print axioms Shor.Readout.qftPlan_lowFootprint
#print axioms Shor.Readout.lowerQFT_lowFootprint
#print axioms Shor.Readout.qftPhaseFoot_subset
#print axioms Shor.Readout.mgate_qftPhaseFoot_subset
#print axioms Shor.Readout.lowerGate_lowFootprint_named
#print axioms Shor.Readout.lowerM_lowSupport_named
#print axioms Shor.Readout.semiclassical_lowSupport_named
#print axioms Shor.Readout.not_mem_qftPhaseFoot_of_not_mem_semiclassicalQubits
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_init_X_named
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_decomp_named
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_superpose_named
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_of_agree_named

-- B5.
#print axioms Shor.LowGate.lowFootprint_subset_ownedFoot
#print axioms Shor.LowGate.reach_subset_ownedFoot
#print axioms Shor.Readout.foot_sequenceO
#print axioms Shor.Readout.foot_CPhaseO
#print axioms Shor.Readout.foot_CCPhaseO
#print axioms Shor.Readout.foot_naiveSignedO
#print axioms Shor.Readout.foot_naiveCSignedO
#print axioms Shor.Readout.lowerGateRec_ownedFoot
#print axioms Shor.Readout.qftPlan_ownedFoot
#print axioms Shor.Readout.lowerQFT_ownedFoot
#print axioms Shor.Readout.qftPhaseReach_subset
#print axioms Shor.Readout.mgate_qftPhaseReach_subset
#print axioms Shor.Readout.lowerGate_reach_named
#print axioms Shor.Readout.lowerGate_lowFootprint_subset_support
#print axioms Shor.Readout.semiclassical_lowered_qubits_named
#print axioms Shor.Readout.signedPlan_valid_of_workspaceOK
#print axioms Shor.Readout.cSignedPlan_valid_of_cWorkspaceOK
#print axioms Shor.Readout.gateWorkspaceOK_QFT_iff
#print axioms Shor.Readout.gateWorkspaceOK_signed_iff
#print axioms Shor.Readout.gateWorkspaceOK_csigned_iff
#print axioms Shor.Readout.qftWorkspace_of_reserveOK
#print axioms Shor.Readout.qftXWork_sub_reserve
#print axioms Shor.Readout.qftZWork_sub_reserve
#print axioms Shor.Readout.phaseProdUsingPlan_valid
#print axioms Shor.Readout.owned_lowBlock
#print axioms Shor.Readout.owned_highPart
#print axioms Shor.Readout.mem_ctlGate_iff
#print axioms Shor.Readout.support_splitGate
#print axioms Shor.Readout.support_siteGate
#print axioms Shor.Readout.support_siteGateU
#print axioms Shor.Readout.support_balance
#print axioms Shor.Readout.support_balanceU
#print axioms Shor.Readout.lowerMBalanced_lowSupport_named
#print axioms Shor.Readout.lowerMBalancedU_lowSupport_named
#print axioms Shor.Readout.semiclassical_lowSupport_balanced
#print axioms Shor.Readout.semiclassical_lowSupport_balancedU
#print axioms Shor.Readout.orderFindingSemiclassicalLowBalanced_recordProb_init_X_named
#print axioms Shor.Readout.orderFindingSemiclassicalLowBalanced_recordProb_decomp_named
#print axioms Shor.Readout.orderFindingSemiclassicalLowBalanced_recordProb_superpose_named
#print axioms Shor.Readout.orderFindingSemiclassicalLowBalancedU_recordProb_init_X_named
#print axioms Shor.Readout.orderFindingSemiclassicalLowBalancedU_recordProb_decomp_named
#print axioms Shor.Readout.orderFindingSemiclassicalLowBalancedU_recordProb_superpose_named
