import ForShor.ShorVerification.Implementation.Readout.LocalityReserve
import ForShor.ShorVerification.Implementation.Readout.LocalityIdeal
import ForShor.ShorVerification.Implementation.Readout.LocalityTests

/-!
# Readout: tests of Tasks A1 (exact support, reserve qubits) and A2 (ideal multipliers)

Abstract semantics. Model.qs instances are in
`Model/Standard/SemiclassicalLocalityIdealModel.lean` (no `Implementation/` file imports
`Model/`).

A1, the exact support is strictly finer and the new theorem covers what the old did not:
* `negate_reserve_named_not_exact`: for `Negate e`, `e` = active `[0]` + reserve `[1]`, qubit `1`
  IS in `qubitSupport` (so `MGate.recordProb_flipBit` does not apply) but NOT in
  `exactSupport`; `negate_reserve_flip` is the new theorem at that qubit.
* `zeroExtend_exact_empty`: `zeroExtend` acts on nothing (it is the identity).

A1, negative sanity:
* `grown_reserve_named`: a reserve qubit the real circuit grows into (`y.newBits 2`,
  `work.newBits 1`, `scratch.newBits 1`) IS in its exact support (one round or more), so the
  theorems do not cover it;
* `grown_reserve_breaks_clean`: flipping any reserve qubit (grown into or not) of a clean start
  ket breaks `SemiclassicalWorkspaceCleanInput`, the lowered circuit's hypothesis;
* `measureReset_flip_named_exact`: locality is FALSE for a qubit in the exact support (the
  existing counterexample, `measureReset q`; its exact support is `{q}`).

A2, negative sanity:
* `ideal_not_safe_data`: an ideal node is NOT `IdealSafe` at a qubit of its data register
  (neither constructor applies), so the A2 theorems never speak about data qubits;
* `ideal_not_safe_ctrl`: nor at its control;
* `semiclassicalIdeal_data_exact`: a data qubit is in the exact support of the ideal readout;
* `idealDom_ket_mem_witness`: the domain hypothesis is satisfiable by every ket with data
  `< N` (`ket_mem_idealDom`), e.g. data `0` and data `1`.
-/

namespace Shor
namespace Readout
namespace LocalityIdealTests

open MeasureClass

/-- Active `[0]`, reserve `[1]`. -/
def e01 : ExtReg := ExtReg.withReserve (Reg.singleton 0) (Reg.singleton 1) (by
  simp [Disjoint, Reg.singleton])

/-- **The exact support is strictly finer.** -/
theorem negate_reserve_named_not_exact :
    1 ∈ (MGate.unitary (Gate.Negate e01)).qubitSupport ∧
      1 ∉ (MGate.unitary (Gate.Negate e01)).exactSupport := by
  refine ⟨?_, ?_⟩
  · simp [MGate.qubitSupport, Gate.qubitSupport, e01, ExtReg.ownedQubits, Reg.singleton]
  · simp [MGate.exactSupport, Gate.exactSupport, e01, Reg.singleton]

theorem zeroExtend_exact_empty (r : ExtReg) (n : ℕ) : (Gate.zeroExtend r n).exactSupport = ∅ :=
  rfl

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- The new theorem at a reserve qubit the old one cannot reach. -/
theorem negate_reserve_flip (b : qs.Basis) (r : Record) :
    recordProb ((MGate.unitary (Gate.Negate e01)).eval (MState.init (qs.ket (flipBit 1 b)))) r
      = recordProb ((MGate.unitary (Gate.Negate e01)).eval (MState.init (qs.ket b))) r :=
  MGate.recordProb_flipBit_exact (MGate.unitary (Gate.Negate e01)) trivial
    negate_reserve_named_not_exact.2 b r

/-- **A grown-into reserve qubit is named** (exact support, one round or more). -/
theorem grown_reserve_named (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) (q : ℕ)
    (hq : q ∈ (y.newBits 2).qubits ∨ q ∈ (work.newBits 1).qubits ∨
      q ∈ (scratch.newBits 1).qubits) :
    q ∈ (orderFindingSemiclassical a N c (m + 1) y work scratch flag hw hs4).exactSupport :=
  reserve_used a N m hw hs4 hq

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- **Flipping a grown-into reserve qubit breaks the clean hypothesis** (as does any reserve
flip). -/
theorem grown_reserve_breaks_clean (y work scratch : ExtReg) (b0 : qs.Basis) (q : ℕ)
    (hq : q ∈ (y.newBits 2).qubits) (h : SemiclassicalWorkspaceCleanInput y work scratch b0) :
    ¬ SemiclassicalWorkspaceCleanInput y work scratch (flipBit q b0) :=
  cleanInput_fails_flip_reserve (Or.inl (List.mem_of_mem_take hq)) h

/-- **Locality is false inside the exact support**: `measureReset q` (exact support `{q}`). -/
theorem measureReset_flip_named_exact (q : ℕ) (b : qs.Basis) (hb : RegEncoding.bit q b = false) :
    q ∈ (MGate.measureReset q).exactSupport ∧
    recordProb ((MGate.measureReset q).eval (MState.init (qs.ket b))) [false] = 1 ∧
    recordProb ((MGate.measureReset q).eval (MState.init (qs.ket (flipBit q b)))) [false] = 0 :=
  ⟨rfl, (LocalityTests.measureReset_flip_named q b hb).1,
    (LocalityTests.measureReset_flip_named q b hb).2⟩

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- **An ideal node is never safe at one of its data qubits.** -/
theorem ideal_not_safe_data [GateSemanticsCore qs] (D : Submodule ℂ qs.State) (c N ctrl : ℕ)
    (data : Reg) {q : ℕ} (hq : q ∈ data.qubits) :
    ¬ (Gate.idealCtrlModMul c N data ctrl).IdealSafe qs D q := by
  intro h
  cases h with
  | local_ _ hU _ => exact hU
  | ideal _ _ _ _ _ _ _ _ hqd _ _ => exact hqd hq

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- **An ideal node is never safe at its control.** -/
theorem ideal_not_safe_ctrl [GateSemanticsCore qs] (D : Submodule ℂ qs.State) (c N ctrl : ℕ)
    (data : Reg) : ¬ (Gate.idealCtrlModMul c N data ctrl).IdealSafe qs D ctrl := by
  intro h
  cases h with
  | local_ _ hU _ => exact hU
  | ideal _ _ _ _ _ _ _ _ _ hqc _ => exact hqc rfl

/-- A data qubit is in the exact support of the ideal readout (one round or more). -/
theorem semiclassicalIdeal_data_exact (a N m : ℕ) (data : Reg) (c : ℕ) {q : ℕ}
    (hq : q ∈ data.qubits) : q ∈ (semiclassicalIdeal a N (m + 1) data c).exactSupport := by
  simp only [semiclassicalIdeal, readoutRounds, MGate.exactSupport, Gate.exactSupport,
    Set.mem_union, Set.mem_ofPred_eq]
  exact Or.inr (Or.inr (Or.inl (Or.inl hq)))

omit [GateSemanticsFacts qs] [LowerGateClass qs] [MeasureClass qs] in
/-- The domain hypothesis is satisfiable: every ket with data `< N` lies in it. -/
theorem idealDom_ket_mem_witness {N : ℕ} {data : Reg} (b : qs.Basis)
    (hb : RegEncoding.toNat data b < N) : qs.ket b ∈ IdealDom qs N data :=
  ket_mem_idealDom hb

end LocalityIdealTests
end Readout
end Shor

-- Axioms of every new theorem (expected: propext, Classical.choice, Quot.sound).
#print axioms Shor.Readout.MState.init_mem
#print axioms Shor.Readout.MGate.spectatorOn_top
#print axioms Shor.MGate.SpectatorOn.eval_init_X
#print axioms Shor.MGate.SpectatorOn.recordProb_init_X
#print axioms Shor.MGate.SpectatorOn.recordProb_flipBit
#print axioms Shor.MGate.SpectatorOn.eval_init_proj
#print axioms Shor.MGate.SpectatorOn.recordProb_decomp
#print axioms Shor.MGate.SpectatorOn.recordProb_superpose
#print axioms Shor.MGate.SpectatorOn.mono
#print axioms Shor.Readout.MGate.recordProb_flipBits_on
#print axioms Shor.Readout.MGate.recordProb_of_agree_on
#print axioms Shor.Readout.Gate.exactSupport_subset
#print axioms Shor.Readout.MGate.exactSupport_subset
#print axioms Shor.Readout.signExtendBasis_flipBit_exact
#print axioms Shor.Readout.bit_signExtendBasis_of_not_mem_exact
#print axioms Shor.Readout.gate_commX_exact
#print axioms Shor.Readout.gate_commP_exact
#print axioms Shor.Readout.MGate.eval_commX_exact
#print axioms Shor.Readout.MGate.eval_commProj_exact
#print axioms Shor.Readout.MGate.spectatorOn_exact
#print axioms Shor.Readout.MGate.recordProb_init_X_exact
#print axioms Shor.Readout.MGate.recordProb_flipBit_exact
#print axioms Shor.Readout.MGate.recordProb_flipBits_exact
#print axioms Shor.Readout.MGate.recordProb_of_agree_exact
#print axioms Shor.Readout.MGate.recordProb_decomp_exact
#print axioms Shor.Readout.MGate.recordProb_superpose_exact
#print axioms Shor.Readout.H_reg_exactSupport
#print axioms Shor.Readout.initY1_exactSupport
#print axioms Shor.Readout.cmodMul_exactSupport
#print axioms Shor.Readout.orderFindingSemiclassical_exactSupport
#print axioms Shor.Readout.unusedReserve_not_mem_exact
#print axioms Shor.Readout.reserve_used_cmodMul
#print axioms Shor.Readout.reserve_used
#print axioms Shor.Readout.freshZero_flipBit
#print axioms Shor.Readout.cleanInput_fails_flip_reserve
#print axioms Shor.Readout.unusedReserve_mem_reserve
#print axioms Shor.Readout.qftReserveNeedOf_ge_two
#print axioms Shor.Readout.referenceDataWidth_ge_two
#print axioms Shor.Readout.reference_data_need_ge
#print axioms Shor.Readout.reference_work_need_ge
#print axioms Shor.Readout.reference_scratch_need_ge
#print axioms Shor.Readout.reference_unusedReserve_length
#print axioms Shor.Readout.reference_unusedReserve_ne_nil
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_flipBits_exact
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_of_agree_exact
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_superpose_exact
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_flip_unusedReserve
#print axioms Shor.Readout.ket_mem_idealDom
#print axioms Shor.Readout.inRange_mem_idealDom
#print axioms Shor.Readout.idealDom_map
#print axioms Shor.Readout.validSpan_true_eq
#print axioms Shor.Readout.idealCtrlModMul_commX_dom
#print axioms Shor.Readout.idealCtrlModMul_commP_dom
#print axioms Shor.Readout.gate_commX_on
#print axioms Shor.Readout.gate_commP_on
#print axioms Shor.Readout.MGate.spectatorOn_of_idealSafe
#print axioms Shor.Readout.idealDom_X
#print axioms Shor.Readout.idealDom_measProj
#print axioms Shor.Gate.KeepsDom.preserves
#print axioms Shor.MGate.KeepsDom.preserves
#print axioms Shor.Readout.readoutRounds_keepsDom
#print axioms Shor.Readout.readoutRounds_idealSafe
#print axioms Shor.Readout.semiclassicalIdeal_keepsDom
#print axioms Shor.Readout.semiclassicalIdeal_idealSafe
#print axioms Shor.Readout.semiclassicalIdeal_spectatorOn
#print axioms Shor.Readout.semiclassicalIdeal_branch_X_dom
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_init_X_dom
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_init_X_inRange
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_decomp_dom
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_flipBits_dom
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_of_agree_dom
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_superpose_dom
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_flipBit_of_dom
#print axioms Shor.Readout.idealCtrlModMul_moves_top
#print axioms Shor.Readout.LocalityIdealTests.negate_reserve_named_not_exact
#print axioms Shor.Readout.LocalityIdealTests.negate_reserve_flip
#print axioms Shor.Readout.LocalityIdealTests.grown_reserve_named
#print axioms Shor.Readout.LocalityIdealTests.grown_reserve_breaks_clean
#print axioms Shor.Readout.LocalityIdealTests.measureReset_flip_named_exact
#print axioms Shor.Readout.LocalityIdealTests.ideal_not_safe_data
#print axioms Shor.Readout.LocalityIdealTests.ideal_not_safe_ctrl
#print axioms Shor.Readout.LocalityIdealTests.semiclassicalIdeal_data_exact
#print axioms Shor.Readout.LocalityIdealTests.idealDom_ket_mem_witness
