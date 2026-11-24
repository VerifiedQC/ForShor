import ForShor.ShorVerification.Implementation.Readout.LocalitySpectator

/-!
# Readout: tests of the semantic locality theorems (abstract semantics)

Negative sanity (the hypotheses are needed and are not vacuous):

* `control_mem_support`: the control `c` IS in the syntactic support of the real circuit as
  soon as there is one round, so the hypothesis of every locality theorem fails for `c` (and,
  by definition of `semiclassicalQubits`, for every owned qubit of `y`, `work`, `scratch` and the
  flag); this is why the success theorems must fix the control to `0` and the data to `1`.
* `superpose_weights_needed`: in the superposed-spectator theorem the factor
  `‖α‖² + ‖β‖²` cannot be dropped: for the empty program and `α = β = 1` the record `[]` has
  probability `2` from `|b⟩ + |flipBit q b⟩` and `1` from `|b⟩`.
* `measureReset_flip_named`: locality is FALSE for a named qubit. The one-step program
  `measureReset q` from a ket with bit `q = 0` gives record `[false]` with probability `1`;
  from the same ket with bit `q` flipped, probability `0`. So no theorem of this shape can drop
  `q ∉ P.qubitSupport`.
* `semiclassicalIdeal_not_noIdeal`: the ideal circuit (one round or more) contains an
  `idealCtrlModMul` node, so the general theorem `MGate.recordProb_of_agree` does not apply to
  it; T1 (`semiclassicalIdeal_recordProb_of_agree`) covers it through the closed form instead.
* `orderFindingSemiclassical_noIdeal` (the real circuit has none) is what makes T3 apply.

Model instances (a flipped exponent-slot qubit of the reference layout leaves the record
distribution of the real, the lowered and the ideal circuit unchanged) are in
`Model/Standard/SemiclassicalLocalityModel.lean` (no `Implementation/` file imports `Model/`).
-/

namespace Shor
namespace Readout
namespace LocalityTests

variable {qs : QSemantics} [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
  [MeasureClass qs]

/-- The control is named by the real circuit once there is a round. -/
theorem control_mem_support (a N c m : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) :
    c ∈ (orderFindingSemiclassical a N c (m + 1) y work scratch flag hw hs4).qubitSupport := by
  simp [orderFindingSemiclassical, readoutRounds, MGate.qubitSupport, Gate.qubitSupport]


/-- **Locality fails for a named qubit.** `measureReset q` from `|b⟩` with bit `q = 0`: record
`[false]` has probability `1`; from `|flipBit q b⟩`: probability `0`. -/
theorem measureReset_flip_named (q : ℕ) (b : qs.Basis) (hb : RegEncoding.bit q b = false) :
    recordProb ((MGate.measureReset q).eval (MState.init (qs.ket b))) [false] = 1 ∧
    recordProb ((MGate.measureReset q).eval (MState.init (qs.ket (flipBit q b)))) [false] = 0 := by
  have e : ∀ ψ : qs.State,
      (MGate.measureReset q).eval (MState.init ψ) [false] = MeasureClass.measProj (qubitReg q) 0 ψ := by
    intro ψ
    have := MGate.eval_measureReset_append q (MState.init ψ) [] false
    simpa [MState.init, measureResetBranch] using this
  refine ⟨?_, ?_⟩
  · rw [recordProb, e, measProj_qubitReg_ket, hb]
    simp [ket_norm_one]
  · rw [recordProb, e, measProj_qubitReg_ket, bit_flipBit_self, hb]
    simp

/-- The ideal circuit with at least one round contains an `idealCtrlModMul` node. -/
theorem semiclassicalIdeal_not_noIdeal (a N m : ℕ) (data : Reg) (c : ℕ) :
    ¬ (semiclassicalIdeal a N (m + 1) data c).NoIdeal := by
  simp [semiclassicalIdeal, readoutRounds, MGate.NoIdeal, Gate.NoIdeal]

/-- **The weights of the superposed-spectator theorem are needed.** The empty program
(`unitary Gate.id`, support `∅`, so every `q` is unnamed), `α = β = 1`: record `[]` has
probability `2` from `|b⟩ + |flipBit q b⟩` and `1` from `|b⟩`; so the record probabilities are
NOT those of `|b⟩` without the factor `‖α‖² + ‖β‖²`. -/
theorem superpose_weights_needed (q : ℕ) (b : qs.Basis) :
    recordProb ((MGate.unitary Gate.id).eval
        (MState.init ((1 : ℂ) • qs.ket b + (1 : ℂ) • qs.ket (flipBit q b)))) [] = 2 ∧
    recordProb ((MGate.unitary Gate.id).eval (MState.init (qs.ket b))) [] = 1 := by
  have h1 : recordProb ((MGate.unitary Gate.id).eval (MState.init (qs.ket b))) [] = 1 := by
    simp [recordProb, MState.init, QSemantics.eval, GateSemanticsCore.eval_id, ket_norm_one]
  refine ⟨?_, h1⟩
  rw [MGate.recordProb_superpose (MGate.unitary Gate.id) trivial
    (by simp [MGate.qubitSupport, Gate.qubitSupport]) b 1 1 [], h1]
  norm_num

end LocalityTests
end Readout
end Shor

-- Axioms of every new theorem (expected: propext, Classical.choice, Quot.sound).
#print axioms Shor.Readout.gate_commX
#print axioms Shor.Readout.idealCtrlModMul_ket_flipBit
#print axioms Shor.Readout.measProj_commX
#print axioms Shor.Readout.phase_commX
#print axioms Shor.Readout.measureResetBranch_commX
#print axioms Shor.Readout.MGate.eval_commX
#print axioms Shor.Readout.MState.init_X
#print axioms Shor.Readout.MGate.eval_init_X
#print axioms Shor.Readout.MGate.recordProb_init_X
#print axioms Shor.Readout.MGate.recordProb_flipBit
#print axioms Shor.Readout.MGate.recordProb_flipBits
#print axioms Shor.Readout.eq_flipBits_of_finite
#print axioms Shor.Readout.MGate.recordProb_of_agree
#print axioms Shor.Readout.semiclassicalIdeal_branch_flipBit
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_flipBit
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_flipBits
#print axioms Shor.Readout.semiclassicalIdeal_recordProb_of_agree
#print axioms Shor.Readout.cmodMul_noIdeal
#print axioms Shor.Readout.orderFindingSemiclassical_noIdeal
#print axioms Shor.Readout.orderFindingSemiclassical_branch_flipBit
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_flipBits
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_of_agree
#print axioms Shor.Readout.orderFindingSemiclassical_success_of_agree
#print axioms Shor.Readout.semiclassicalWorkspaceCleanInput_ofAgree
#print axioms Shor.Readout.SemiclassicalGhostFreeSetup.ofAgree
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_flip_exponent
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_of_agree
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_flipBits
#print axioms Shor.Readout.orderFindingSemiclassicalLow_success_of_agree
#print axioms Shor.Readout.LocalityTests.control_mem_support
#print axioms Shor.Readout.LocalityTests.superpose_weights_needed
#print axioms Shor.Readout.gate_commP
#print axioms Shor.Readout.measProj_commProj
#print axioms Shor.Readout.phase_commProj
#print axioms Shor.Readout.measureResetBranch_commProj
#print axioms Shor.Readout.MGate.eval_commProj
#print axioms Shor.Readout.MGate.eval_add
#print axioms Shor.Readout.MGate.eval_smul
#print axioms Shor.Readout.MGate.eval_init_proj
#print axioms Shor.Readout.MGate.recordProb_decomp
#print axioms Shor.Readout.MGate.recordProb_init_smul
#print axioms Shor.Readout.MGate.recordProb_superpose
#print axioms Shor.Readout.MGate.recordProb_superpose_unit
#print axioms Shor.Readout.MLowGate.eval_add
#print axioms Shor.Readout.MLowGate.eval_smul
#print axioms Shor.Readout.orderFindingSemiclassical_eval_init_proj
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_decomp
#print axioms Shor.Readout.orderFindingSemiclassical_recordProb_superpose
#print axioms Shor.Readout.orderFindingSemiclassicalLow_recordProb_superpose
#print axioms Shor.Readout.LocalityTests.measureReset_flip_named
#print axioms Shor.Readout.LocalityTests.semiclassicalIdeal_not_noIdeal
