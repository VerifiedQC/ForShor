import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerEval
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerPeak
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerSupport
import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Readiness
import ForShor.ShorVerification.Implementation.Readout.Proofs.SemiclassicalHyps
import ForShor.ShorVerification.Implementation.Readout.Proofs.ReferenceLayout

/-!
# Readout: tests of the lowering and of the proved peak

* `lowerM_one_round`: with `m = 1` the lowered circuit is, constructor for constructor,
  the lowered `initY1`, the identity of zero rounds, `H c`, the lowered real multiplier
  by `a mod N` controlled by `c`, `ffPhase c 0`, `H c`, `measureReset c`.
* `peak_one_round`: the peak formula at `m = 1`.
* `peak_no_round`: with `m = 0` (no multiplier) the peak is the base set's size: the
  extra term of the formula comes from the multiplier and nothing else.
* `peak_independent_of_rounds` (negative sanity): the semiclassical peak is the same for
  every `m ≥ 1` (no term grows with the number of rounds; the coherent circuit's
  inverse-QFT term `qftPeakD xW` has no counterpart).
* `peak_gt_base` (negative sanity): the multiplier term is really there: the peak is at
  least the base set plus `3` (`step3Peak ≥ 3`), so the formula is not the base count.
* `semiclassical_vs_coherent_peak`: on the registers of the coherent circuit, with the
  control `c` its first exponent qubit, the coherent lowering hypotheses give the
  semiclassical ones (`hws`, layout), and the two PROVED peaks satisfy
  `old = new + (xW - 1) + (qftPeakD xW - N_SC)` (`qubits_saving_eq`, now between
  lowered circuits, not only formulas).
* `reference_semiclassical_peak`: at the reference layout of `Implementation/Reference`
  (every policy, instance and level; the layout the board is built on), with
  `m = xW = log₂(2N²)` rounds, all hypotheses hold (non-vacuity) and the same
  identity holds.
-/

namespace Shor
namespace Readout
namespace LoweringTests

open QubitCount

/-! ## A small instance -/

/-- **`lowerM` at one round.** -/
theorem lowerM_one_round (P : ShorLoweringPolicy) (a N c : ℕ) (y work scratch : ExtReg) (flag : ℕ)
    (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c 1 y work scratch flag hw hs4)) :
    orderFindingSemiclassicalLow P a N c 1 y work scratch flag hw hs4 hws
      = .seq (.unitary (Policy.lowerGate P (initY1 y.active) hws.1))
          (.seq (.unitary LowGate.id)
            (.seq (.unitary (LowGate.H c))
              (.seq (.unitary (Policy.lowerGate P
                  (CmodMulInPlaceCore (a % N) N c y work scratch flag hw hs4) hws.2.2.2.1))
                (.seq (.ffPhase c 0) (.seq (.unitary (LowGate.H c)) (.measureReset c)))))) := by
  simp only [orderFindingSemiclassicalLow, orderFindingSemiclassical, readoutRounds,
    semiclassicalMultipliers, Policy.lowerM, Policy.lowerMWith, Policy.lowerGate,
    Nat.sub_self, pow_zero, pow_one]

/-- **The peak formula at one round.** -/
theorem peak_one_round (P : ShorLoweringPolicy) (hP : P.Admissible) (a N c : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c 1 y work scratch flag hw hs4))
    (hlay : SemiclassicalLayout c y work scratch flag) :
    (orderFindingSemiclassicalLow P a N c 1 y work scratch flag hw hs4 hws).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag)
      = 1 + (y.width + 1) + work.width + scratch.width + 1
        + Policy.orderFindingPeakSC P y.width work.width scratch.width := by
  rw [semiclassical_peak_formula P hP a N c 1 y work scratch flag hw hs4 hws hlay le_rfl,
    Policy.orderFindingQubitsSC]

/-- With no round the peak is the base set's size. -/
theorem peak_no_round (P : ShorLoweringPolicy) (hP : P.Admissible) (a N c : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c 0 y work scratch flag hw hs4))
    (hlay : SemiclassicalLayout c y work scratch flag) :
    (orderFindingSemiclassicalLow P a N c 0 y work scratch flag hw hs4 hws).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag)
      = 1 + (y.width + 1) + work.width + scratch.width + 1 := by
  rw [(semiclassical_peak_eq P hP a N c 0 y work scratch flag hw hs4 hws hlay).2,
    orderFindingBaseSetSC_card hw hs4 hlay]
  rfl

/-! ## Negative sanity -/

/-- **The peak does not grow with the number of rounds.** -/
theorem peak_independent_of_rounds (P : ShorLoweringPolicy) (hP : P.Admissible) (a N c m m' : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hws' : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m' y work scratch flag hw hs4))
    (hlay : SemiclassicalLayout c y work scratch flag) (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag)
      = (orderFindingSemiclassicalLow P a N c m' y work scratch flag hw hs4 hws').peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag) := by
  rw [semiclassical_peak_formula P hP a N c m y work scratch flag hw hs4 hws hlay hm,
    semiclassical_peak_formula P hP a N c m' y work scratch flag hw hs4 hws' hlay hm']

/-- **The multiplier term is really there**: at least `3` above the base set. -/
theorem peak_gt_base (P : ShorLoweringPolicy) (hP : P.Admissible) (a N c m : ℕ)
    (y work scratch : ExtReg) (flag : ℕ) (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : MGate.WorkspaceOK P (orderFindingSemiclassical a N c m y work scratch flag hw hs4))
    (hlay : SemiclassicalLayout c y work scratch flag) (hm : 1 ≤ m) :
    (orderFindingBaseSetSC c y work scratch flag).card + 3
      ≤ (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4 hws).peakQubitsFor
        P.negation (orderFindingBaseSetSC c y work scratch flag) := by
  rw [(semiclassical_peak_eq P hP a N c m y work scratch flag hw hs4 hws hlay).2]
  simp only [show m ≠ 0 by omega, ite_false]
  have : 3 ≤ Policy.orderFindingPeakSC P y.width work.width scratch.width := by
    simp only [Policy.orderFindingPeakSC, orderFindingPeakSCD, orderFindingPeakSCWith,
      modMulPeakWith, modMulPhasePeaksWith, List.foldr, step3Peak]
    omega
  omega

/-! ## Against the coherent circuit -/


/-- **Old and new proved peaks.** On the coherent circuit's registers, with `c` its first
exponent qubit and `m ≥ 1` rounds: the PROVED peak of the lowered coherent circuit is the
PROVED peak of the lowered semiclassical circuit plus `x.width - 1` plus the excess
`qftPeakD x.width - orderFindingPeakSC` of the inverse QFT over the multiplier. -/
theorem semiclassical_vs_coherent_peak (P : ShorLoweringPolicy) (hP : P.Admissible) (a N m : ℕ)
    {x y work scratch : ExtReg} {flag : ℕ} (hw : ModMulCircuitWorkspaceOK y work)
    (hs4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag) {c : ℕ} {rest : List ℕ}
    (hc : x.active.qubits = c :: rest)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hw hs4))
    (hlay : OrderFindingSpaceLayout x y work scratch flag) (hm : 1 ≤ m) :
    (orderFindingApproxLow P a N x y work scratch flag hw hs4 hws).peakQubitsFor P.negation
        (orderFindingBaseSet x y work scratch flag)
      = (orderFindingSemiclassicalLow P a N c m y work scratch flag hw hs4
            ((semiclassical_hyps_of_coherent hc hws hlay).1 m)).peakQubitsFor P.negation
          (orderFindingBaseSetSC c y work scratch flag)
        + (x.width - 1)
        + (qftPeakD P.negation P.widthRule (Policy.compile P) x.width
            - Policy.orderFindingPeakSC P y.width work.width scratch.width) := by
  have hx : 1 ≤ x.width := by
    show 1 ≤ x.active.qubits.length
    rw [hc]; simp
  rw [QubitCount.orderFindingPeakFormula P hP a N x y work scratch flag hw hs4 hws hlay,
    semiclassical_peak_formula P hP a N c m y work scratch flag hw hs4 _
      (semiclassical_hyps_of_coherent hc hws hlay).2 hm]
  exact qubits_saving_eq P hx _ _ _

/-! ## The reference layout -/

-- `RL` abbreviates the reference layout `Reference.allocateReferenceLayout P inst ℓ`
-- (a purely syntactic notation, so the statement below is unchanged).
set_option hygiene false in
local notation "RL" => Reference.allocateReferenceLayout P inst ℓ

/-- **At the reference layout** (every policy, instance and level; `Reference.allocateReferenceLayout`),
with the control its first exponent qubit and `xW = log₂(2N²)` rounds, all hypotheses hold
(non-vacuity), the lowered semiclassical circuit's peak is `orderFindingQubitsSC` at the
reference widths, and the lowered coherent circuit's peak is that plus `xW - 1` plus
`qftPeakD xW - N_SC`. -/
theorem reference_semiclassical_peak (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (ℓ : ℕ) :
    ∃ (c : ℕ) (_ : c ∈ (RL).x.active.qubits)
      (hws : MGate.WorkspaceOK P (orderFindingSemiclassical inst.a inst.N c
        (Reference.referenceXWidth inst) (RL).data
        (RL).work
        (RL).scratch
        (RL).flag
        (Reference.reference_modMulCircuitWorkspaceOK P inst ℓ)
        (Reference.reference_step4Workspace P inst ℓ))),
      SemiclassicalLayout c (RL).data
        (RL).work
        (RL).scratch
        (RL).flag ∧
      (orderFindingSemiclassicalLow P inst.a inst.N c (Reference.referenceXWidth inst)
          (RL).data
          (RL).work
          (RL).scratch
          (RL).flag
          (Reference.reference_modMulCircuitWorkspaceOK P inst ℓ)
          (Reference.reference_step4Workspace P inst ℓ) hws).peakQubitsFor P.negation
          (orderFindingBaseSetSC c (RL).data
            (RL).work
            (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsSC P (Reference.referenceDataWidth inst)
            (Reference.referenceWorkWidth inst ℓ) (Reference.referenceScratchWidth inst ℓ) ∧
      (orderFindingApproxLow P inst.a inst.N (RL).x
          (RL).data
          (RL).work
          (RL).scratch
          (RL).flag
          (Reference.reference_modMulCircuitWorkspaceOK P inst ℓ)
          (Reference.reference_step4Workspace P inst ℓ)
          (Reference.reference_gateWorkspaceOK P inst ℓ)).peakQubitsFor P.negation
          (orderFindingBaseSet (RL).x
            (RL).data
            (RL).work
            (RL).scratch
            (RL).flag)
        = Policy.orderFindingQubitsSC P (Reference.referenceDataWidth inst)
            (Reference.referenceWorkWidth inst ℓ) (Reference.referenceScratchWidth inst ℓ)
          + (Reference.referenceXWidth inst - 1)
          + (qftPeakD P.negation P.widthRule (Policy.compile P) (Reference.referenceXWidth inst)
              - Policy.orderFindingPeakSC P (Reference.referenceDataWidth inst)
                  (Reference.referenceWorkWidth inst ℓ) (Reference.referenceScratchWidth inst ℓ)) := by
  have hlay : OrderFindingSpaceLayout (RL).x
      (RL).data
      (RL).work
      (RL).scratch
      (RL).flag :=
    ⟨Reference.reference_exponent_data_disjoint P inst ℓ,
     Reference.reference_exponent_work_disjoint P inst ℓ,
     Reference.reference_exponent_scratch_disjoint P inst ℓ,
     Reference.reference_flag_outside_exponent P inst ℓ⟩
  have hxw : (RL).x.width = Reference.referenceXWidth inst :=
    Reference.allocateReferenceLayout_x_width P inst ℓ
  have hdw : (RL).data.width
      = Reference.referenceDataWidth inst :=
    Reference.allocateReferenceLayout_data_width P inst ℓ
  have hww : (RL).work.width
      = Reference.referenceWorkWidth inst ℓ :=
    Reference.allocateReferenceLayout_work_width P inst ℓ
  have hsw : (RL).scratch.width
      = Reference.referenceScratchWidth inst ℓ :=
    Reference.allocateReferenceLayout_scratch_width P inst ℓ
  have hpos : 0 < (RL).x.active.qubits.length := by
    show 0 < (RL).x.width
    rw [hxw, Reference.referenceXWidth, Nat.log2_eq_log_two]
    have := inst.range
    exact Nat.log_pos Nat.one_lt_two (by nlinarith)
  obtain ⟨c, rest, hc⟩ : ∃ c rest,
      (RL).x.active.qubits = c :: rest := by
    cases h : (RL).x.active.qubits with
    | nil => rw [h] at hpos; simp at hpos
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hws := Reference.reference_gateWorkspaceOK P inst ℓ
  have hhyp := semiclassical_hyps_of_coherent hc hws hlay
  have hm : 1 ≤ Reference.referenceXWidth inst := by
    rw [← hxw]; show 1 ≤ (RL).x.active.qubits.length
    omega
  have hnew := semiclassical_peak_formula P hP inst.a inst.N c (Reference.referenceXWidth inst)
    (RL).data (RL).work
    (RL).scratch (RL).flag
    (Reference.reference_modMulCircuitWorkspaceOK P inst ℓ)
    (Reference.reference_step4Workspace P inst ℓ) (hhyp.1 _) hhyp.2 hm
  have hold := semiclassical_vs_coherent_peak P hP inst.a inst.N (Reference.referenceXWidth inst)
    (y := (RL).data)
    (work := (RL).work)
    (scratch := (RL).scratch)
    (flag := (RL).flag)
    (Reference.reference_modMulCircuitWorkspaceOK P inst ℓ)
    (Reference.reference_step4Workspace P inst ℓ) hc hws hlay hm
  refine ⟨c, by rw [hc]; exact List.mem_cons_self, hhyp.1 _, hhyp.2, ?_, ?_⟩
  · rw [hnew, hdw, hww, hsw]
  · rw [hold, hnew, hdw, hww, hsw, hxw]

end LoweringTests
end Readout
end Shor
