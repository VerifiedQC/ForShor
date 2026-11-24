import ForShor.ShorVerification.Implementation.Readout.Cost
import ForShor.ShorVerification.Implementation.Readout.Proofs.LowerPeak
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Numerals
import ForShor.ShorVerification.Implementation.Readout.Proofs.ReferenceLayout
import ForShor.ShorVerification.Submission.Audit

/-!
# Semiclassical readout: numerals for a concrete policy (the generic part)

The per-policy files of this folder close, by `decide +kernel`, two numbers of a board
policy `P` (width rule `exact`, negation `oneQubit`) at the 2048-bit reference widths
(data 2048, work 2347, scratch 4398):

* `N_SC = Policy.orderFindingPeakUSC P Balanced.defaultRule 2048 2347 4398`, the peak of one
  controlled modular multiplication (the semiclassical circuit's extra-qubit peak: no
  inverse-QFT term), and
* `q = qftPeakD P.negation P.widthRule (Policy.compile P) 4095`, the inverse QFT's peak at the
  board's exponent width.

This file turns them into the public claims, with no further evaluation:

* `peakU_eq_of` (the algebra of `orderFindingPeakWith = max (modMulPeak) (qftPeak xW)`): when
  `q ≤ N_SC`, the OLD balanced peak at `xW = 4095` is `N_SC` (so the old kernel numeral
  `balanced_exact_oneQubit` of `QubitCount/Proofs/PolicyNumeralsBoard/*Exact.lean` is
  re-derived, not re-evaluated, and not imported).
* `qubitsUSC_eq_of`: `Policy.orderFindingQubitsUSC P defaultRule 2048 2347 4398 = 1 + 8795 + N_SC`.
* `saving_eq_of`: the old count at `xW = 4095` minus the new one is `4094 = xW - 1`.
* `ReferenceSemiclassicalPeakIs P N_SC` and `referenceSemiclassicalPeakIs_of`: for every
  2048-bit instance, at the reference layout of level `Reference.m2048` (the layout of the old
  numerals' `ReferenceBalancedPeakIs`), with the control `referenceControl` (the first
  exponent qubit, `Readout/Proofs/ReferenceLayout.lean`) and `log₂(2N²)` rounds, the lowered BALANCED and every-site-split
  semiclassical circuits (the circuit terms of
  `Model.model_semiclassical_lowered_balanced(U)_success_and_peak`), walked from
  `orderFindingBaseSetSC`, peak at exactly `1 + 8795 + N_SC` qubits
  (`semiclassical_peak_formula_balanced_u`; the balanced circuit is the same term,
  `lowerMBalancedU_eq`).

`8795` is the data register with its carry bit (2049), the work register (2347), the scratch
register (4398) and the flag; the semiclassical base set adds the one control qubit `c`.

Limitation: the link from these numerals to the lowered circuit's walked peak
(`referenceSemiclassicalPeakIs_of`) is stated at the single reference layout of level
`Reference.m2048`; no other approximation level or width is covered by this folder.
-/

namespace Shor
namespace Readout
namespace PolicyNumeralsSC

open Reference QubitCount

/-! ## Formula algebra -/

/-- **The old balanced peak from the new one.** When the inverse QFT's peak at `xW ≥ 1` does
not exceed the multiplication's, the old balanced peak `orderFindingPeakU` at `xW` equals the
semiclassical one. -/
theorem peakU_eq_of (P : ShorLoweringPolicy) (R : Balanced.Rule) {xW : ℕ} (hx : 1 ≤ xW)
    (dW wW sW : ℕ) {Nsc q : ℕ}
    (hN : Policy.orderFindingPeakUSC P R dW wW sW = Nsc)
    (hq : qftPeakD P.negation P.widthRule (Policy.compile P) xW = q) (hle : q ≤ Nsc) :
    Policy.orderFindingPeakU P R xW dW wW sW = Nsc := by
  subst hN hq
  simp only [Policy.orderFindingPeakU, orderFindingPeakUD, Policy.orderFindingPeakUSC,
    orderFindingPeakUSCD] at hle ⊢
  rw [orderFindingPeakWith_eq _ _ _ (by omega)]
  omega

/-- **The new count.** -/
theorem qubitsUSC_eq_of (P : ShorLoweringPolicy) {Nsc : ℕ}
    (hN : Policy.orderFindingPeakUSC P Balanced.defaultRule 2048 2347 4398 = Nsc) :
    Policy.orderFindingQubitsUSC P Balanced.defaultRule 2048 2347 4398 = 1 + 8795 + Nsc := by
  unfold Policy.orderFindingQubitsUSC
  rw [hN]

/-- **The old count at `xW = 4095`**, re-derived from `N_SC` and the QFT peak. -/
theorem qubitsU_eq_of (P : ShorLoweringPolicy) {Nsc q : ℕ}
    (hN : Policy.orderFindingPeakUSC P Balanced.defaultRule 2048 2347 4398 = Nsc)
    (hq : qftPeakD P.negation P.widthRule (Policy.compile P) 4095 = q) (hle : q ≤ Nsc) :
    Policy.orderFindingQubitsU P Balanced.defaultRule 4095 2048 2347 4398 = 4095 + 8795 + Nsc := by
  unfold Policy.orderFindingQubitsU
  rw [peakU_eq_of P Balanced.defaultRule (by norm_num) 2048 2347 4398 hN hq hle]

/-- **The saving at `xW = 4095` is exactly `xW - 1 = 4094`.** -/
theorem saving_eq_of (P : ShorLoweringPolicy) {Nsc q : ℕ}
    (hN : Policy.orderFindingPeakUSC P Balanced.defaultRule 2048 2347 4398 = Nsc)
    (hq : qftPeakD P.negation P.widthRule (Policy.compile P) 4095 = q) (hle : q ≤ Nsc) :
    Policy.orderFindingQubitsU P Balanced.defaultRule 4095 2048 2347 4398
      - Policy.orderFindingQubitsUSC P Balanced.defaultRule 2048 2347 4398 = 4094 := by
  rw [qubitsU_eq_of P hN hq hle, qubitsUSC_eq_of P hN]
  omega

/-! ## The lowered circuit at the reference layout -/

-- `RL` abbreviates the 2048-bit reference layout (level `Reference.m2048`, as the old numerals).
set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst Reference.m2048

set_option hygiene false in
local notation "cRL" => referenceControl P inst Reference.m2048

/-- **The lowered semiclassical circuit of `P` at the 2048-bit reference layout peaks at
`1 + 8795 + N_SC` qubits**: for every 2048-bit instance, the balanced (default rule) and the
every-site-split lowerings of `orderFindingSemiclassical` (control `referenceControl`, the first
exponent qubit; `log₂(2N²)` rounds; the layout's own workspaces
`referenceCircuitWorkspace`/`referenceStep4Workspace`, by unfolding the ones
`Model.referenceSemiclassicalSetup` carries),
walked from `orderFindingBaseSetSC`, counted with `P.negation`. -/
def ReferenceSemiclassicalPeakIs (P : ShorLoweringPolicy) (Nsc : ℕ) : Prop :=
  ∀ inst : ShorOrderFindingInstance, Is2048Bit inst.N →
    (orderFindingSemiclassicalLowBalanced P Balanced.defaultRule inst.a inst.N cRL
        (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
        (referenceCircuitWorkspace P inst Reference.m2048)
        (referenceStep4Workspace P inst Reference.m2048)
        (referenceSemiclassicalWorkspaceOK P inst Reference.m2048 _)).peakQubitsFor P.negation
        (orderFindingBaseSetSC cRL (RL).data (RL).work (RL).scratch (RL).flag)
      = 1 + 8795 + Nsc ∧
    (orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N cRL
        (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
        (referenceCircuitWorkspace P inst Reference.m2048)
        (referenceStep4Workspace P inst Reference.m2048)
        (referenceSemiclassicalWorkspaceOK P inst Reference.m2048 _)
        (referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst Reference.m2048 _)).peakQubitsFor
        P.negation (orderFindingBaseSetSC cRL (RL).data (RL).work (RL).scratch (RL).flag)
      = 1 + 8795 + Nsc

/-- From the kernel-evaluated `N_SC`. -/
theorem referenceSemiclassicalPeakIs_of (P : ShorLoweringPolicy) (hP : P.Admissible) {Nsc : ℕ}
    (hN : Policy.orderFindingPeakUSC P Balanced.defaultRule 2048 2347 4398 = Nsc) :
    ReferenceSemiclassicalPeakIs P Nsc := by
  intro inst hNb
  obtain ⟨hd, hw, hs, -⟩ := reference_widths_2048 hNb
  have hU : (orderFindingSemiclassicalLowBalancedU P Balanced.defaultRule inst.a inst.N cRL
        (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
        (referenceCircuitWorkspace P inst Reference.m2048)
        (referenceStep4Workspace P inst Reference.m2048)
        (referenceSemiclassicalWorkspaceOK P inst Reference.m2048 _)
        (referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst Reference.m2048
          _)).peakQubitsFor
        P.negation (orderFindingBaseSetSC cRL (RL).data (RL).work (RL).scratch (RL).flag)
      = 1 + 8795 + Nsc := by
    rw [semiclassical_peak_formula_balanced_u P _ hP _ _ _ _ _ _ _ _ _ _ _ _
      (referenceSemiclassicalLayout P inst Reference.m2048)
      (referenceX_pos P inst Reference.m2048), referenceLayout_data_width',
      referenceLayout_work_width', referenceLayout_scratch_width', hd, hw, hs]
    exact qubitsUSC_eq_of P hN
  refine ⟨?_, hU⟩
  unfold orderFindingSemiclassicalLowBalanced
  rw [← lowerMBalancedU_eq P Balanced.defaultRule _ _
    (referenceSemiclassicalFits P _ (Balanced.referenceFits_default P) inst Reference.m2048
      (regSize (RL).x.active))]
  exact hU

#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.peakU_eq_of
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.qubitsUSC_eq_of
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.qubitsU_eq_of
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.saving_eq_of
#assert_axioms _root_.Shor.Readout.PolicyNumeralsSC.referenceSemiclassicalPeakIs_of

end PolicyNumeralsSC
end Readout
end Shor
