import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyPeak
import ForShor.ShorVerification.Submission.Audit

/-!
# Qubit count: numerals for a concrete policy (the generic part)

`PolicyPeak.lean` reduces the peak of the 2048-bit reference circuit of an admissible policy `P`
to the closed-form budgets `Policy.orderFindingPeak P` (plain) and
`Policy.orderFindingPeakBalanced P` (balanced, a function of the spare capacities the allocator
gives the registers). This file adds what the numerals of a *concrete* policy need:

* `reference2048PeakBalanced_policyU` evaluates the balanced budget with **no capacity
  hypothesis**. The reference layout is sized so that the default rule's plan fits at every
  site (`Balanced.reference_fits`), and where every plan fits the balanced count is the
  width-only count of `balanceU` (`orderFindingQubitsBalanced_eq_U`). So the balanced reference
  circuit of any admissible policy peaks at the base registers plus
  `Policy.orderFindingPeakU P Balanced.defaultRule`, a function of the register widths only, with
  nothing to assume about the allocator's reserves.
* `ReferencePeakIs P N`, `ReferenceBalancedPeakIs P N`, `ReferenceBalancedUPeakIs P N` are the
  public claims "the reference 2048-bit circuit of `P` (plain, balanced, every site split)
  peaks at `xW + 8795 + N` qubits, `xW` the exponent width (4095 or 4096), counted with the
  negation method `P.negation`", and `referencePeakIs_of` and friends turn two kernel-evaluated
  budgets (one per exponent width) into them. The per-policy files in this folder state the
  budgets as numerals and close them with `decide +kernel`.

`8795` is the data register with its carry bit (2049), the work register (2347), the scratch
register (4398) and the flag.
-/

namespace Shor
namespace QubitCount

open _root_.Shor.Balanced

/-! ## The balanced reference circuit, with no capacity hypothesis -/

/-- For every 2048-bit modulus and every admissible policy `P`, the balanced reference circuit
(`Balanced.defaultRule`), counted with `P.negation`, peaks at the base registers plus
`Policy.orderFindingPeakU P Balanced.defaultRule` at the reference widths, with no hypothesis on
the spare capacities: the reference layout holds every site's plan
(`Balanced.reference_fits`), so the balanced count is the width-only count. -/
theorem reference2048PeakBalanced_policyU (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    let layout := Reference.allocateReferenceLayout P inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Balanced.balancedShorCircuit P Balanced.defaultRule inst Reference.m2048
    g.peakQubitsFor P.negation L0
      = Reference.referenceXWidth inst + 8795
        + Policy.orderFindingPeakU P Balanced.defaultRule (Reference.referenceXWidth inst)
          2048 2347 4398 ∧
    g.peakQubitsFor P.negation ∅
      ≤ Reference.referenceXWidth inst + 8795
        + Policy.orderFindingPeakU P Balanced.defaultRule (Reference.referenceXWidth inst)
          2048 2347 4398 := by
  have h := reference2048PeakBalanced_policy P hP Balanced.defaultRule inst hN
  obtain ⟨hd, hw, hs, hx⟩ := reference_widths_2048 hN
  have hxw : (Reference.allocateReferenceLayout P inst Reference.m2048).x.width
      = Reference.referenceXWidth inst :=
    Reference.allocateReferenceLayout_x_width P inst Reference.m2048
  have hdw : (Reference.allocateReferenceLayout P inst Reference.m2048).data.width
      = Reference.referenceDataWidth inst :=
    Reference.allocateReferenceLayout_data_width P inst Reference.m2048
  have hww : (Reference.allocateReferenceLayout P inst Reference.m2048).work.width
      = Reference.referenceWorkWidth inst Reference.m2048 :=
    Reference.allocateReferenceLayout_work_width P inst Reference.m2048
  have hsw : (Reference.allocateReferenceLayout P inst Reference.m2048).scratch.width
      = Reference.referenceScratchWidth inst Reference.m2048 :=
    Reference.allocateReferenceLayout_scratch_width P inst Reference.m2048
  have hx0 : (Reference.allocateReferenceLayout P inst Reference.m2048).x.width ≠ 0 := by
    rw [hxw]; omega
  have hcore := coreFits_of_fits P Balanced.defaultRule inst.a inst.N _ _ _ _ _
    (Reference.reference_modMulCircuitWorkspaceOK P inst Reference.m2048)
    (Reference.reference_step4Workspace P inst Reference.m2048)
    (Balanced.reference_fits P inst Reference.m2048) hx0
  have hsites := coreFits_sites P Balanced.defaultRule
    (Reference.reference_modMulCircuitWorkspaceOK P inst Reference.m2048)
    (Reference.reference_step4Workspace P inst Reference.m2048) hcore
  have heq := orderFindingQubitsBalanced_eq_U P Balanced.defaultRule
    (Reference.allocateReferenceLayout P inst Reference.m2048).x.width
    (Reference.allocateReferenceLayout P inst Reference.m2048).data.width
    (Reference.allocateReferenceLayout P inst Reference.m2048).data.capacity
    (Reference.allocateReferenceLayout P inst Reference.m2048).work.width
    (Reference.allocateReferenceLayout P inst Reference.m2048).work.capacity
    (Reference.allocateReferenceLayout P inst Reference.m2048).scratch.width
    (Reference.allocateReferenceLayout P inst Reference.m2048).scratch.capacity hsites
  simp only [Policy.orderFindingQubitsBalanced, Policy.orderFindingQubitsU] at heq
  rw [hxw, hdw, hww, hsw, hd, hw, hs] at heq
  have hpeak : Policy.orderFindingPeakBalanced P Balanced.defaultRule
        (Reference.referenceXWidth inst) 2048
        (Reference.allocateReferenceLayout P inst Reference.m2048).data.capacity 2347
        (Reference.allocateReferenceLayout P inst Reference.m2048).work.capacity 4398
        (Reference.allocateReferenceLayout P inst Reference.m2048).scratch.capacity
      = Policy.orderFindingPeakU P Balanced.defaultRule (Reference.referenceXWidth inst)
          2048 2347 4398 := by
    omega
  dsimp only at h ⊢
  rw [hpeak] at h
  exact h

/-! ## The claims -/

/-- **The reference 2048-bit circuit of `P` peaks at `xW + 8795 + N` qubits**, `xW` the
exponent register's width (4095 or 4096), counted with the negation method `P.negation`: from
the base set it is exactly that, and from an empty start it never exceeds `4096 + 8795 + N`. -/
def ReferencePeakIs (P : ShorLoweringPolicy) (N : ℕ) : Prop :=
  ∀ inst : ShorOrderFindingInstance, Is2048Bit inst.N →
    let layout := Reference.allocateReferenceLayout P inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Reference.referenceShorCircuit P inst Reference.m2048
    (Reference.referenceXWidth inst = 4095 ∨ Reference.referenceXWidth inst = 4096) ∧
    g.peakQubitsFor P.negation L0 = Reference.referenceXWidth inst + 8795 + N ∧
    g.peakQubitsFor P.negation ∅ ≤ 4096 + 8795 + N

/-- The same for the balanced reference circuit (`Balanced.balancedShorCircuit` with the
default rule). -/
def ReferenceBalancedPeakIs (P : ShorLoweringPolicy) (N : ℕ) : Prop :=
  ∀ inst : ShorOrderFindingInstance, Is2048Bit inst.N →
    let layout := Reference.allocateReferenceLayout P inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Balanced.balancedShorCircuit P Balanced.defaultRule inst Reference.m2048
    (Reference.referenceXWidth inst = 4095 ∨ Reference.referenceXWidth inst = 4096) ∧
    g.peakQubitsFor P.negation L0 = Reference.referenceXWidth inst + 8795 + N ∧
    g.peakQubitsFor P.negation ∅ ≤ 4096 + 8795 + N

/-- The same for the reference circuit with every site split (`Balanced.balancedUShorCircuit`,
which is the balanced circuit at the reference layout: `balancedUShorCircuit_eq`). -/
def ReferenceBalancedUPeakIs (P : ShorLoweringPolicy) (N : ℕ) : Prop :=
  ∀ inst : ShorOrderFindingInstance, Is2048Bit inst.N →
    let layout := Reference.allocateReferenceLayout P inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Balanced.balancedUShorCircuit P Balanced.defaultRule inst Reference.m2048
      (Balanced.reference_fits P inst Reference.m2048)
    (Reference.referenceXWidth inst = 4095 ∨ Reference.referenceXWidth inst = 4096) ∧
    g.peakQubitsFor P.negation L0 = Reference.referenceXWidth inst + 8795 + N ∧
    g.peakQubitsFor P.negation ∅ ≤ 4096 + 8795 + N

/-- From the two kernel-evaluated budgets (4096 and 4095 exponent qubits). -/
theorem referencePeakIs_of (P : ShorLoweringPolicy) (hP : P.Admissible) {N : ℕ}
    (h6 : Policy.orderFindingPeak P 4096 2048 2347 4398 = N)
    (h5 : Policy.orderFindingPeak P 4095 2048 2347 4398 = N) : ReferencePeakIs P N := by
  intro inst hN
  obtain ⟨hx, h1, h2⟩ := reference2048Peak_policy P hP inst hN
  refine ⟨hx, ?_, ?_⟩
  · rcases hx with hx | hx <;> rw [hx] at h1 <;> simp only [hx] <;> omega
  · rcases hx with hx | hx <;> rw [hx] at h2 <;> omega

/-- From the two kernel-evaluated width-only budgets (4096 and 4095 exponent qubits). -/
theorem referenceBalancedPeakIs_of (P : ShorLoweringPolicy) (hP : P.Admissible) {N : ℕ}
    (h6 : Policy.orderFindingPeakU P Balanced.defaultRule 4096 2048 2347 4398 = N)
    (h5 : Policy.orderFindingPeakU P Balanced.defaultRule 4095 2048 2347 4398 = N) :
    ReferenceBalancedPeakIs P N := by
  intro inst hN
  obtain ⟨hd, hw, hs, hx⟩ := reference_widths_2048 hN
  obtain ⟨h1, h2⟩ := reference2048PeakBalanced_policyU P hP inst hN
  refine ⟨hx, ?_, ?_⟩
  · rcases hx with hx | hx
    · rw [hx, h5] at h1; simpa [hx] using h1
    · rw [hx, h6] at h1; simpa [hx] using h1
  · rcases hx with hx | hx
    · rw [hx, h5] at h2; omega
    · rw [hx, h6] at h2; omega

/-- The balanced and the every-site-split reference circuits are the same circuit. -/
theorem referenceBalancedUPeakIs_of (P : ShorLoweringPolicy) {N : ℕ}
    (h : ReferenceBalancedPeakIs P N) : ReferenceBalancedUPeakIs P N := by
  intro inst hN
  have := h inst hN
  dsimp only at this ⊢
  rw [Balanced.balancedUShorCircuit_eq]
  exact this

#assert_axioms _root_.Shor.QubitCount.reference2048PeakBalanced_policyU
#assert_axioms _root_.Shor.QubitCount.referencePeakIs_of
#assert_axioms _root_.Shor.QubitCount.referenceBalancedPeakIs_of
#assert_axioms _root_.Shor.QubitCount.referenceBalancedUPeakIs_of

end QubitCount
end Shor
