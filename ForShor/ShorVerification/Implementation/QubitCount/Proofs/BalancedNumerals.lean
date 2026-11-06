import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Numerals
import ForShor.ShorVerification.Implementation.Reference.Balanced.Proofs.Checks

/-!
# Qubit count: the 2048-bit numerals, balanced

The default rule's plans at the four unequal sites of the 2048-bit reference
layout fit the reserves those sites hold, and the balanced budget is 558:
the phase product of Step 1 (a 2049 x 2348 site split into two) with its two
qubits of scratch. Before modular swap 001 the budget was 4400, the negation of
the 4398-qubit scratch register with its unit qubit and its register-wide
constant; the incrementer negation (one clean ancilla) removes that step from
the top.
-/

namespace Shor
namespace QubitCount

open _root_.Shor.Balanced

/-! ## The budgets at the sites -/

/-- The standard `k = 2` table, compiled. -/
abbrev D2 : List (ℕ × TableData) := Policy.compile standardPolicy2

lemma reserveBudgetD_2348_2348 :
    reserveBudgetD standardPolicy2.widthRule D2 2348 2348 = (42708, 42708) := by
  decide +kernel

lemma reserveNeed_2049_2348 : Policy.reserveNeed standardPolicy2 2049 2348 = (43007, 42708) := by
  rw [← reserveBudgetD_eq]; decide +kernel

lemma reserveNeed_2348_2050 : Policy.reserveNeed standardPolicy2 2348 2050 = (42708, 43006) := by
  rw [← reserveBudgetD_eq]; decide +kernel

lemma reserveNeed_2050_2348 : Policy.reserveNeed standardPolicy2 2050 2348 = (43006, 42708) := by
  rw [← reserveBudgetD_eq]; decide +kernel

lemma reserveNeed_2348_4399 : Policy.reserveNeed standardPolicy2 2348 4399 = (87764, 85713) := by
  rw [← reserveBudgetD_eq]; decide +kernel

lemma peakReserveD_2348_2348 : peakReserveD standardPolicy2.widthRule D2 2348 2348 = 257 := by
  decide +kernel

/-! ## The four sites -/

/-- Step 1: the data register with its carry bit, padded to the work register. -/
lemma sitePeak_step1 {cx cz : ℕ} (hx : 43007 ≤ cx) (hz : 42708 ≤ cz) :
    sitePeakD standardPolicy2.widthRule D2 defaultRule 2049 cx 2348 cz = 556 := by
  simp [sitePeakD, sitePeakOf, defaultRule, defaultPlan_2348_2049, planFitsOf,
    reserveBudgetD_2348_2348, splitPeakOf, peakReserveD_2348_2348, hx, hz]

/-- Step 2: the data register with its carry bit and one more, padded. -/
lemma sitePeak_step2 {cx cz : ℕ} (hx : 42708 ≤ cx) (hz : 43006 ≤ cz) :
    sitePeakD standardPolicy2.widthRule D2 defaultRule 2348 cx 2050 cz = 555 := by
  simp [sitePeakD, sitePeakOf, defaultRule, defaultPlan_2348_2050, planFitsOf,
    reserveBudgetD_2348_2348, splitPeakOf, peakReserveD_2348_2348, hx, hz]

/-- Step 4: the scratch register cut into two blocks, both padded to 2348. -/
lemma sitePeak_step4 {cx cz : ℕ} (hx : 42708 ≤ cx) (hz : 43004 ≤ cz) :
    sitePeakD standardPolicy2.widthRule D2 defaultRule 2348 cx 4399 cz = 553 := by
  have h1 : 42709 ≤ cz := by omega
  simp [sitePeakD, sitePeakOf, defaultRule, defaultPlan_4399_2348, planFitsOf,
    reserveBudgetD_2348_2348, splitPeakOf, peakReserveD_2348_2348, hx, hz, h1]

/-- Step 5: as Step 2, operands swapped. -/
lemma sitePeak_step5 {cx cz : ℕ} (hx : 43006 ≤ cx) (hz : 42708 ≤ cz) :
    sitePeakD standardPolicy2.widthRule D2 defaultRule 2050 cx 2348 cz = 555 := by
  simp [sitePeakD, sitePeakOf, defaultRule, defaultPlan_2348_2050, planFitsOf,
    reserveBudgetD_2348_2348, splitPeakOf, peakReserveD_2348_2348, hx, hz]

/-- The balanced budget at the 2048-bit widths, for registers with the spare
qubits the plans need (the scratch register's `4398 + 2` before swap 001 is no longer binding). -/
theorem balancedOrderFindingPeak_2048 {xW dC wC sC : ℕ} (hx : xW = 4095 ∨ xW = 4096)
    (hd : 43009 ≤ dC) (hw : 42709 ≤ wC) (hs : 43005 ≤ sC) :
    Policy.orderFindingPeakBalanced standardPolicy2 defaultRule xW 2048 dC 2347 wC 4398 sC
      = 558 := by
  simp only [Policy.orderFindingPeakBalanced, orderFindingPeakBalancedD, orderFindingPeakWith,
    modMulPeakWith, modMulPhasePeaksWith, Nat.reduceAdd,
    sitePeak_step1 (show 43007 ≤ dC - 2 by omega) (show 42708 ≤ wC - 1 by omega),
    sitePeak_step2 (show 42708 ≤ wC - 1 by omega) (show 43006 ≤ dC - 2 by omega),
    sitePeak_step4 (show 42708 ≤ wC - 1 by omega) (show 43004 ≤ sC - 1 by omega),
    sitePeak_step5 (show 43006 ≤ dC - 2 by omega) (show 42708 ≤ wC - 1 by omega)]
  rcases hx with rfl | rfl <;> decide +kernel

/-! ## The 2048-bit number -/

/-- For every 2048-bit modulus, the reference circuit of `reference2048Peak` lowered
after balancing every site with `Balanced.defaultRule` peaks, scratch included, at
13,449 qubits with 4096 exponent qubits and 13,448 with 4095; from an empty start it
never exceeds 13,449. -/
theorem reference2048PeakBalanced (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    let layout := Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Balanced.balancedShorCircuit standardPolicy2 Balanced.defaultRule inst Reference.m2048
    (Reference.referenceXWidth inst = 4096 → g.peakQubits L0 = 13449) ∧
    (Reference.referenceXWidth inst = 4095 → g.peakQubits L0 = 13448) ∧
    g.peakQubits ∅ ≤ 13449 := by
  dsimp only
  obtain ⟨hd, hw, hs, hx⟩ := reference_widths_2048 hN
  have hP := standardPolicy_admissible 2 (by decide)
  have hlay : OrderFindingSpaceLayout
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).x
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).data
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).work
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).scratch
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).flag :=
    ⟨Reference.reference_exponent_data_disjoint standardPolicy2 inst Reference.m2048,
     Reference.reference_exponent_work_disjoint standardPolicy2 inst Reference.m2048,
     Reference.reference_exponent_scratch_disjoint standardPolicy2 inst Reference.m2048,
     Reference.reference_flag_outside_exponent standardPolicy2 inst Reference.m2048⟩
  have hxw : (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).x.width = Reference.referenceXWidth inst :=
    Reference.allocateReferenceLayout_x_width standardPolicy2 inst Reference.m2048
  have hdw : (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).data.width = Reference.referenceDataWidth inst :=
    Reference.allocateReferenceLayout_data_width standardPolicy2 inst Reference.m2048
  have hww : (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).work.width = Reference.referenceWorkWidth inst Reference.m2048 :=
    Reference.allocateReferenceLayout_work_width standardPolicy2 inst Reference.m2048
  have hsw : (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).scratch.width = Reference.referenceScratchWidth inst Reference.m2048 :=
    Reference.allocateReferenceLayout_scratch_width standardPolicy2 inst Reference.m2048
  have hp := orderFindingPeakFormulaBalanced standardPolicy2 defaultRule hP inst.a inst.N
    (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).x
    (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).data
    (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).work
    (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).scratch
    (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).flag
    (Reference.reference_modMulCircuitWorkspaceOK standardPolicy2 inst Reference.m2048)
    (Reference.reference_step4Workspace standardPolicy2 inst Reference.m2048)
    (Reference.reference_gateWorkspaceOK standardPolicy2 inst Reference.m2048) hlay
  have hcap := Reference.allocatedReferenceWorkspaceLargeEnough standardPolicy2 inst Reference.m2048
  have hD := hcap.data_large_enough
  have hW := hcap.auxiliary_large_enough
  have hS := hcap.scratch_large_enough
  simp only [Policy.shorWorkspaceNeed, shorWorkspaceNeedOf, hdw, hww, hsw, hd, hw, hs,
    Nat.reduceAdd, reserveNeed_2049_2348, reserveNeed_2348_2050, reserveNeed_2050_2348,
    reserveNeed_2348_4399] at hD hW hS
  rw [Policy.orderFindingQubitsBalanced, hxw, hdw, hww, hsw, hd, hw, hs,
    balancedOrderFindingPeak_2048 hx (by omega) (by omega) (by omega)] at hp
  have hbase : Reference.referenceXWidth inst + (2048 + 1) + 2347 + 4398 + 1 + 558
      = Reference.referenceXWidth inst + 9353 := by
    omega
  rw [hbase] at hp
  have hmono := (mono scratch
    (Balanced.balancedShorCircuit standardPolicy2 defaultRule inst Reference.m2048)
    true (Finset.empty_subset (orderFindingBaseSet
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).x
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).data
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).work
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).scratch
      (Reference.allocateReferenceLayout standardPolicy2 inst Reference.m2048).flag))).2
  change LowGate.peakQubits (Balanced.balancedShorCircuit standardPolicy2 defaultRule inst
    Reference.m2048) _ = _ at hp
  simp only [LowGate.peakQubits] at hp hmono ⊢
  refine ⟨fun h => by rw [hp, h], fun h => by rw [hp, h], ?_⟩
  omega

end QubitCount
end Shor
