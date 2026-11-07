import ForShor.ShorVerification.Implementation.QubitCount.Proofs.BalancedU
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.Numerals

/-!
# Qubit count: the peak of an arbitrary policy

The interface for costing a policy at the 2048-bit reference widths, under either
negation method.

* `Policy.orderFindingPeakUnder P m` is the closed-form peak extra qubits of the
  order-finding circuit of `P`'s bands and width rule with the negations built by `m`.
  It is `Policy.orderFindingPeak (P.withNegation m)`, and `Policy.orderFindingPeak P` is
  `Policy.orderFindingPeakUnder P P.negation`, by `rfl`. The balanced counts have the same
  two forms.
* `reference2048Peak_policy` reduces the peak of the reference circuit of an
  admissible policy `P` at any 2048-bit modulus to `Policy.orderFindingPeak P` at the
  reference widths, and `reference2048PeakBalanced_policy` the peak of the balanced
  reference circuit to `Policy.orderFindingPeakBalanced P` at the reference widths and
  the capacities the allocator gives. Both are counted with `P.negation`, so a policy that
  names `negation := .scratch` is counted with the register-wide charge and one that names
  no method with the one-qubit charge.

The budgets are plain arithmetic on fuel (`peakReserveD` and the like) and are meant to be
evaluated by the kernel on a concrete policy (`decide +kernel`).
-/

namespace Shor
namespace QubitCount

/-! ## The closed forms, by method -/

/-- Peak extra qubits of the order-finding circuit of `P`'s bands and width rule with the
negations built by `m`, phase products lowered directly. -/
def Policy.orderFindingPeakUnder (P : ShorLoweringPolicy) (m : NegationMethod)
    (xW dW wW sW : ℕ) : ℕ :=
  orderFindingPeakD m P.widthRule (Policy.compile P) xW dW wW sW

/-- Peak extra qubits of the balanced order-finding circuit of `P`'s bands and width rule
with the negations built by `m`. -/
def Policy.orderFindingPeakBalancedUnder (P : ShorLoweringPolicy) (m : NegationMethod)
    (Rule : Balanced.Rule) (xW dW dC wW wC sW sC : ℕ) : ℕ :=
  orderFindingPeakBalancedD m P.widthRule (Policy.compile P) Rule xW dW dC wW wC sW sC

/-- Peak extra qubits of the unconditionally balanced order-finding circuit of `P`'s bands and
width rule with the negations built by `m`. -/
def Policy.orderFindingPeakUUnder (P : ShorLoweringPolicy) (m : NegationMethod)
    (Rule : Balanced.Rule) (xW dW wW sW : ℕ) : ℕ :=
  orderFindingPeakUD m P.widthRule (Policy.compile P) Rule xW dW wW sW

theorem Policy.orderFindingPeak_eq_under (P : ShorLoweringPolicy) (xW dW wW sW : ℕ) :
    Policy.orderFindingPeak P xW dW wW sW = Policy.orderFindingPeakUnder P P.negation xW dW wW sW :=
  rfl

theorem Policy.orderFindingPeak_withNegation (P : ShorLoweringPolicy) (m : NegationMethod)
    (xW dW wW sW : ℕ) :
    Policy.orderFindingPeak (P.withNegation m) xW dW wW sW
      = Policy.orderFindingPeakUnder P m xW dW wW sW :=
  rfl

theorem Policy.orderFindingPeakBalanced_eq_under (P : ShorLoweringPolicy) (Rule : Balanced.Rule)
    (xW dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingPeakBalanced P Rule xW dW dC wW wC sW sC
      = Policy.orderFindingPeakBalancedUnder P P.negation Rule xW dW dC wW wC sW sC :=
  rfl

theorem Policy.orderFindingPeakBalanced_withNegation (P : ShorLoweringPolicy) (m : NegationMethod)
    (Rule : Balanced.Rule) (xW dW dC wW wC sW sC : ℕ) :
    Policy.orderFindingPeakBalanced (P.withNegation m) Rule xW dW dC wW wC sW sC
      = Policy.orderFindingPeakBalancedUnder P m Rule xW dW dC wW wC sW sC :=
  rfl

theorem Policy.orderFindingPeakU_withNegation (P : ShorLoweringPolicy) (m : NegationMethod)
    (Rule : Balanced.Rule) (xW dW wW sW : ℕ) :
    Policy.orderFindingPeakU (P.withNegation m) Rule xW dW wW sW
      = Policy.orderFindingPeakUUnder P m Rule xW dW wW sW :=
  rfl

/-- Step 3's peak under the `oneQubit` method. -/
theorem step3Peak_oneQubit (sW : ℕ) : step3Peak .oneQubit sW = 3 := rfl

/-- Step 3's peak under the `scratch` method, for a scratch register of at least one qubit. -/
theorem step3Peak_scratch (sW : ℕ) (h : 1 ≤ sW) : step3Peak .scratch sW = sW + 2 := by
  simp only [step3Peak, negationScratch]
  omega

/-! ## The reference circuit at 2048 bits, for any admissible policy -/

/-- For every 2048-bit modulus and every admissible policy `P`, the reference circuit's
peak, scratch included and counted with `P.negation`, is the base registers plus
`Policy.orderFindingPeak P` at the reference widths: the exponent register
(`referenceXWidth inst`, 4095 or 4096 qubits), data 2048, work 2347 and scratch 4398. From an
empty start it never exceeds that. -/
theorem reference2048Peak_policy (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    let layout := Reference.allocateReferenceLayout P inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Reference.referenceShorCircuit P inst Reference.m2048
    (Reference.referenceXWidth inst = 4095 ∨ Reference.referenceXWidth inst = 4096) ∧
    g.peakQubitsFor P.negation L0
      = Reference.referenceXWidth inst + 8795
        + Policy.orderFindingPeak P (Reference.referenceXWidth inst) 2048 2347 4398 ∧
    g.peakQubitsFor P.negation ∅
      ≤ Reference.referenceXWidth inst + 8795
        + Policy.orderFindingPeak P (Reference.referenceXWidth inst) 2048 2347 4398 := by
  dsimp only
  obtain ⟨hd, hw, hs, hx⟩ := reference_widths_2048 hN
  have hp := referencePeakFormula P hP inst Reference.m2048
  dsimp only at hp
  rw [Policy.orderFindingQubits, hd, hw, hs] at hp
  have hbase : Reference.referenceXWidth inst + (2048 + 1) + 2347 + 4398 + 1
      = Reference.referenceXWidth inst + 8795 := by
    omega
  rw [hbase] at hp
  have hmono := (mono (scratchFor P.negation) (Reference.referenceShorCircuit P inst Reference.m2048)
    true (Finset.empty_subset (orderFindingBaseSet
      (Reference.allocateReferenceLayout P inst Reference.m2048).x
      (Reference.allocateReferenceLayout P inst Reference.m2048).data
      (Reference.allocateReferenceLayout P inst Reference.m2048).work
      (Reference.allocateReferenceLayout P inst Reference.m2048).scratch
      (Reference.allocateReferenceLayout P inst Reference.m2048).flag))).2
  simp only [LowGate.peakQubitsFor] at hp hmono ⊢
  exact ⟨hx, hp, hmono.trans hp.le⟩

/-- The balanced reference circuit of an admissible policy `P` at a 2048-bit modulus, counted
with `P.negation`: its peak is the base registers plus `Policy.orderFindingPeakBalanced P` at
the reference widths and the spare capacities the allocator gives the data, work and scratch
registers. From an empty start it never exceeds that. -/
theorem reference2048PeakBalanced_policy (P : ShorLoweringPolicy) (hP : P.Admissible)
    (R : Balanced.Rule) (inst : ShorOrderFindingInstance) (hN : Is2048Bit inst.N) :
    let layout := Reference.allocateReferenceLayout P inst Reference.m2048
    let L0 := orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag
    let g := Balanced.balancedShorCircuit P R inst Reference.m2048
    g.peakQubitsFor P.negation L0
      = Reference.referenceXWidth inst + 8795
        + Policy.orderFindingPeakBalanced P R (Reference.referenceXWidth inst) 2048
          layout.data.capacity 2347 layout.work.capacity 4398 layout.scratch.capacity ∧
    g.peakQubitsFor P.negation ∅
      ≤ Reference.referenceXWidth inst + 8795
        + Policy.orderFindingPeakBalanced P R (Reference.referenceXWidth inst) 2048
          layout.data.capacity 2347 layout.work.capacity 4398 layout.scratch.capacity := by
  dsimp only
  obtain ⟨hd, hw, hs, hx⟩ := reference_widths_2048 hN
  have hlay : OrderFindingSpaceLayout
      (Reference.allocateReferenceLayout P inst Reference.m2048).x
      (Reference.allocateReferenceLayout P inst Reference.m2048).data
      (Reference.allocateReferenceLayout P inst Reference.m2048).work
      (Reference.allocateReferenceLayout P inst Reference.m2048).scratch
      (Reference.allocateReferenceLayout P inst Reference.m2048).flag :=
    ⟨Reference.reference_exponent_data_disjoint P inst Reference.m2048,
     Reference.reference_exponent_work_disjoint P inst Reference.m2048,
     Reference.reference_exponent_scratch_disjoint P inst Reference.m2048,
     Reference.reference_flag_outside_exponent P inst Reference.m2048⟩
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
  have hp := orderFindingPeakFormulaBalanced P R hP inst.a inst.N
    (Reference.allocateReferenceLayout P inst Reference.m2048).x
    (Reference.allocateReferenceLayout P inst Reference.m2048).data
    (Reference.allocateReferenceLayout P inst Reference.m2048).work
    (Reference.allocateReferenceLayout P inst Reference.m2048).scratch
    (Reference.allocateReferenceLayout P inst Reference.m2048).flag
    (Reference.reference_modMulCircuitWorkspaceOK P inst Reference.m2048)
    (Reference.reference_step4Workspace P inst Reference.m2048)
    (Reference.reference_gateWorkspaceOK P inst Reference.m2048) hlay
  rw [Policy.orderFindingQubitsBalanced, hxw, hdw, hww, hsw, hd, hw, hs] at hp
  have hbase : Reference.referenceXWidth inst + (2048 + 1) + 2347 + 4398 + 1
      = Reference.referenceXWidth inst + 8795 := by
    omega
  rw [hbase] at hp
  have hmono := (mono (scratchFor P.negation) (Balanced.balancedShorCircuit P R inst Reference.m2048)
    true (Finset.empty_subset (orderFindingBaseSet
      (Reference.allocateReferenceLayout P inst Reference.m2048).x
      (Reference.allocateReferenceLayout P inst Reference.m2048).data
      (Reference.allocateReferenceLayout P inst Reference.m2048).work
      (Reference.allocateReferenceLayout P inst Reference.m2048).scratch
      (Reference.allocateReferenceLayout P inst Reference.m2048).flag))).2
  change LowGate.peakQubitsFor P.negation (Balanced.balancedShorCircuit P R inst Reference.m2048) _
    = _ at hp
  simp only [LowGate.peakQubitsFor] at hp hmono ⊢
  exact ⟨hp, hmono.trans hp.le⟩

end QubitCount
end Shor
