import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceLayout
import FastMultiplication.ShorVerification.Implementation.Workspace.ShorReadiness

namespace Shor
namespace Reference

universe u

noncomputable section

/-!
# Reference Shor readiness

This file discharges the implementation-specific readiness assumptions for the
reference LowGate implementation.

`ReferenceLayout` chooses a deterministic physical register layout.  Here we
show that, when the framework starts from the canonical global zero basis state,

* the approximate Shor setup is valid;
* all implementation reserves are large enough;
* all required register regions are isolated; and
* every reserve/workspace qubit is initially clean.

The main result is `referenceLayout_ready`.
-/

/-! =========================================================
    Section 1: The global zero basis is zero on every register
========================================================= -/

/--
Every finite register encodes the natural number `0` in the canonical ground
basis state.

This is the basic bridge from the framework-level assumption that the entire
physical register file begins in `RegEncoding.zero` to the implementation-level
zero/freshness predicates.
-/
@[simp] private theorem toNat_ground_zero
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg) :
    RegEncoding.toNat r
        (RegEncoding.zero (Basis := Basis)) = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro i

  by_cases hi : i < regSize r
  · let j : Fin (regSize r) := ⟨i, hi⟩

    have hbit :=
      RegEncoding.bit_eq_testBit_toNat
        (r := r)
        (b := RegEncoding.zero (Basis := Basis))
        j

    calc
      Nat.testBit
          (RegEncoding.toNat r
            (RegEncoding.zero (Basis := Basis)))
          i
          =
          RegEncoding.bit
            (r.get j)
            (RegEncoding.zero (Basis := Basis)) := by
              simpa [j] using hbit.symm
      _ = false := RegEncoding.bit_zero _

  · have hwidth : regSize r ≤ i :=
      Nat.le_of_not_gt hi

    have hlt :
        RegEncoding.toNat r
            (RegEncoding.zero (Basis := Basis))
          < 2 ^ regSize r := by
      simpa [ASize] using
        (RegEncoding.toNat_lt_ASize
          (r := r)
          (b := RegEncoding.zero (Basis := Basis)))

    have hpow :
        2 ^ regSize r ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num) hwidth

    exact
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hlt hpow)

/--
Every register is `FreshZero` in the canonical global zero basis state.
-/
@[simp] private theorem freshZero_ground_zero
    {Basis : Type u}
    [RegEncoding Basis]
    (r : Reg) :
    FreshZero r
      (RegEncoding.zero (Basis := Basis)) := by
  unfold FreshZero
  exact toNat_ground_zero r

/--
Every requested prefix of an extended register's reserve is fresh in the
canonical global zero basis state.
-/
@[simp] private theorem freshFor_ground_zero
    {Basis : Type u}
    [RegEncoding Basis]
    (e : ExtReg)
    (n : ℕ) :
    e.FreshFor n
      (RegEncoding.zero (Basis := Basis)) := by
  unfold ExtReg.FreshFor
  exact freshZero_ground_zero _

/-! =========================================================
    Section 2: Minimal approximate-Shor setup
========================================================= -/

/--
The reference allocator automatically satisfies all fields of
`ShorApproxSetupMinimal` in the global zero basis state.

The only hypotheses are the implementation's admissible precision conditions
`0 < η < 1/2`.
-/
theorem referenceApproxSetupMinimal
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ)
    (hηpos : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ)) :
    ShorApproxSetupMinimal
      qs
      η
      (referenceX ops inst η)
      (referenceData ops inst η)
      (referenceWork ops inst η)
      (referenceFlag ops inst η)
      (RegEncoding.zero (Basis := qs.Basis)) := by
  refine
    {
      data_can_grow_two :=
        reference_data_canGrow_two ops inst η

      work_can_grow_one :=
        reference_work_canGrow_one ops inst η

      exponent_data_disjoint :=
        reference_exponent_data_disjoint ops inst η

      data_work_disjoint :=
        reference_data_work_disjoint ops inst η

      flag_outside_data :=
        reference_flag_outside_data ops inst η

      flag_outside_work :=
        reference_flag_outside_work ops inst η

      controls_outside_work :=
        reference_controls_outside_work ops inst η

      flag_outside_controls :=
        reference_flag_outside_controls ops inst η

      algorithm1_precision :=
        reference_algorithm1Precision
          ops inst η hηpos hηhalf

      exponent_zero :=
        toNat_ground_zero
          (referenceX ops inst η).active

      data_zero :=
        toNat_ground_zero
          (referenceData ops inst η).active

      data_fresh :=
        freshFor_ground_zero
          (referenceData ops inst η)
          2

      work_zero :=
        toNat_ground_zero
          (referenceWork ops inst η).active

      work_fresh :=
        freshFor_ground_zero
          (referenceWork ops inst η)
          1

      flag_zero :=
        toNat_ground_zero
          (qubitReg (referenceFlag ops inst η))
    }

/--
`referenceApproxSetupMinimal` stated directly through the packaged
`ReferenceShorLayout`.
-/
theorem allocatedReferenceApproxSetupMinimal
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ)
    (hηpos : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ)) :
    ShorApproxSetupMinimal
      qs
      η
      (allocateReferenceLayout ops inst η).x
      (allocateReferenceLayout ops inst η).data
      (allocateReferenceLayout ops inst η).work
      (allocateReferenceLayout ops inst η).flag
      (RegEncoding.zero (Basis := qs.Basis)) := by
  simpa [allocateReferenceLayout] using
    referenceApproxSetupMinimal
      (qs := qs)
      ops inst η hηpos hηhalf

/-! =========================================================
    Section 3: Global zero implies clean lowering workspace
========================================================= -/

/--
Every reserve allocated by the reference layout is clean in the framework's
canonical global zero basis state.
-/
theorem referenceWorkspaceCleanInput
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ) :
    ShorWorkspaceCleanInput
      (referenceX ops inst η)
      (referenceData ops inst η)
      (referenceWork ops inst η)
      (RegEncoding.zero (Basis := qs.Basis)) := by
  unfold ShorWorkspaceCleanInput
  exact
    ⟨freshZero_ground_zero (referenceX ops inst η).reserve,
      freshZero_ground_zero (referenceData ops inst η).reserve,
      freshZero_ground_zero (referenceWork ops inst η).reserve⟩

/--
The same clean-workspace fact stated through the packaged allocator result.
-/
theorem allocatedReferenceWorkspaceCleanInput
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ) :
    ShorWorkspaceCleanInput
      (allocateReferenceLayout ops inst η).x
      (allocateReferenceLayout ops inst η).data
      (allocateReferenceLayout ops inst η).work
      (RegEncoding.zero (Basis := qs.Basis)) := by
  simpa [allocateReferenceLayout] using
    referenceWorkspaceCleanInput
      (qs := qs)
      ops inst η

/-! =========================================================
    Section 4: Static allocator wrappers
========================================================= -/

/--
The packaged reference layout has enough reserve for the complete Shor
lowering.
-/
theorem allocatedReferenceWorkspaceLargeEnough
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ) :
    ShorWorkspaceLargeEnough
      ops
      (allocateReferenceLayout ops inst η).x
      (allocateReferenceLayout ops inst η).data
      (allocateReferenceLayout ops inst η).work := by
  simpa [allocateReferenceLayout] using
    reference_shorWorkspaceLargeEnough
      ops inst η

/--
The packaged reference layout satisfies the implementation-specific isolation
condition required by lowered Shor.
-/
theorem allocatedReferenceWorkspaceIsolation
    {k : ℕ}
    (ops : Prog k)
    (inst : ShorOrderFindingInstance)
    (η : ℝ) :
    ShorWorkspaceIsolation
      (allocateReferenceLayout ops inst η).x
      (allocateReferenceLayout ops inst η).work
      (allocateReferenceLayout ops inst η).flag := by
  simpa [allocateReferenceLayout] using
    reference_shorWorkspaceIsolation
      ops inst η

/-! =========================================================
    Section 5: Main readiness theorem
========================================================= -/

/--
Main implementation-side readiness theorem.

For any valid order-finding instance and any admissible approximation parameter,
the deterministic reference allocator supplies every implementation-specific
precondition needed by the existing lowered Shor correctness theorem.

In particular, no caller supplies:

* reserve-size hypotheses;
* register-disjointness hypotheses;
* workspace-layout hypotheses; or
* workspace-cleanliness hypotheses.

All of those are discharged by the allocator together with the framework's
canonical `RegEncoding.zero` initial state.
-/
theorem referenceLayout_ready
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (lowering : ShorLoweringSetup)
    (inst : ShorOrderFindingInstance)
    (η : ℝ)
    (hηpos : 0 < η)
    (hηhalf : η < (1 / 2 : ℝ)) :
    LoweredShorReady
      qs
      lowering
      η
      inst.a
      inst.N
      (allocateReferenceLayout lowering.ops inst η).x
      (allocateReferenceLayout lowering.ops inst η).data
      (allocateReferenceLayout lowering.ops inst η).work
      (allocateReferenceLayout lowering.ops inst η).flag
      (RegEncoding.zero (Basis := qs.Basis)) := by
  refine
    {
      approx := ?_
      workspace_large_enough := ?_
      workspace_isolated := ?_
      workspace_initially_zero := ?_
    }

  · exact
      allocatedReferenceApproxSetupMinimal
        (qs := qs)
        lowering.ops
        inst
        η
        hηpos
        hηhalf

  · exact
      allocatedReferenceWorkspaceLargeEnough
        lowering.ops
        inst
        η

  · exact
      allocatedReferenceWorkspaceIsolation
        lowering.ops
        inst
        η

  · exact
      allocatedReferenceWorkspaceCleanInput
        (qs := qs)
        lowering.ops
        inst
        η

end
end Reference
end Shor
