import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Layout
import ForShor.ShorVerification.Implementation.Shor.Main

/-!
# Reference: readiness

From the framework's all-zero initial state, every layout satisfies the
preconditions of the lowered Shor correctness theorem: the approximate setup is
valid, the reserves are large enough and isolated, and every workspace qubit is
clean (`referenceLayout_ready`). The circuit's own precondition follows:
`reference_ready`.
-/

namespace Shor
namespace Reference

universe u

/-! ## The all-zero state is zero on every register -/

@[simp] private theorem toNat_ground_zero {Basis : Type u} [RegEncoding Basis] (r : Reg) :
    RegEncoding.toNat r (RegEncoding.zero (Basis := Basis)) = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro i
  by_cases hi : i < regSize r
  · let j : Fin (regSize r) := ⟨i, hi⟩
    have hbit :=
      RegEncoding.bit_eq_testBit_toNat (r := r) (b := RegEncoding.zero (Basis := Basis)) j
    calc
      Nat.testBit (RegEncoding.toNat r (RegEncoding.zero (Basis := Basis))) i
          = RegEncoding.bit (r.get j) (RegEncoding.zero (Basis := Basis)) := by
            simpa [j] using hbit.symm
      _ = false := RegEncoding.bit_zero _
  · have hwidth : regSize r ≤ i := Nat.le_of_not_gt hi
    have hlt : RegEncoding.toNat r (RegEncoding.zero (Basis := Basis)) < 2 ^ regSize r := by
      simpa [ASize] using
        (RegEncoding.toNat_lt_ASize (r := r) (b := RegEncoding.zero (Basis := Basis)))
    have hpow : 2 ^ regSize r ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hwidth
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt hpow)

@[simp] private theorem freshZero_ground_zero {Basis : Type u} [RegEncoding Basis] (r : Reg) :
    FreshZero r (RegEncoding.zero (Basis := Basis)) := by
  unfold FreshZero
  exact toNat_ground_zero r

@[simp] private theorem freshFor_ground_zero {Basis : Type u} [RegEncoding Basis] (e : ExtReg)
    (n : ℕ) : e.FreshFor n (RegEncoding.zero (Basis := Basis)) := by
  unfold ExtReg.FreshFor
  exact freshZero_ground_zero _

/-! ## The approximate setup -/

variable {qs : QSemantics} [RegEncoding qs.Basis]
variable (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ)

/-- The layout satisfies `ShorApproxSetupMinimal` in the all-zero state. -/
def referenceApproxSetupMinimal :
    ShorApproxSetupMinimal qs (referencePrecision m) inst.N (referenceX P inst m)
      (referenceData P inst m) (referenceWork P inst m) (referenceScratch P inst m)
      (referenceFlag P inst m) (RegEncoding.zero (Basis := qs.Basis)) where
  step4_workspace := reference_step4Workspace P inst m
  exponent_data_disjoint := reference_exponent_data_disjoint P inst m
  algorithm1_precision := reference_algorithm1Precision P inst m
  exponent_zero := toNat_ground_zero (referenceX P inst m).active
  data_zero := toNat_ground_zero (referenceData P inst m).active
  work_zero := toNat_ground_zero (referenceWork P inst m).active
  scratch_zero := toNat_ground_zero (referenceScratch P inst m).active
  flag_zero := toNat_ground_zero (qubitReg (referenceFlag P inst m))

/-- `referenceApproxSetupMinimal` through `allocateReferenceLayout`. -/
def allocatedReferenceApproxSetupMinimal :
    ShorApproxSetupMinimal qs (referencePrecision m) inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag (RegEncoding.zero (Basis := qs.Basis)) := by
  simpa [allocateReferenceLayout] using referenceApproxSetupMinimal (qs := qs) P inst m

/-! ## Clean, large enough, isolated -/

theorem referenceWorkspaceCleanInput :
    ShorWorkspaceCleanInput (referenceX P inst m) (referenceData P inst m) (referenceWork P inst m)
      (referenceScratch P inst m) (RegEncoding.zero (Basis := qs.Basis)) := by
  unfold ShorWorkspaceCleanInput
  exact ⟨freshZero_ground_zero (referenceX P inst m).reserve,
    freshZero_ground_zero (referenceData P inst m).reserve,
    freshZero_ground_zero (referenceWork P inst m).reserve,
    freshZero_ground_zero (referenceScratch P inst m).reserve⟩

theorem allocatedReferenceWorkspaceCleanInput :
    ShorWorkspaceCleanInput (allocateReferenceLayout P inst m).x
      (allocateReferenceLayout P inst m).data (allocateReferenceLayout P inst m).work
      (allocateReferenceLayout P inst m).scratch (RegEncoding.zero (Basis := qs.Basis)) := by
  simpa [allocateReferenceLayout] using referenceWorkspaceCleanInput (qs := qs) P inst m

theorem allocatedReferenceWorkspaceLargeEnough :
    Policy.ShorWorkspaceLargeEnough P (allocateReferenceLayout P inst m).x
      (allocateReferenceLayout P inst m).data (allocateReferenceLayout P inst m).work
      (allocateReferenceLayout P inst m).scratch := by
  simpa [allocateReferenceLayout] using reference_shorWorkspaceLargeEnough P inst m

theorem allocatedReferenceWorkspaceIsolation :
    ShorWorkspaceIsolation (allocateReferenceLayout P inst m).x
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag := by
  simpa [allocateReferenceLayout] using reference_shorWorkspaceIsolation P inst m

/-! ## Readiness -/

/-- Every precondition of the lowered Shor correctness theorem holds of the layout
in the all-zero state: no caller supplies a reserve-size, disjointness, layout or
cleanliness hypothesis. -/
def referenceLayout_ready :
    LoweredShorReady qs P (referencePrecision m) inst.a inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag (RegEncoding.zero (Basis := qs.Basis)) where
  approx := allocatedReferenceApproxSetupMinimal (qs := qs) P inst m
  workspace_large_enough := allocatedReferenceWorkspaceLargeEnough P inst m
  workspace_isolated := allocatedReferenceWorkspaceIsolation P inst m
  workspace_initially_zero := allocatedReferenceWorkspaceCleanInput (qs := qs) P inst m

/-- The full approximate-Shor setup, from the readiness package. -/
noncomputable def referenceApproxSetup :
    ShorApproxSetup qs (referencePrecision m) inst.N
      (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag (RegEncoding.zero (Basis := qs.Basis)) :=
  (referenceLayout_ready (qs := qs) P inst m).toShorApproxSetup

/-- The lowering's workspace, through the setup. -/
theorem referenceLowerWorkspace :
    Policy.GateWorkspaceOK P
      (orderFindingApprox inst.a inst.N (allocateReferenceLayout P inst m).x
        (allocateReferenceLayout P inst m).data (allocateReferenceLayout P inst m).work
        (allocateReferenceLayout P inst m).scratch (allocateReferenceLayout P inst m).flag
        (referenceApproxSetup (qs := qs) P inst m).circuit_workspace
        (referenceApproxSetup (qs := qs) P inst m).step4_workspace) :=
  gateWorkspaceOK_orderFindingApprox (P := P) (η := referencePrecision m) (a := inst.a)
    (N := inst.N) (x := (allocateReferenceLayout P inst m).x)
    (data := (allocateReferenceLayout P inst m).data)
    (work := (allocateReferenceLayout P inst m).work)
    (scratch := (allocateReferenceLayout P inst m).scratch)
    (flag := (allocateReferenceLayout P inst m).flag)
    (b0 := RegEncoding.zero (Basis := qs.Basis))
    (referenceApproxSetup (qs := qs) P inst m)
    (allocatedReferenceWorkspaceLargeEnough P inst m)

/-- The lowering's workspace, from the static layout facts alone: no semantics. -/
theorem reference_gateWorkspaceOK :
    Policy.GateWorkspaceOK P
      (orderFindingApprox inst.a inst.N (allocateReferenceLayout P inst m).x
        (allocateReferenceLayout P inst m).data (allocateReferenceLayout P inst m).work
        (allocateReferenceLayout P inst m).scratch (allocateReferenceLayout P inst m).flag
        (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m)) := by
  have hlayout :
      ModExpLayout (allocateReferenceLayout P inst m).x.active
        (allocateReferenceLayout P inst m).data (allocateReferenceLayout P inst m).work
        (allocateReferenceLayout P inst m).flag := by
    simpa [allocateReferenceLayout] using
      modExpLayout_of_disjoint
        (reference_exponent_data_disjoint P inst m)
        (reference_data_work_disjoint P inst m)
        (reference_flag_outside_data P inst m)
        (reference_flag_outside_work P inst m)
        (reference_controls_outside_work P inst m)
        (reference_flag_outside_controls P inst m)
  exact gateWorkspaceOK_orderFindingApprox_of_static P inst.a inst.N
    (allocateReferenceLayout P inst m).x (allocateReferenceLayout P inst m).data
    (allocateReferenceLayout P inst m).work (allocateReferenceLayout P inst m).scratch
    (allocateReferenceLayout P inst m).flag
    (reference_modMulCircuitWorkspaceOK P inst m) (reference_step4Workspace P inst m)
    hlayout (allocatedReferenceWorkspaceLargeEnough P inst m)

/-- The layout is ready: the circuit can be built on it. -/
theorem reference_ready : Ready P inst m where
  layout := reference_layoutOK P inst m
  lowering := reference_gateWorkspaceOK P inst m

end Reference
end Shor
