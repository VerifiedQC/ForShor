import FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Shor
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation

/-!
# The reference `ShorImplementation` with balanced phase products

`balancedShorImplementation P hP R` is ForShor's reference submission
(`Reference.referenceShorImplementation`) with one change: the order-finding
circuit is lowered after the balancing pass. Same layout
(`allocateReferenceLayout`), same precision choice, same declared success
probability and trial count; the `correct` field is proved by
`balancedProgramAt_prob_eq` (the balanced program has the reference program's
success probability from the framework's initial state) and the reference
program's own correctness.
-/

namespace Shor
namespace Balanced

open Reference

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]

/-- The static workspace of the reference order-finding circuit (a public copy
of `Reference.reference_gateWorkspaceOK_orderFindingApprox`, which is private). -/
theorem reference_gateWorkspaceOK
    (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    Policy.GateWorkspaceOK P
      (orderFindingApprox inst.a inst.N
        (allocateReferenceLayout P inst m).x
        (allocateReferenceLayout P inst m).data
        (allocateReferenceLayout P inst m).work
        (allocateReferenceLayout P inst m).scratch
        (allocateReferenceLayout P inst m).flag
        (reference_modMulCircuitWorkspaceOK P inst m)
        (reference_step4Workspace P inst m)) := by
  have hlayout :
      ModExpLayout
        (allocateReferenceLayout P inst m).x.active
        (allocateReferenceLayout P inst m).data
        (allocateReferenceLayout P inst m).work
        (allocateReferenceLayout P inst m).flag := by
    simpa [allocateReferenceLayout] using
      modExpLayout_of_disjoint
        (reference_exponent_data_disjoint P inst m)
        (reference_data_work_disjoint P inst m)
        (reference_flag_outside_data P inst m)
        (reference_flag_outside_work P inst m)
        (reference_controls_outside_work P inst m)
        (reference_flag_outside_controls P inst m)
  exact
    gateWorkspaceOK_orderFindingApprox_of_static
      P inst.a inst.N
      (allocateReferenceLayout P inst m).x
      (allocateReferenceLayout P inst m).data
      (allocateReferenceLayout P inst m).work
      (allocateReferenceLayout P inst m).scratch
      (allocateReferenceLayout P inst m).flag
      (reference_modMulCircuitWorkspaceOK P inst m)
      (reference_step4Workspace P inst m)
      hlayout
      (allocatedReferenceWorkspaceLargeEnough P inst m)

/-- The reference circuit, balanced. Same layout as `referenceShorCircuit`. -/
def balancedShorCircuit (P : ShorLoweringPolicy) (R : Rule)
    (inst : ShorOrderFindingInstance) (m : ℕ) : LowGate :=
  let layout := allocateReferenceLayout P inst m
  orderFindingApproxLowBalanced P R
    inst.a inst.N layout.x layout.data layout.work layout.scratch layout.flag
    (reference_modMulCircuitWorkspaceOK P inst m)
    (reference_step4Workspace P inst m)
    (reference_gateWorkspaceOK P inst m)

/-- The balanced reference program at precision level `m`. -/
def balancedProgramAt (P : ShorLoweringPolicy) (R : Rule) (m : ℕ)
    (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram where
  circuit := balancedShorCircuit P R inst m
  output := (allocateReferenceLayout P inst m).x.active

/-- From the framework's initial state the balanced and the reference programs
have the same success probability. -/
theorem balancedProgramAt_prob_eq
    (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) (m : ℕ)
    (T : ℕ → ℕ) (inst : ShorOrderFindingInstance) :
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (balancedProgramAt P R m inst).output) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (balancedProgramAt P R m inst).output)
        (C := (balancedProgramAt P R m inst).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))
      =
    probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (referenceProgramAt P hP m inst).output) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (referenceProgramAt P hP m inst).output)
        (C := (referenceProgramAt P hP m inst).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  have hclean :
      Policy.GateWorkspaceCleanState qs P
        (orderFindingApprox inst.a inst.N
          (allocateReferenceLayout P inst m).x
          (allocateReferenceLayout P inst m).data
          (allocateReferenceLayout P inst m).work
          (allocateReferenceLayout P inst m).scratch
          (allocateReferenceLayout P inst m).flag
          (reference_modMulCircuitWorkspaceOK P inst m)
          (reference_step4Workspace P inst m))
        (reference_gateWorkspaceOK P inst m)
        (qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
    (referenceLayout_ready (qs := qs) P inst m).workspace_clean hP
  change probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (allocateReferenceLayout P inst m).x.active) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (allocateReferenceLayout P inst m).x.active)
        (C := Policy.lowerGate P (balance P R _) (balance_ok P R _ (reference_gateWorkspaceOK P inst m)))
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) =
      probability_of_success (qs := qs) (evalC := LowerGateClass.evalL (qs := qs)) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (allocateReferenceLayout P inst m).x.active) (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (allocateReferenceLayout P inst m).x.active)
        (C := Policy.lowerGate P _ (reference_gateWorkspaceOK P inst m))
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis)))
  rw [probability_of_success_balance_eq (qs := qs) P hP R T _ _ _ _ _ _ _ hclean,
    probability_of_success_lowerGate_eq (qs := qs) P hP T _ _ _ _ _ _ _ hclean]

/-- Every fixed-`m` balanced program achieves the reference program's declared bound. -/
theorem balancedProgramAt_success
    (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (balancedProgramAt P R m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (balancedProgramAt P R m inst).output)
          (C := (balancedProgramAt P R m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  rw [balancedProgramAt_prob_eq (qs := qs) P hP R m T inst]
  exact referenceProgramAt_success (qs := qs) P hP m T hT inst

/-- The balanced submitted program (precision chosen as the reference does). -/
noncomputable def balancedSubmittedProgram (P : ShorLoweringPolicy) (R : Rule)
    (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram :=
  balancedProgramAt P R (referenceChosenPrecision inst.N) inst

theorem balancedSubmittedProgram_correct (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      0 ≤ referenceSuccessProbability inst.N ∧
      referenceSuccessProbability inst.N ≤ 1 ∧
      referenceSuccessProbability inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (balancedSubmittedProgram P R inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (balancedSubmittedProgram P R inst).output)
          (C := (balancedSubmittedProgram P R inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  intro T hT inst
  obtain ⟨h0, h1, h2⟩ := referenceSubmittedProgram_correct (qs := qs) P hP T hT inst
  refine ⟨h0, h1, ?_⟩
  unfold balancedSubmittedProgram
  rw [balancedProgramAt_prob_eq (qs := qs) P hP R _ T inst]
  exact h2

/-- **ForShor's reference submission with balanced phase products**, packaged
into the framework's `ShorImplementation` contract. -/
noncomputable def balancedShorImplementation (P : ShorLoweringPolicy) (hP : P.Admissible) (R : Rule) :
    ShorImplementation (qs := qs) where
  program := balancedSubmittedProgram P R
  successProbability := referenceSuccessProbability
  correct := balancedSubmittedProgram_correct (qs := qs) P hP R
  trialCount := referenceTrialCount
  trialCount_correct := by
    intro N _
    apply referenceTrialCount_correct

end Balanced
end Shor
