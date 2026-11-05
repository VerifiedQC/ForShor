import ForShor.ShorVerification.Implementation.Reference.Standard.Statement
import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Headline
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Coefficients
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.Table_Generation.Programs.WithProduct
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.GeneratedProgram

/-!
# Reference: the implementation

Every layout is ready, so the circuit, the program and the submitted program are
defined outright; the claims of `Statement.lean` are proved; and
`referenceShorImplementation` packages the result as the framework's
`ShorImplementation`. This file is the way into `Reference/` from outside.
-/

namespace Shor

/-! ## The standard table -/

/-- The standard setup at arity `k`: the generated interpolation-point table
`genOpsWithProduct`. It matches `ShorLoweringSetup.consumes`'s expected point
stream (`genInterpolationPoints k`) exactly. -/
def standardLoweringSetup (k : ℕ) (hk : 1 < k) : ShorLoweringSetup where
  k := k
  hk := hk
  pts := genInterpolationPoints k
  hpts := generatedInterpolationPoints_length k
  good := genInterpolationPoints_good k
  ops := genOpsWithProduct (k := k) (by omega) (genInterpolationPoints k)
  consumes := genOpsWithProduct_ProgConsumesPtsSafe (k := k) (by omega) (genInterpolationPoints k)
  returns := genOpsWithProduct_returns_to_original (k := k) (by omega) (genInterpolationPoints k)

/-- The standard setup, as a one-band policy at threshold `0`. -/
def standardPolicy (k : ℕ) (hk : 1 < k) : ShorLoweringPolicy :=
  ShorLoweringPolicy.constPolicy (standardLoweringSetup k hk).table

/-- The standard policy is admissible. -/
theorem standardPolicy_admissible (k : ℕ) (hk : 1 < k) :
    (standardPolicy k hk).Admissible :=
  ShorLoweringPolicy.constPolicy_admissible (standardLoweringSetup k hk).table_admissible

namespace Reference

/-! ## Readiness -/

theorem referenceReady (P : ShorLoweringPolicy) : ReferenceReady P :=
  fun inst m => reference_ready P inst m

/-! ## The circuit and the programs -/

/-- The lowered order-finding circuit of an instance at precision level `m`. -/
def referenceShorCircuit (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    LowGate :=
  referenceShorCircuitOf (reference_ready P inst m)

/-- The circuit, measuring the exponent register. -/
def referenceShorProg (P : ShorLoweringPolicy) (inst : ShorOrderFindingInstance) (m : ℕ) :
    ShorOrderFindingProgram :=
  referenceProgramOf (reference_ready P inst m)

/-- The reference program at precision level `m`. -/
def referenceProgramAt (P : ShorLoweringPolicy) (_hP : P.Admissible) (m : ℕ)
    (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram :=
  referenceShorProg P inst m

/-- The submitted program: the reference program at the chosen precision. -/
noncomputable def referenceSubmittedProgram (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) : ShorOrderFindingProgram :=
  referenceProgramAt P hP (referenceChosenPrecision inst.N) inst

/-- The logical gate count of the submitted circuit. The asymptotic bounds
(`Shor/Main.lean`) have unnamed constants, so the declared count is the count itself. -/
noncomputable def referenceGateCount (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) : ℕ :=
  LowGate.gateCount shorGateCostModel (referenceSubmittedProgram P hP inst).circuit

theorem referenceGateCount_correct (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) :
    LowGate.gateCount shorGateCostModel (referenceSubmittedProgram P hP inst).circuit =
      referenceGateCount P hP inst :=
  rfl

/-- The single-run gate count of the headline-level circuit of a 2048-bit instance. -/
def headlineGateCount (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) : ℕ :=
  LowGate.gateCount shorGateCostModel (referenceProgramAt P hP m2048 inst).circuit

/-- The gate count over all `headlineTrialCount` runs: what a comparison against
another counted circuit is made on. -/
noncomputable def headlineTotalGateCount (P : ShorLoweringPolicy) (hP : P.Admissible)
    (inst : ShorOrderFindingInstance) : ℕ :=
  headlineTrialCount * headlineGateCount P hP inst

/-! ## The claims, proved -/

section

variable (qs : QSemantics) [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs]
  [LowerGateClass qs]

theorem referenceSuccessAt (P : ShorLoweringPolicy) (hP : P.Admissible) (m : ℕ) :
    ReferenceSuccessAt qs P m :=
  fun T hT inst _ => programOf_success (qs := qs) P hP m T hT inst

theorem referenceCorrect (P : ShorLoweringPolicy) (hP : P.Admissible) : ReferenceCorrect qs P :=
  fun T hT inst _ => submittedProgramOf_correct (qs := qs) P hP T hT inst

end

theorem referenceTrialCount_amplifies : ReferenceTrialCount :=
  referenceTrialCount_correct

theorem headline2048 : Headline2048 :=
  fun _ hN => headline_success_bound hN

theorem headlineTrialCount_amplifies : HeadlineTrialCount :=
  headlineTrialCount_correct

/-! ## The theorems on the programs -/

section

variable {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs]
  [LowerGateClass qs]

/-- The reference program at level `m` achieves its declared bound. -/
theorem referenceProgramAt_success (P : ShorLoweringPolicy) (hP : P.Admissible) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt P hP m inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt P hP m inst).output)
          (C := (referenceProgramAt P hP m inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
  programOf_success (qs := qs) P hP m

/-- The submitted program meets the contract's `correct`. -/
theorem referenceSubmittedProgram_correct (P : ShorLoweringPolicy) (hP : P.Admissible) :
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
          (x := (referenceSubmittedProgram P hP inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceSubmittedProgram P hP inst).output)
          (C := (referenceSubmittedProgram P hP inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
  submittedProgramOf_correct (qs := qs) P hP

/-- A 2048-bit instance at the headline level succeeds with probability at least 99%
of the ideal `κ / log(log₂ N + 1)` baseline. -/
theorem headline_program_success (P : ShorLoweringPolicy) (hP : P.Admissible) {N : ℕ}
    (hN : Is2048Bit N) (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (hinstN : inst.N = N) :
    (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤
      probability_of_success
        (qs := qs)
        (evalC := LowerGateClass.evalL (qs := qs))
        (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (referenceProgramAt P hP m2048 inst).output)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (referenceProgramAt P hP m2048 inst).output)
        (C := (referenceProgramAt P hP m2048 inst).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  have h := referenceProgramAt_success (qs := qs) P hP m2048 T hT inst
  rw [← hinstN] at hN
  exact le_trans (headline_success_bound hN) h

/-! ## The implementation -/

/-- **The reference submission**, as the framework's `ShorImplementation`. -/
noncomputable def referenceShorImplementation (P : ShorLoweringPolicy) (hP : P.Admissible) :
    ShorImplementation (qs := qs) where
  program := referenceSubmittedProgram P hP
  successProbability := referenceSuccessProbability
  correct := referenceSubmittedProgram_correct (qs := qs) P hP
  trialCount := referenceTrialCount
  trialCount_correct := fun N _ => referenceTrialCount_correct N

end

end Reference
end Shor
