import ForShor.ShorVerification.Submission.Score
import ForShor.ShorVerification.Implementation.Readout.BalancedShor
import ForShor.ShorVerification.Implementation.Readout.Proofs.ReferenceLayout

/-!
# The certificate every accepted submission gets, for the semiclassical readout

`Submission/Correct.lean` certifies the **coherent** reference program
`referenceProgramAt P hP submissionPrecision inst` (exponent register, inverse QFT, one
measurement of the exponent register): its single-run success probability is at least
`referenceSuccessProbabilityAt submissionPrecision N`, the bound `Submission/Score.lean`
turns into the board's trial count.

This file states and proves the **same bound, at the same precision, for the
semiclassical readout** of the same submission: the measured program
`orderFindingSemiclassicalLow` (one recycled control qubit, `log₂(2N²)` rounds of
`H ; controlled modular multiplier ; feed-forward phase ; H ; measure-and-reset`), built on
the coherent reference layout `allocateReferenceLayout P inst submissionPrecision` with the
control = that layout's first exponent qubit, lowered by the submission's own policy, run
from the all-zero ket. So a board that scores the semiclassical circuit can keep
`submissionSuccessBound` and `submissionTrialCount` unchanged.

## The programs

* `referenceSemiclassicalProgramAt P hP m inst`: the plain lowering `Policy.lowerM P`
  (the counterpart of `referenceProgramAt`, which lowers by `Policy.lowerGate P`);
* `balancedSemiclassicalProgramAt P R m inst`: the guarded balanced lowering, any rule `R`
  (the counterpart of `Balanced.balancedProgramAt`);
* `balancedUSemiclassicalProgramAt P R hfits m inst`: every phase-product site split by `R`,
  for a rule the reference layout fits (`Balanced.ReferenceFits P R`; the default rule
  always does, `Balanced.referenceFits_default`).

A `SemiclassicalProgram` is the lowered measured circuit plus its number of rounds; the
outcome is the record of those rounds read little-endian as an integer in `[0, 2^rounds)`
(`probability_of_success_M`, the same continued-fraction post-processing `r_found` as the
coherent `probability_of_success`).

## How the statements compare with the coherent ones

Same quantifiers and hypotheses: a `ShorPolicySubmission` (or `ShorSubmission`), every
complete continued-fraction search `T`, every order-finding instance. No precision relation
(`η ≤ shorPrecision`) is assumed: as in the coherent proof, the bound used is the uniform
one `κ / log(log₂N+1) − 2·m·√(2·1600·η)` (here `Shor_correct_semiclassical_of_modMul_bound`
at `K = 1600`), which is exactly `referenceRawSuccessProbabilityAt`, then clamped to `[0,1]`.
The lowering-workspace obligation (`MGate.WorkspaceOK`), the semiclassical layout, the clean
start and the zero reserves are discharged at the reference layout from the coherent
reference's own facts (`Readout.referenceSemiclassicalWorkspaceOK`,
`ShorApproxSetup.toSemiclassicalShorSetup`, `SemiclassicalWorkspaceCleanInput.of_shor`); they
are not hypotheses.

Differences, stated exactly:

* **Universe.** The semiclassical success theorems (`Readout/Shor.lean`) are stated for
  `qs : QSemantics.{0}`, so these certificates are too; the coherent ones are
  universe-polymorphic. The standard model `Model.qs` is in universe `0`
  (`Model/Standard/SemiclassicalSubmissionModel.lean` instantiates them there).
* **Success functional.** `probability_of_success_M` on the branching state of
  `MLowGate.eval` replaces `probability_of_success` on the final state of `LowGate` evaluation;
  the post-processing `r_found` and the verifier are the same.
* **Feed-forward phases are exact** (`LowGate.Phase c (ffAngle j r)`, no synthesis error).
  A synthesized rotation's error is budgeted outside Lean; the coherent certificate likewise
  takes the lowered `LowGate` rotations as exact.

## What is NOT claimed

* Nothing about gate counts or qubit counts (the board measures the gate count outside Lean;
  the semiclassical qubit formulas are in `Readout/Cost.lean`).
* Nothing about the emitted IR here. `Emit/` has a semiclassical emitter, the `readout`
  subcommand (`Emit/Lower/Readout.lean`, schema `forshor.mlowgate/v1`, one-band standard
  policy only); `Submission/CorrectSemiclassicalEmit.lean` proves that its Lean term at
  `level = submissionPrecision`, `rounds = referenceXWidth inst` is the circuit certified here
  (`emit_readout_is_certified`). The JSON serialisation itself is not proved.
* The trial-count amplification (`submissionTrialCount_correct`) is about the number
  `submissionSuccessBound N` alone; that a run of the semiclassical program meets that number
  is what `policy_submissionSuccessBound_le_success_semiclassical` adds.
-/

namespace Shor

open Reference Readout

/-! ## The semiclassical programs at the reference layout -/

/-- A lowered measured order-finding program: the circuit and its number of rounds. The
outcome of a run is the record of `rounds` measurements read little-endian. -/
structure SemiclassicalProgram where
  /-- The lowered measured circuit. -/
  circuit : MLowGate
  /-- The number of measured rounds. -/
  rounds : ℕ

namespace Readout

-- `RL` abbreviates the reference layout `allocateReferenceLayout P inst m`.
set_option hygiene false in
local notation "RL" => allocateReferenceLayout P inst m

/-- The semiclassical reference program at precision level `m`: the plain lowering
`Policy.lowerM P` of `orderFindingSemiclassical` on the coherent reference layout at level `m`,
control its first exponent qubit, `regSize x.active = log₂(2N²)` rounds. The admissibility proof
is not used by the construction; it is taken to mirror `referenceProgramAt`. -/
def referenceSemiclassicalProgramAt (P : ShorLoweringPolicy) (_hP : P.Admissible) (m : ℕ)
    (inst : ShorOrderFindingInstance) : SemiclassicalProgram where
  circuit :=
    orderFindingSemiclassicalLow P inst.a inst.N (referenceControl P inst m)
      (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
      (referenceCircuitWorkspace P inst m) (referenceStep4Workspace P inst m)
      (referenceSemiclassicalWorkspaceOK P inst m _)
  rounds := regSize (RL).x.active

/-- The semiclassical reference program with the guarded balanced lowering by rule `R`. -/
def balancedSemiclassicalProgramAt (P : ShorLoweringPolicy) (R : Balanced.Rule) (m : ℕ)
    (inst : ShorOrderFindingInstance) : SemiclassicalProgram where
  circuit :=
    orderFindingSemiclassicalLowBalanced P R inst.a inst.N (referenceControl P inst m)
      (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
      (referenceCircuitWorkspace P inst m) (referenceStep4Workspace P inst m)
      (referenceSemiclassicalWorkspaceOK P inst m _)
  rounds := regSize (RL).x.active

/-- The semiclassical reference program with every phase-product site split by a rule `R`
that the reference layout fits. -/
def balancedUSemiclassicalProgramAt (P : ShorLoweringPolicy) (R : Balanced.Rule)
    (hfits : Balanced.ReferenceFits P R) (m : ℕ) (inst : ShorOrderFindingInstance) :
    SemiclassicalProgram where
  circuit :=
    orderFindingSemiclassicalLowBalancedU P R inst.a inst.N (referenceControl P inst m)
      (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
      (referenceCircuitWorkspace P inst m) (referenceStep4Workspace P inst m)
      (referenceSemiclassicalWorkspaceOK P inst m _)
      (referenceSemiclassicalFits P R hfits inst m _)
  rounds := regSize (RL).x.active

@[simp] theorem referenceSemiclassicalProgramAt_rounds (P : ShorLoweringPolicy)
    (hP : P.Admissible) (m : ℕ) (inst : ShorOrderFindingInstance) :
    (referenceSemiclassicalProgramAt P hP m inst).rounds = Nat.log2 (2 * inst.N ^ 2) :=
  allocateReferenceLayout_x_width P inst m

@[simp] theorem balancedSemiclassicalProgramAt_rounds (P : ShorLoweringPolicy)
    (R : Balanced.Rule) (m : ℕ) (inst : ShorOrderFindingInstance) :
    (balancedSemiclassicalProgramAt P R m inst).rounds = Nat.log2 (2 * inst.N ^ 2) :=
  allocateReferenceLayout_x_width P inst m

@[simp] theorem balancedUSemiclassicalProgramAt_rounds (P : ShorLoweringPolicy)
    (R : Balanced.Rule) (hfits : Balanced.ReferenceFits P R) (m : ℕ)
    (inst : ShorOrderFindingInstance) :
    (balancedUSemiclassicalProgramAt P R hfits m inst).rounds = Nat.log2 (2 * inst.N ^ 2) :=
  allocateReferenceLayout_x_width P inst m

/-! ## The success bound at every precision level -/

section Success

variable {qs : QSemantics.{0}}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]

omit [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs] [LowerGateClass qs] in
/-- The semiclassical success functional is nonnegative. -/
theorem probability_of_success_M_nonneg (T : ℕ → ℕ) (verify : ℕ → Bool) (m r Q : ℕ)
    (ψ : MState qs) : 0 ≤ probability_of_success_M T verify m r Q ψ := by
  unfold probability_of_success_M
  refine Finset.sum_nonneg fun o _ => mul_nonneg ?_ ?_
  · unfold r_found
    split_ifs <;> norm_num
  · unfold recordOutcomeProb
    refine tsum_nonneg fun rec => ?_
    split_ifs
    · unfold recordProb
      positivity
    · exact le_rfl

/-- The high-level semiclassical circuit at the reference layout, run from the all-zero ket,
meets the unclamped declared bound `referenceRawSuccessProbabilityAt m N`. -/
theorem referenceSemiclassical_raw_success (P : ShorLoweringPolicy) (m : ℕ) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) (inst : ShorOrderFindingInstance) :
    referenceRawSuccessProbabilityAt m inst.N ≤
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (2 ^ regSize (RL).x.active)
        ((orderFindingSemiclassical inst.a inst.N (referenceControl P inst m)
            (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
            (referenceCircuitWorkspace P inst m) (referenceStep4Workspace P inst m)).eval
          (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) := by
  let hsetup := (referenceApproxSetup (qs := qs) P inst m).toSemiclassicalShorSetup
    (referenceX_pos P inst m)
  have hb := Shor_correct_semiclassical_of_modMul_bound 1600 (modMul_approx_valid_dist_1600 qs)
    T hT inst (referenceControl P inst m) (RL).x (RL).data (RL).work (RL).scratch (RL).flag _
    (allocateReferenceLayout_x_width P inst m) (allocateReferenceLayout_data_width P inst m) _
    hsetup
  have herr : 2 * (regSize (RL).x.active : ℝ) * Real.sqrt (2 * (1600 * referencePrecision m))
      = referenceApproximationErrorAt m inst.N := by
    rw [allocateReferenceLayout_x_width]
    simp [referenceApproximationErrorAt, referenceK]
  unfold referenceRawSuccessProbabilityAt
  rw [← herr]
  exact hb

/-- Every lowering of the reference semiclassical circuit that evaluates as the circuit from
the all-zero ket meets the declared bound (clamping included). -/
theorem referenceSemiclassical_success_of_eval (P : ShorLoweringPolicy) (m : ℕ) (T : ℕ → ℕ)
    (hT : ContinuedFractionSearchComplete T) (inst : ShorOrderFindingInstance) (C : MLowGate)
    (hC : C.eval (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))
      = (orderFindingSemiclassical inst.a inst.N (referenceControl P inst m)
            (regSize (RL).x.active) (RL).data (RL).work (RL).scratch (RL).flag
            (referenceCircuitWorkspace P inst m) (referenceStep4Workspace P inst m)).eval
          (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) :
    referenceSuccessProbabilityAt m inst.N ≤
      probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
        (regSize (RL).x.active) (ord inst.a inst.N inst.coprime) (2 ^ regSize (RL).x.active)
        (C.eval (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) := by
  rw [hC, referenceSuccessProbabilityAt]
  exact max_le (probability_of_success_M_nonneg _ _ _ _ _ _)
    ((min_le_right _ _).trans (referenceSemiclassical_raw_success P m T hT inst))

/-- **The semiclassical reference program at level `m` meets the coherent reference's
declared bound `referenceSuccessProbabilityAt m N`** — the semiclassical counterpart of
`referenceProgramAt_success`, with the same hypotheses: for every admissible policy, level,
complete continued-fraction search and order-finding instance, the plain-lowered
semiclassical program, run from the all-zero ket, finds the order with at least that
probability. -/
theorem referenceSemiclassicalProgramAt_success (P : ShorLoweringPolicy) (hP : P.Admissible)
    (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (referenceSemiclassicalProgramAt P hP m inst).rounds (ord inst.a inst.N inst.coprime)
          (2 ^ (referenceSemiclassicalProgramAt P hP m inst).rounds)
          ((referenceSemiclassicalProgramAt P hP m inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) := by
  intro T hT inst
  let hsetup := (referenceApproxSetup (qs := qs) P inst m).toSemiclassicalShorSetup
    (referenceX_pos P inst m)
  exact referenceSemiclassical_success_of_eval P m T hT inst _
    (semiclassical_lowerM_eval hP _ _ _ _ _ _ _ _ _ _
      (referenceSemiclassicalWorkspaceOK P inst m _) (referenceSemiclassicalLayout P inst m) _
      (SemiclassicalWorkspaceCleanInput.of_shor
        (allocatedReferenceWorkspaceCleanInput (qs := qs) P inst m))
      hsetup.clean_input.2.2.2.2.2.1)

/-- **The guarded-balanced semiclassical reference program meets the same bound**, for every
rule `R` (the counterpart of `Balanced.balancedProgramAt_success`). -/
theorem balancedSemiclassicalProgramAt_success (P : ShorLoweringPolicy) (hP : P.Admissible)
    (R : Balanced.Rule) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (balancedSemiclassicalProgramAt P R m inst).rounds (ord inst.a inst.N inst.coprime)
          (2 ^ (balancedSemiclassicalProgramAt P R m inst).rounds)
          ((balancedSemiclassicalProgramAt P R m inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) := by
  intro T hT inst
  let hsetup := (referenceApproxSetup (qs := qs) P inst m).toSemiclassicalShorSetup
    (referenceX_pos P inst m)
  exact referenceSemiclassical_success_of_eval P m T hT inst _
    (semiclassical_lowerMBalanced_eval hP R _ _ _ _ _ _ _ _ _ _
      (referenceSemiclassicalWorkspaceOK P inst m _)
      (referenceSemiclassicalLayout P inst m) _
      (SemiclassicalWorkspaceCleanInput.of_shor
        (allocatedReferenceWorkspaceCleanInput (qs := qs) P inst m))
      hsetup.clean_input.2.2.2.2.2.1)

/-- **The every-site-split semiclassical reference program meets the same bound**, for every
rule `R` the reference layout fits. -/
theorem balancedUSemiclassicalProgramAt_success (P : ShorLoweringPolicy) (hP : P.Admissible)
    (R : Balanced.Rule) (hfits : Balanced.ReferenceFits P R) (m : ℕ) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt m inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (balancedUSemiclassicalProgramAt P R hfits m inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (balancedUSemiclassicalProgramAt P R hfits m inst).rounds)
          ((balancedUSemiclassicalProgramAt P R hfits m inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) := by
  intro T hT inst
  let hsetup := (referenceApproxSetup (qs := qs) P inst m).toSemiclassicalShorSetup
    (referenceX_pos P inst m)
  exact referenceSemiclassical_success_of_eval P m T hT inst _
    (semiclassical_lowerMBalancedU_eval hP R _ _ _ _ _ _ _ _ _ _
      (referenceSemiclassicalWorkspaceOK P inst m _) (referenceSemiclassicalFits P R hfits inst m _)
      (referenceSemiclassicalLayout P inst m) _
      (SemiclassicalWorkspaceCleanInput.of_shor
        (allocatedReferenceWorkspaceCleanInput (qs := qs) P inst m))
      hsetup.clean_input.2.2.2.2.2.1)

end Success

end Readout

/-! ## The certificates at `submissionPrecision` -/

section Certificate

variable {qs : QSemantics.{0}}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]

/-- **The semiclassical certificate.** Any policy that can be packaged as a
`ShorPolicySubmission` yields a semiclassical program — its order-finding circuit with the
exponent register replaced by one recycled control qubit measured `log₂(2N²)` times,
lowered by the submission's own policy on the reference layout at the fixed precision
`submissionPrecision` — that meets the SAME declared single-run success bound as the
coherent certificate `policy_submission_correct`, for every order-finding instance and every
complete continued-fraction search. The run starts from the all-zero ket; success means the
record of measurements, read as an integer and post-processed by continued fractions,
returns the order of `a` mod `N`.

Hypotheses are those of `policy_submission_correct`, nothing more; the only differences
are the universe (`QSemantics.{0}`) and the success functional (`probability_of_success_M`
on the measured program). Not claimed: anything about gate or qubit counts, or about the
serialised IR (the link from the `readout` emitter's Lean term to this circuit is
`emit_readout_is_certified`, standard policy only). -/
theorem policy_submission_correct_semiclassical (s : ShorPolicySubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds)
          ((referenceSemiclassicalProgramAt s.policy s.policy_admissible
              submissionPrecision inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) :=
  referenceSemiclassicalProgramAt_success (qs := qs) s.policy s.policy_admissible submissionPrecision

/-- **The semiclassical certificate for a table submission**: `policy_submission_correct_semiclassical`
at the one-band policy, mirroring `submission_correct`. -/
theorem submission_correct_semiclassical (s : ShorSubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (referenceSemiclassicalProgramAt (ShorLoweringPolicy.constPolicy s.table)
            (ShorLoweringPolicy.constPolicy_admissible s.table_admissible)
            submissionPrecision inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (referenceSemiclassicalProgramAt (ShorLoweringPolicy.constPolicy s.table)
            (ShorLoweringPolicy.constPolicy_admissible s.table_admissible)
            submissionPrecision inst).rounds)
          ((referenceSemiclassicalProgramAt (ShorLoweringPolicy.constPolicy s.table)
              (ShorLoweringPolicy.constPolicy_admissible s.table_admissible)
              submissionPrecision inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) :=
  policy_submission_correct_semiclassical (ShorPolicySubmission.ofSetup s)

/-- **The semiclassical certificate, balanced lowering.** As
`policy_submission_correct_semiclassical`, for the guarded balanced lowering by any rule `R`. -/
theorem policy_submission_correct_semiclassical_balanced (s : ShorPolicySubmission)
    (R : Balanced.Rule) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (balancedSemiclassicalProgramAt s.policy R submissionPrecision inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (balancedSemiclassicalProgramAt s.policy R submissionPrecision inst).rounds)
          ((balancedSemiclassicalProgramAt s.policy R submissionPrecision inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) :=
  balancedSemiclassicalProgramAt_success (qs := qs) s.policy s.policy_admissible R
    submissionPrecision

/-- **The semiclassical certificate, every site split.** As
`policy_submission_correct_semiclassical`, for the lowering that splits every phase-product
site by the default rule `Balanced.defaultRule` (which every reference layout fits,
`Balanced.referenceFits_default`): the configuration of `Balanced.balancedUShorImplementation`. -/
theorem policy_submission_correct_semiclassical_balancedU (s : ShorPolicySubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (balancedUSemiclassicalProgramAt s.policy Balanced.defaultRule
            (Balanced.referenceFits_default s.policy) submissionPrecision inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (balancedUSemiclassicalProgramAt s.policy Balanced.defaultRule
            (Balanced.referenceFits_default s.policy) submissionPrecision inst).rounds)
          ((balancedUSemiclassicalProgramAt s.policy Balanced.defaultRule
              (Balanced.referenceFits_default s.policy) submissionPrecision inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) :=
  balancedUSemiclassicalProgramAt_success (qs := qs) s.policy s.policy_admissible
    Balanced.defaultRule (Balanced.referenceFits_default s.policy) submissionPrecision

/-- **The scored bound, semiclassical form**: `policy_submission_correct_semiclassical` with
the board's name `submissionSuccessBound inst.N` (the number `submissionTrialCount` is derived
from) on the left. So the board's trial count needs no change when it scores the
semiclassical program. -/
theorem policy_submissionSuccessBound_le_success_semiclassical (s : ShorPolicySubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      submissionSuccessBound inst.N ≤
        probability_of_success_M T (fun d => decide ((inst.a ^ d) % inst.N = 1))
          (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds
          (ord inst.a inst.N inst.coprime)
          (2 ^ (referenceSemiclassicalProgramAt s.policy s.policy_admissible
            submissionPrecision inst).rounds)
          ((referenceSemiclassicalProgramAt s.policy s.policy_admissible
              submissionPrecision inst).circuit.eval
            (MState.init (qs.ket (RegEncoding.zero (Basis := qs.Basis))))) :=
  policy_submission_correct_semiclassical s

end Certificate

end Shor
