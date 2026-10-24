import FastMultiplication.ShorVerification.Implementation.Reference.Reference2048Headline

/-!
# The certificate every accepted submission gets

`Submission/Decide.lean` decides whether a table is admissible; this file
says what being admissible *buys*.

The work is already done: `referenceProgramAt_success` is generic in the
policy it is handed, since the correctness chain never looks at the point
values. So there is no per-submission proof obligation and no per-submission
theorem to write. What is left is a choice and a name:

- the **choice** is the precision `m`. The organiser fixes one,
  the same for every submission, so that the declared success bound — and
  therefore the trial count `Submission/Score.lean` derives from it — is a
  per-`N` constant
  rather than something a submitter could tune. `referenceChosenPrecision`,
  the reference construction's own internal `Nat.find`, is deliberately *not*
  used: it only guarantees a positive success probability, with no bound on
  how small.
- the **names** are `policy_submission_correct` and its one-band case
  `submission_correct`, one certificate per accepted submission, so the
  submissions repo has something to point at.

This, `Score.lean` and `Template.lean` are the only `Submission/` files that
reach into `Implementation/`; `Decide.lean` stays implementation-free.
-/

namespace Shor

open Reference

noncomputable section

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]

/-- The one precision level every submission is scored at. `m2048` is the
reference schedule's explicit level for a 2048-bit modulus: `referencePrecision m2048 = 2⁻¹⁵⁰` exactly
(`referencePrecision_m2048`), which
`Reference.headline_success_bound` turns into at least 99% of
the ideal `κ / log(log₂ N + 1)` baseline.

Change it here and nowhere else: `submission_correct` below and
`Submission/Score.lean` both read this. -/
def submissionPrecision : ℕ := m2048

/-- **The certificate.** Any policy that can be packaged as a
`ShorPolicySubmission` — every band passing C1–C4 and the thresholds strictly
decreasing — yields a reference program
that meets the declared single-run success bound at the fixed precision, for
every order-finding instance and every complete continued-fraction search.

This is `referenceProgramAt_success` restated at `submissionPrecision`.
Proving it for a new submission costs nothing, which is what narrowing the
challenge to the table buys. -/
theorem policy_submission_correct (s : ShorPolicySubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt s.policy s.policy_admissible
            submissionPrecision inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt s.policy s.policy_admissible
            submissionPrecision inst).output)
          (C := (referenceProgramAt s.policy s.policy_admissible
            submissionPrecision inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
  referenceProgramAt_success (qs := qs) s.policy s.policy_admissible submissionPrecision

/-- The certificate for a table submission: `policy_submission_correct` at
the one-band policy. -/
theorem submission_correct (s : ShorSubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt (ShorLoweringPolicy.constPolicy s.table)
            (ShorLoweringPolicy.constPolicy_admissible s.table_admissible)
            submissionPrecision inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt (ShorLoweringPolicy.constPolicy s.table)
            (ShorLoweringPolicy.constPolicy_admissible s.table_admissible)
            submissionPrecision inst).output)
          (C := (referenceProgramAt (ShorLoweringPolicy.constPolicy s.table)
            (ShorLoweringPolicy.constPolicy_admissible s.table_admissible)
            submissionPrecision inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
  policy_submission_correct (ShorPolicySubmission.ofSetup s)

end

end Shor
