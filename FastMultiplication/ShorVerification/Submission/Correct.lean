import FastMultiplication.ShorVerification.Implementation.Reference.Reference2048Headline

/-!
# The certificate every accepted submission gets

`SUBMISSION_PLAN.md` S2.2. `Submission/Decide.lean` decides whether a table
is admissible; this file says what being admissible *buys*.

The work is already done: `referenceProgramAt_success` is generic in the
`ShorLoweringSetup` it is handed — it was generic before S1 too, since the
correctness chain never looked at the point values, and S1 made the points a
field rather than a constant without changing that. So there is no
per-submission proof obligation and no per-submission theorem to write. What
is left is a choice and a name:

- the **choice** is the precision `m` (decision P3). The organiser fixes one,
  the same for every submission, so that the declared success bound — and
  therefore the trial count S3 computes from it — is a per-`N` constant
  rather than something a submitter could tune. `referenceChosenPrecision`,
  the reference construction's own internal `Nat.find`, is deliberately *not*
  used: it only guarantees a positive success probability, with no bound on
  how small.
- the **name** is `submission_correct`, one certificate per accepted
  submission, so the submissions repo has something to point at.

With `Template.lean` (S4), this and `Score.lean` (S3) are the only
`Submission/` files that reach into `Implementation/`; `Decide.lean` stays
implementation-free.
-/

namespace Shor

open Reference

noncomputable section

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]
variable [IdealCtrlModMulExactSemantics qs]

/-- The one precision level every submission is scored at (`SUBMISSION_PLAN.md`
P3). `m2048` is the reference schedule's explicit level for a 2048-bit
modulus: `referencePrecision m2048 = 2⁻¹⁵⁰` exactly
(`referencePrecision_m2048`), which
`referenceSuccessProbabilityAt_m2048_ge_99_percent` turns into at least 99% of
the ideal `κ / (log₂ N)⁴` baseline.

Change it here and nowhere else: `submission_correct` below and
`Submission/Score.lean` (S3) both read this. -/
def submissionPrecision : ℕ := m2048

/-- **The certificate.** Any table that can be packaged as a `ShorSubmission`
— that is, any `(ops, pts)` pair passing C1-C4 — yields a reference program
that meets the declared single-run success bound at the fixed precision, for
every order-finding instance and every complete continued-fraction search.

This is `referenceProgramAt_success` restated at `submissionPrecision`;
proving it for a new submission costs nothing, which is the whole point of
narrowing the challenge to the table (`SUBMISSION_PLAN.md` §0). -/
theorem submission_correct (s : ShorSubmission) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt s submissionPrecision inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt s submissionPrecision inst).output)
          (C := (referenceProgramAt s submissionPrecision inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
  referenceProgramAt_success (qs := qs) s submissionPrecision

end

end Shor
