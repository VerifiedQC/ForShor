import FastMultiplication
import FastMultiplication.ShorVerification.Submission.Audit

/-!
# The repository's own axiom guard

`#assert_axioms` (`Submission/Audit.lean`) is the command the acceptance build
points at a submission's `setup`. This file points the same command at the
repository's own headline theorems, so the README's claim that they rest only
on `propext`, `Classical.choice` and `Quot.sound` is checked by CI rather than
by hand.

Run it with `lake env lean scripts/AxiomCheck.lean`; it fails the build if any
listed theorem depends on anything else.
-/

open Shor.Audit

-- Correctness.
#assert_axioms Shor.Shor_correct
#assert_axioms Shor.Shor_end_to_end_factoring
#assert_axioms Shor.Shor_correct_approx_lowered_uniform
#assert_axioms Shor.Shor_correct_approx_lowered

-- Resource estimation.
#assert_axioms Shor.exists_shorGateCountBound
#assert_axioms Shor.shorGateCountBound_of_setup
#assert_axioms Shor.shorGateCountBoundShorEta_of_setup

-- The submission surface.
#assert_axioms Shor.submission_correct
#assert_axioms Shor.ShorLoweringSetup.programOK
#assert_axioms Shor.ShorPolicySubmission.policy_admissible

-- The modular-exponentiation bound the precision schedule is stated against.
#assert_axioms Shor.modExpApprox_correct
#assert_axioms Shor.modExpApprox_correct_2048
