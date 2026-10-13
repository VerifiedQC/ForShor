import FastMultiplication.ShorVerification.Submission.PolicyTemplate
import FastMultiplication.ShorVerification.Submission.PolicyDecide
import FastMultiplication.ShorVerification.Submission.Audit
import FastMultiplication.ShorVerification.Submission.Correct
import FastMultiplication.ShorVerification.Submission.Score
import FastMultiplication.Emit.Reflect.Driver
import FastMultiplication.Emit.Reflect.PolicyVerify
import FastMultiplication.Emit.IR.Json

/-!
# The acceptance check for a policy submission

`lean_lib PolicySubmission` is rooted here, so **building this file is the
check**. Nothing in it is edited by a submitter; everything it touches comes
from [`PolicyTemplate.lean`](PolicyTemplate.lean), which is the file a policy
submitter owns.

What the build establishes, and — as with the single-table check — it is
worth being precise about which is which.

## Kernel-checked, and audited

`PolicySubmission.policy` carries, per band, proofs of C1–C4 for that band's
table, written in `PolicyTemplate.lean` and reduced by Lean's kernel; and one
proof that the thresholds strictly decrease. `#assert_axioms` then reads the
axioms the finished term actually depends on and fails unless they lie inside
`propext`, `Classical.choice`, `Quot.sound` — so `native_decide`
(`Lean.ofReduceBool`), `sorry` (`sorryAx`) and a submitter's own `axiom` are
all rejected by name. See [`Audit.lean`](Audit.lean).

Passing those obligations is not evidence that the policy is admissible, it
*is* admissibility: `Shor.policy_submission_correct` is generic in the
policy, so it applies to `policy` with no further work and gives the same
proved success bound every other submission gets. A table submission is the
one-band policy at threshold `0`
(`Shor.ShorPolicySubmission.ofSetup`), and `Shor.submission_correct` is
literally a corollary of the policy theorem.

## Checked by evaluation, at sampled widths

`extract_policy_ir_doc` builds the IR a resource estimator reads: one
dispatcher per phase-product flavour, one body template per band, and the
shared `qft`/`shor_gate`/`shor`/leaf templates.
`Shor.Reflect.policySubmissionChecks` then instantiates it and compares it
against the real compiled circuit — at each band boundary, at the widths
reaching one, two and three levels of the policy's own recursion, at odd
`qft` widths where the split straddles the lowest threshold, and at the
reference Shor instances.

Instantiating the entry template exercises the whole stack at once: the
dispatcher's guard chain, the band body it routes to, and the recursion back
through the dispatcher. A width at the top of the policy therefore covers
every band the chain descends through.

**This tier is evaluation, not proof**, exactly as for a single table: the
IR is not proved equal to the circuit at every width. One part of it *is*
proved, and is worth naming — `IR.dispatcherCallAt_dispatcherTemplate` shows
the emitted guard chain picks the same band as `ShorLoweringPolicy.choose`
at every width, so which body a width routes to is not something the
sampling has to establish.
-/

namespace PolicySubmission

open Shor Operations Shor.Audit

/-! ## The audit

Every per-band side condition and the sortedness proof, reduced by the kernel
and by nothing else. This line is what makes "kernel-checked" a checked claim
rather than a documented intention. -/

#assert_axioms PolicySubmission.policy

/-! The bands a submitter writes are the bands the policy carries, so the
policy printed by `PolicyMain.lean` and the policy C1–C4 were proved about
are the same policy. `rfl`, because `policy` is built from them. -/

example : policy.bands = [(40, band0), (14, band1)] := rfl
example : band0.k = band0K := rfl
example : band0.ops = band0Ops := rfl
example : band1.k = band1K := rfl
example : band1.ops = band1Ops := rfl

/-! ## What the policy chooses

One width per band, and one below the last threshold where the schoolbook
leaf takes over. These reduce by `rfl`: `choose` is a `List.find?` over a
literal band list. -/

example : policy.policy.choose 100 = some band0.table := rfl
example : policy.policy.choose 40 = some band0.table := rfl
example : policy.policy.choose 39 = some band1.table := rfl
example : policy.policy.choose 14 = some band1.table := rfl
example : policy.policy.choose 13 = none := rfl

/-- The policy is admissible, which is exactly its bands being submissions. -/
example : policy.policy.Admissible := policy.policy_admissible

/-! ## The advisory shrink check

Not an admissibility condition (see [`PolicyDecide.lean`](PolicyDecide.lean)):
a band whose table does not shrink the width on its own range is dead weight,
not unsound. Both shipped bands pass. -/

example : Shor.Policy.bandShrinks policy.policy 0 = true := by decide +kernel
example : Shor.Policy.bandShrinks policy.policy 1 = true := by decide +kernel

/-- And the check has teeth: dropping band 1's threshold to `12` is still a
perfectly admissible policy, but `bandShrinks` reports it as dead weight,
because this `k = 2` table maps `12 ↦ 12` and `13 ↦ 13` and so declines to
recurse at the bottom two widths of its own band. This is the warning a
submitter is meant to act on by raising the threshold. -/
example :
    Shor.Policy.bandShrinks
      { bands := [(40, band0), (12, band1)], sorted := by decide : ShorPolicySubmission }.policy 1
      = false := by decide +kernel

/-! ## The IR, and its agreement with the circuit

`extract_policy_ir_doc` runs the extractor at build time and splices the
result in as a plain `def`, so the checks below read a pinned value instead
of re-running reflection inside a proof.

These lines stay on `native_decide` for the same reason `Check.lean`'s do:
they are *evaluation*, a deliberately different tier from the kernel-checked
side conditions above, and `#assert_axioms` is scoped to
`PolicySubmission.policy` — the proof object — which does not depend on any
of this. -/

set_option maxHeartbeats 4000000 in
extract_policy_ir_doc doc policy

example : IR.Doc.wellFormed doc = true := by native_decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example : Shor.Reflect.policySubmissionChecks policy doc = true := by native_decide

/-! ## The certificate -/

/-- The certificate at this policy submission, as a name the submissions repo
can cite. There is nothing to prove: `Shor.policy_submission_correct` is
generic in the policy, so `policy` existing is the whole argument. -/
def correct {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] [IdealCtrlModMulExactSemantics qs] :=
  Shor.policy_submission_correct (qs := qs) policy

/-- The scored form, with the declared bound named. -/
def scored {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] [IdealCtrlModMulExactSemantics qs] :=
  Shor.policy_submissionSuccessBound_le_success (qs := qs) policy

end PolicySubmission
