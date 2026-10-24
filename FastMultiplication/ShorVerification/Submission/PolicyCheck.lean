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
(its compiled-evaluator axiom), `sorry` (`sorryAx`) and a submitter's own `axiom` are
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
`Shor.Reflect.policySubmissionChecks` then compares it against the real
compiled circuit. The document's two dispatchers must be exactly
`dispatcherTemplate` of this policy, whose routing is proved. The sampled
checks run on the *probe submission*: the same band setups in the same
order, so the same band bodies and `coeff` offsets, at the smallest strictly
decreasing thresholds where each band's table shrinks (a band whose table
never shrinks is probed at the leaf, as the compiler treats it), with the
dispatchers rebuilt for it. There, the first band of each distinct table has its body
instantiated **one level deep** at its probe threshold, with child calls
treated as the phase-product leaves the compiler emits there (and each call's
width and capacity arguments checked against the registers it passes), and
compared with the compiler's one-level step on the real layout; every later
band with the same table must be that body with its `coeff` indices shifted.
Then the document is instantiated at **full depth** at the widths reaching
one, two and three levels of the probe's own recursion, provided they fit
a leaf budget (`policyFullDepthLeafBudget`). Then `qft` at odd widths where
the split straddles the lowest probe threshold, the leaves, and the
reference Shor instances. The cost depends on the distinct tables only, not
on the submission's thresholds.

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
rather than a documented intention.

Every repo-owned name below is written with `_root_.`, for the reason given
in `Check.lean`: inside `namespace PolicySubmission` a partly qualified name
resolves one namespace deeper first, where a submitter could place a decoy.
-/

#assert_axioms _root_.PolicySubmission.policy

/-- The policy is admissible, which is exactly its bands being submissions. -/
example : policy.policy.Admissible := policy.policy_admissible

/-! Nothing in this file names the shipped bands or thresholds: this library's
build is the acceptance check, so every line here must hold for any
admissible policy. The worked examples on the shipped template (`choose` at
particular widths, the advisory shrink check firing at threshold `12`) are in
[`PolicyTests.lean`](PolicyTests.lean), built by `lean_lib PolicyTests`. -/

/-! ## The IR, and its agreement with the circuit

`extract_policy_ir_doc` runs the extractor at build time and splices the
result in as a plain `def`. Well-formedness is pinned here by `native_decide`;
`Shor.Reflect.policySubmissionChecks policy doc` is evaluated by the compiled
`forshor_policy_submission` executable (`PolicyMain.lean`), which prints
`policy.json` only when it is `true` and exits `1` otherwise. Both are
*evaluation*, a deliberately different tier from the kernel-checked side
conditions above, and `#assert_axioms` is scoped to `PolicySubmission.policy`
— the proof object — which does not depend on any of this. -/

set_option maxHeartbeats 4000000 in
extract_policy_ir_doc doc policy

example : _root_.Shor.IR.Doc.wellFormed doc = true := by native_decide

/-! ## The certificate -/

/-- The certificate at this policy submission, as a name the submissions repo
can cite. There is nothing to prove: `Shor.policy_submission_correct` is
generic in the policy, so `policy` existing is the whole argument. -/
theorem correct {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] :
    type_of% (_root_.Shor.policy_submission_correct (qs := qs) policy) :=
  _root_.Shor.policy_submission_correct (qs := qs) policy

/-- The scored form, with the declared bound named. -/
theorem scored {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] :
    type_of% (_root_.Shor.policy_submissionSuccessBound_le_success (qs := qs) policy) :=
  _root_.Shor.policy_submissionSuccessBound_le_success (qs := qs) policy

end PolicySubmission
