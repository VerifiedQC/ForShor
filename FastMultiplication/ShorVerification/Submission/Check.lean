import FastMultiplication.ShorVerification.Submission.Template
import FastMultiplication.ShorVerification.Submission.Audit
import FastMultiplication.ShorVerification.Submission.Correct
import FastMultiplication.ShorVerification.Submission.Score
import FastMultiplication.Emit.Reflect.Driver
import FastMultiplication.Emit.Reflect.Verify
import FastMultiplication.Emit.IR.Json

/-!
# The acceptance check

`lean_lib Submission` is rooted here, so **building this file is the check**.
Nothing in it is edited by a submitter; everything it touches comes from
[`Template.lean`](Template.lean), which is the file a submitter owns.

What the build establishes, and it is worth being precise about which is
which.

## Kernel-checked, and audited

`Submission.setup` carries proofs of C1–C4 for the submitted table, written
in `Template.lean` and reduced by Lean's kernel. `#assert_axioms` then reads
the axioms the finished term actually depends on and fails unless they lie
inside `propext`, `Classical.choice`, `Quot.sound` — so `native_decide`
(`Lean.ofReduceBool`), `sorry` (`sorryAx`) and a submitter's own `axiom` are
all rejected by name. See [`Audit.lean`](Audit.lean) for what this does and
does not cover.

Passing C1–C4 is not evidence that the submission is admissible, it *is*
admissibility: `Shor.submission_correct` is generic in the table, so it
applies to `setup` with no further work and gives the same proved success
bound every other submission gets. There is no per-submission correctness
proof, which is the entire point of narrowing the challenge this way.

## Checked by evaluation

`Shor.Reflect.submissionChecks` compares the extracted IR against the real
compiled circuit at sampled widths (`n = 8, 16` for the phase products,
`w = 4, 8` for the QFT, and the smallest reference Shor instance). This is
evaluation, not a theorem: the IR is not proved correct at *every* width.
That project (R6) concerns the reference table only and was archived; it is
deliberately not a submission requirement. The extractor is keyed by Lean
construct, never by `k` or by a table, which is why agreement at sampled
widths is meaningful evidence rather than a coincidence.

These two lines stay on `native_decide`, and that is deliberate: they are
repo-owned `example`s about the *extractor*, not fields of `setup`, so they
do not appear in the audit above. Making the evaluation tier kernel-checked
is a separate project.
-/

namespace Submission

open Shor Operations Shor.Audit

/-! ## The audit

Every field of `setup` — C1, C2, C3, C4 — reduced by the kernel and by
nothing else. This line is what makes "kernel-checked" a checked claim
rather than a documented intention. -/

#assert_axioms Submission.setup

/-! ## The IR

`doc` is what a resource estimator reads: extracted by reflection from the
reference construction specialised at `setup`, and printed by
[`Main.lean`]. -/

set_option maxHeartbeats 4000000 in
extract_ir_doc doc setup

/-- The IR is well-formed: every template's free variables are bound, every
`Node.call` names a template in the document, and so on. -/
example : IR.Doc.wellFormed doc = true := by native_decide

/-! The evaluation tier: `instantiate doc` agrees with the real compiled
circuit at the sampled widths and at the smallest reference Shor instance,
against *this* submission's points. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
example : Shor.Reflect.submissionChecks setup doc = true := by native_decide

/-! ## The certificate -/

/-- The certificate at this submission, as a name the submissions repo can
cite. There is nothing to prove: `Shor.submission_correct` is generic in the
table, so `setup` existing is the whole argument. -/
def correct {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] [IdealCtrlModMulExactSemantics qs] :=
  Shor.submission_correct (qs := qs) setup

end Submission
