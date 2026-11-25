import ForShor.ShorVerification.Submission.PolicyTemplate
import ForShor.ShorVerification.Submission.PolicyDecide
import ForShor.ShorVerification.Submission.Audit
import ForShor.ShorVerification.Framework.PrimitiveSynthesis
import ForShor.ShorVerification.Framework.FullRunDesign
import ForShor.ShorVerification.Submission.Correct
import ForShor.ShorVerification.Submission.Score
import ForShor.Emit.Reflect.Driver
import ForShor.Emit.Reflect.PolicyVerify
import ForShor.Emit.IR.Json

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

The policy's `negation` option (how a negation is built and priced, `oneQubit` unless the template says
`scratch`) is not an obligation: it changes the resource estimate and nothing the kernel checks here
(`Shor.ShorLoweringPolicy.withNegation_admissible`; the certificate below is generic in the policy,
negation included).

## Checked by evaluation, at sampled widths

`Shor.Reflect.buildPolicyDoc` (run by the executable) builds the IR a resource estimator reads: one
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

namespace Shor.SubmissionDesign

/-- Read a declaration by its exact environment name, not by namespace resolution.
Only an absent declaration chooses the legacy design. -/
def resolveDeclaration (name : Lean.Name) (sourceModule : Option Lean.Name := none) : Lean.Elab.Term.TermElabM Lean.Expr :=
  _root_.Shor.resolveOptional ``Shor.SubmissionDesign ``Shor.SubmissionDesign.legacy name sourceModule

/-- Selected once at build time from the same template as `PolicySubmission.policy`. -/
def resolved : SubmissionDesign := by_elab
  resolveDeclaration `PolicySubmission.submittedDesign
    (some `ForShor.ShorVerification.Submission.PolicyTemplate)

#assert_axioms _root_.Shor.SubmissionDesign.resolved

end Shor.SubmissionDesign

/-! The opt-in rules are defined before the policy namespace, so the names below cannot be shadowed by a
submission. -/

namespace Shor.OptIn

/-- A full-run design is attestable: a qualified profile, or a design body the consumer can read
(QFT backend axis on the reference topology). Anything else is refused, never priced. -/
def attestable (d : _root_.Shor.FullRunDesign) : Bool := d.label?.isSome || d.body?.isSome

/-- Full-run synthesis and a standalone primitive are not jointly qualified. -/
def exclusive (d : _root_.Shor.FullRunDesign) (p : _root_.Shor.PrimitiveSynthesis) : Bool :=
  d == .reference || p == .rossSelinger

/-- A full-run design is priced on the semiclassical readout only. -/
def semiclassicalOnly (d : _root_.Shor.FullRunDesign) (r : _root_.Shor.SubmissionReadout) : Bool :=
  d == .reference || r == .semiclassical

open Lean Elab Tactic in
elab "full_run_attestable_check" : tactic => _root_.Shor.kernelOrRefuse
  "submittedFullRunDesign is refused: it is not one of the qualified profiles (Shor.FullRunDesign.qualified), and it cannot be declared as a design body either. A body carries only the data, work and scratch QFT choices on the reference multiplier topology: remove the multiplier topology, rotation backends, phase-product steps and the exponent family (a full run has no exponent register), or use a qualified profile."

open Lean Elab Tactic in
elab "full_run_exclusive_check" : tactic => _root_.Shor.kernelOrRefuse
  "submittedFullRunDesign and submittedPrimitive are both set, and that pair is not qualified: remove one of them."

open Lean Elab Tactic in
elab "full_run_semiclassical_check" : tactic => _root_.Shor.kernelOrRefuse
  "submittedFullRunDesign is refused: a full run is priced on the semiclassical readout. Set `readout := .semiclassical` in submittedDesign, or remove submittedFullRunDesign."

end Shor.OptIn

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

def resolvedPrimitive : _root_.Shor.PrimitiveSynthesis := by_elab
  _root_.Shor.resolveOptional ``_root_.Shor.PrimitiveSynthesis ``_root_.Shor.PrimitiveSynthesis.rossSelinger
    `PolicySubmission.submittedPrimitive (some `ForShor.ShorVerification.Submission.PolicyTemplate)

#assert_axioms _root_.PolicySubmission.resolvedPrimitive

/-- The submitted full-run design, or `reference` when the policy declares none. -/
def resolvedFullRun : _root_.Shor.FullRunDesign := by_elab
  _root_.Shor.resolveOptional ``_root_.Shor.FullRunDesign ``_root_.Shor.FullRunDesign.reference
    `PolicySubmission.submittedFullRunDesign (some `ForShor.ShorVerification.Submission.PolicyTemplate)

#assert_axioms _root_.PolicySubmission.resolvedFullRun

/-! ### Opt-in combinations, refused at build time

These are properties of the declarations alone, so the kernel decides them here, as PTP's
`check` is decided, and `lake build PolicySubmission` fails for a policy that breaks one, with a
message that says which rule. Only the checks that depend on command-line flags stay in
`PolicyMain.lean`. The rules are plain `Bool`s so that `PolicyTests` can pin each refusal. -/

theorem fullRun_attestable :
    _root_.Shor.OptIn.attestable _root_.PolicySubmission.resolvedFullRun = true := by
  full_run_attestable_check

theorem fullRun_primitive_exclusive :
    _root_.Shor.OptIn.exclusive _root_.PolicySubmission.resolvedFullRun
      _root_.PolicySubmission.resolvedPrimitive = true := by
  full_run_exclusive_check

theorem fullRun_semiclassical :
    _root_.Shor.OptIn.semiclassicalOnly _root_.PolicySubmission.resolvedFullRun
      _root_.Shor.SubmissionDesign.resolved.readout = true := by
  full_run_semiclassical_check

#assert_axioms _root_.PolicySubmission.fullRun_attestable
#assert_axioms _root_.PolicySubmission.fullRun_primitive_exclusive
#assert_axioms _root_.PolicySubmission.fullRun_semiclassical

/-- The policy is admissible, which is exactly its bands being submissions. -/
example : policy.policy.Admissible := policy.policy_admissible

/-! Nothing in this file names the shipped bands or thresholds: this library's
build is the acceptance check, so every line here must hold for any
admissible policy. The worked examples on the shipped template (`choose` at
particular widths, the advisory shrink check firing at threshold `12`) are in
[`PolicyTests.lean`](PolicyTests.lean), built by `lean_lib PolicyTests`. -/

/-! ## The IR, and its agreement with the circuit (at run time)

Upstream extracted the IR here, at build time, with
`extract_policy_ir_doc doc policy` under `maxHeartbeats 4000000`, and pinned
`doc.wellFormed` by `native_decide`. That elaboration-time reflection refused
`k = 5, 6` tables and most multi-band policies (deterministic `whnf` timeout;
`k = 4` alone did not finish in 30 minutes at `4·10⁸`).

Nothing in this library's *proof* content depended on it: `#assert_axioms` is
scoped to `PolicySubmission.policy`, and `correct`/`scored` below are generic.
So `forshor_policy_submission` builds the same `Doc` with the same extractor
(`Shor.Reflect.buildPolicyDoc`), compiled and with the heartbeat limit off (as
`forshor_emit template` already does), and checks well-formedness and the full
evaluation tier before printing (`PolicyMain.lean`). The IR claim stays
evaluation, never proof, and every check is the same. -/

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

/-- The same bands on the exact width rule (`forshor_policy_submission
--exact-widths`): the policy that run prints. -/
abbrev policyExact : ShorPolicySubmission := { policy with widthRule := .exact }

/-- The certificate on the exact width rule: the same theorem, at the
exact-width copy of the submission. Same hypotheses, same bound. -/
theorem correct_exact {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] :
    type_of% (_root_.Shor.policy_submission_correct (qs := qs) policyExact) :=
  _root_.Shor.policy_submission_correct (qs := qs) policyExact

/-- The scored form on the exact width rule. -/
theorem scored_exact {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs] :
    type_of% (_root_.Shor.policy_submissionSuccessBound_le_success (qs := qs) policyExact) :=
  _root_.Shor.policy_submissionSuccessBound_le_success (qs := qs) policyExact

end PolicySubmission
