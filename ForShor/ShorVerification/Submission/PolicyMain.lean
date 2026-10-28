import ForShor.ShorVerification.Submission.PolicyCheck
import ForShor.Emit.Json.Common

/-!
# `forshor_policy_submission`: what a policy submission hands over

Prints one `forshor.policy-submission/v1` JSON document on stdout: the bands
in width order, the IR a resource estimator reads, the fixed precision, and
the trial count the score is multiplied by.

Unlike [`Main.lean`](Main.lean), this executable runs one check itself: the
evaluation tier `Shor.Reflect.policySubmissionChecks`, evaluated natively
before anything is printed. Everything else it reports as established was
established by `lake build PolicySubmission`: C1–C4 per band by Lean's
kernel on the proofs in `PolicyTemplate.lean`, the thresholds' strict
decrease by `decide`, the absence of `native_decide`/`sorry` among them by
`#assert_axioms`, and the extracted IR's well-formedness. So the CI line is

```bash
lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
```

with `&&`: if any band is inadmissible the build fails and this never runs,
and if the evaluation tier fails this prints nothing on stdout and exits `1`.

## What the `ir` field holds

One dispatcher per phase-product flavour, one body template per band, and
the shared `qft`/`shor_gate`/`shor`/leaf templates. The dispatcher is the
entry point and carries the policy's own guard chain, so a consumer
instantiates `phase_product` at a width and the document routes it to the
band that covers it.

The width oracles a consumer must supply are **the same ten names, with the
same arities**, as for a single-table document: `Policy.reserveNeed P` is
already a function of the operand widths alone, and `nextWidth` is evaluated
by a band body only where the dispatcher sent it. One index convention does
change, and `IR/README.md` records it: `coeff`'s point index is a position
in the bands' interpolation points *concatenated*, band 0 first, because two
bands with different `k` would otherwise both emit `coeff 0` meaning
different numbers.

The `bands[].shrinks` flag is the advisory check from
[`PolicyDecide.lean`](PolicyDecide.lean), reported per band: `false` marks a
band that is selected but declines to recurse somewhere in its own range.
It is a performance warning and never an admissibility failure, so it is
reported rather than enforced.

Nothing in this file is edited by a submitter; it reads `policy` from
`PolicyTemplate.lean`.
-/

-- `2 ^ 2047` and `2 ^ 2048` are the point of this file, so the elaborator's
-- warning that it declined to evaluate an exponent above 256 is noise here.
set_option exponentiation.threshold 4096

open Lean (Json)
open Shor

namespace PolicySubmission

/-- The representative benchmark modulus, as in `Main.lean`:
`submissionTrialCount` is constant across `[2^2047, 2^2048)`, so one member
of the range stands for all of it. -/
def benchmarkModulus : ℕ := 2 ^ 2047

theorem benchmarkModulus_is2048Bit : Is2048Bit benchmarkModulus :=
  ⟨le_refl _, Nat.pow_lt_pow_right (by norm_num) (by norm_num)⟩

/-- The number of independent runs the score is computed over. Backed by
`Shor.submissionTrialCount_correct`, whose hypothesis
`benchmarkModulus_is2048Bit` discharges. -/
def benchmarkTrialCount : ℕ := _root_.Shor.submissionTrialCount benchmarkModulus

/-- Big naturals go out as strings: `submissionPrecision` is a 46-digit
number and JSON consumers routinely parse numbers as doubles. -/
def natStr (n : ℕ) : Json := Json.str (toString n)

/-- One band: the width it takes over at, its table, and the advisory shrink
flag for the range it covers. `index` is the band's position in the policy,
which is what `Shor.Policy.bandShrinks` is keyed on. -/
def bandJson (i : ℕ) (b : ℕ × ShorLoweringSetup) : Json :=
  Json.mkObj [
    ("index", (i : Json)),
    ("threshold", (b.1 : Json)),
    ("k", (b.2.k : Json)),
    ("points", Json.arr (b.2.pts.map _root_.Shor.pointJson).toArray),
    ("ops", _root_.Shor.progJson b.2.ops),
    ("shrinks", Json.bool (_root_.Shor.Policy.bandShrinks policy.policy i))
  ]

def policySubmissionJson : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.policy-submission/v1"),
    ("bands", Json.arr (policy.bands.zipIdx.map (fun p => bandJson p.2 p.1)).toArray),
    ("leaf", Json.str
      s!"widths below the last threshold use the schoolbook leaf; with these bands that is \
         n < {(policy.bands.map Prod.fst).getLast?.getD 0}"),
    ("precision", Json.mkObj [
      ("m", natStr _root_.Shor.submissionPrecision),
      ("m_expr", Json.str "2^150 - 3 (Reference.m2048)"),
      ("eta", Json.str "2^-150")
    ]),
    ("benchmark", Json.mkObj [
      ("bits", (2048 : Json)),
      ("modulus_expr", Json.str "2^2047 (representative: trial_count is constant on [2^2047, 2^2048))"),
      ("trial_count", natStr benchmarkTrialCount)
    ]),
    ("score", Json.str
      "trial_count × (single-run gate count of the IR below, as measured by Qualtran). \
       The gate count is not computed in Lean."),
    ("checks", Json.mkObj [
      ("side_conditions", Json.str
        "per band: C1 length, C2 det ≠ 0 (proved from pairwise projective distinctness), \
         C3 ordered point consumption + safe adds, C4 returns to start — all four proved \
         for every band in Submission/PolicyTemplate.lean by the submitter and reduced by \
         Lean's kernel at build time"),
      ("sorted", Json.str
        "ShorPolicySubmission.sorted: the thresholds strictly decrease, closed by decide. \
         This is the only obligation a policy adds on top of its bands' own C1-C4, and it \
         is what makes band i cover [t_i, t_{i-1}) literally"),
      ("axioms", Json.str
        "#assert_axioms _root_.PolicySubmission.policy in Submission/PolicyCheck.lean: fails the \
         build on native_decide (its compiled-evaluator axiom), sorry (sorryAx) or any declared axiom, \
         so every band's side conditions really did go through the kernel"),
      ("correctness", Json.str
        "Shor.policy_submission_correct: proved once, generic in the policy; no \
         per-submission proof. Shor.submission_correct is the one-band case at threshold 0"),
      ("ir_agreement", Json.str
        "Shor.Reflect.policySubmissionChecks (probe design): the document is well formed \
         and its two dispatchers are exactly dispatcherTemplate of this policy (routing proved: \
         Emit/Symbolic/Dispatcher.lean). The sampled checks run on the PROBE submission - the \
         same band setups in the same order (so the same band bodies and coeff offsets) at the \
         smallest strictly decreasing thresholds where each band's table shrinks (a band whose \
         table never shrinks is probed at the leaf) - with the \
         dispatchers rebuilt for it: each band body one level deep at its probe threshold \
         (child calls as the compiler's phase-product leaves, width and capacity arguments \
         checked against the registers passed) = the compiler's one-level step; full-depth \
         instantiate = real compiled circuit at the probe ladder widths within the leaf budget, \
         in both reserve regimes; odd qft widths straddling the lowest probe threshold; the \
         leaves; and the reference Shor instances. Evaluated natively by this executable, which \
         prints this document only if the check is true. Cost depends on the tables only, not on \
         the submission's thresholds."),
      ("ir_not_proved", Json.str
        "the IR is NOT proved equal to the circuit at every width; the line above is \
         evaluation at sampled widths, not a theorem. What IS proved is that the emitted \
         guard chain picks the same band as ShorLoweringPolicy.choose at every width \
         (Shor.IR.dispatcherCallAt_dispatcherTemplate)."),
      ("shrink_advisory", Json.str
        "bands[].shrinks is Shor.Policy.bandShrinks: does this band's table shrink the \
         operand width at every width the band covers? false means the recursion falls \
         through to the schoolbook leaf somewhere in the band's own range, so the band is \
         dead weight there. A performance warning, NOT an admissibility condition - the \
         policy is correct either way")
    ]),
    ("provenance", Json.str
      "extracted by reflection from the named constants in Submission/PolicyTemplate.lean; \
       trusted: translation table and Lean normalisation; checked: instantiate = real term \
       at the listed widths; not a theorem. The dispatcher is built from the policy's own \
       bands rather than extracted, and is proved to agree with ShorLoweringPolicy.choose."),
    ("ir", _root_.Shor.IR.docJson doc)
  ]

end PolicySubmission

/-- The evaluation tier runs here, natively, before anything is printed. A
failing submission prints nothing on stdout and exits 1, so
`lake build PolicySubmission && lake exe forshor_policy_submission > policy.json`
produces a document only for a submission that passed every check. -/
def main : IO UInt32 := do
  if _root_.Shor.Reflect.policySubmissionChecks _root_.PolicySubmission.policy _root_.PolicySubmission.doc then
    IO.eprintln "forshor_policy_submission: evaluation tier passed"
    IO.println _root_.PolicySubmission.policySubmissionJson.compress
    return 0
  else
    IO.eprintln "forshor_policy_submission: evaluation tier FAILED \
      (Shor.Reflect.policySubmissionChecks policy doc = false); no policy.json printed"
    return 1
