import FastMultiplication.ShorVerification.Submission.PolicyCheck
import FastMultiplication.Emit.Json.Common

/-!
# `forshor_policy_submission`: what a policy submission hands over

Prints one `forshor.policy-submission/v1` JSON document on stdout: the bands
in width order, the IR a resource estimator reads, the fixed precision, and
the trial count the score is multiplied by.

As with [`Main.lean`](Main.lean), this executable is a *printer*, not a
checker. Everything it reports as established was established by `lake build
PolicySubmission`: C1–C4 per band by Lean's kernel on the proofs in
`PolicyTemplate.lean`, the thresholds' strict decrease by `decide`, and the
absence of `native_decide`/`sorry` among them by `#assert_axioms`. So the CI
line is

```bash
lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
```

with `&&`: if any band is inadmissible the build fails and this never runs.

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
def benchmarkTrialCount : ℕ := submissionTrialCount benchmarkModulus

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
    ("points", Json.arr (b.2.pts.map pointJson).toArray),
    ("ops", progJson b.2.ops),
    ("shrinks", Json.bool (Shor.Policy.bandShrinks policy.policy i))
  ]

def policySubmissionJson : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.policy-submission/v1"),
    ("bands", Json.arr (policy.bands.zipIdx.map (fun p => bandJson p.2 p.1)).toArray),
    ("leaf", Json.str
      s!"widths below the last threshold use the schoolbook leaf; with these bands that is \
         n < {(policy.bands.map Prod.fst).getLast?.getD 0}"),
    ("precision", Json.mkObj [
      ("m", natStr submissionPrecision),
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
        "#assert_axioms PolicySubmission.policy in Submission/PolicyCheck.lean: fails the \
         build on native_decide (Lean.ofReduceBool), sorry (sorryAx) or any declared axiom, \
         so every band's side conditions really did go through the kernel"),
      ("correctness", Json.str
        "Shor.policy_submission_correct: proved once, generic in the policy; no \
         per-submission proof. Shor.submission_correct is the one-band case at threshold 0"),
      ("ir_agreement", Json.str
        "Shor.Reflect.policySubmissionChecks: instantiate = real compiled circuit at the \
         policy's band boundaries and at the widths reaching one, two and three levels of \
         its own recursion, in both reserve regimes; at odd qft widths where the split \
         straddles the lowest threshold; and at the reference Shor instances - pinned by \
         native_decide in Submission/PolicyCheck.lean. Instantiating the entry template \
         exercises the dispatcher's guard chain, the band body it routes to, and the \
         recursion back through the dispatcher, all at once."),
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
    ("ir", IR.docJson doc)
  ]

end PolicySubmission

def main : IO Unit :=
  IO.println PolicySubmission.policySubmissionJson.compress
