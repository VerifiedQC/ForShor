import FastMultiplication.ShorVerification.Submission.Check
import FastMultiplication.Emit.Json.Common

/-!
# `forshor_submission`: what a submission hands over

Prints one `forshor.submission/v1` JSON document on stdout: the submitted table, the IR extracted from it (what a resource
estimator reads), the fixed precision, and the trial count the score is
multiplied by.

This executable is a *printer*, not a checker. Everything it reports as
established was established by `lake build Submission` — the four side
conditions by Lean's kernel on the proofs in `Template.lean`, the absence of
`native_decide`/`sorry` among them by `#assert_axioms`, and the IR agreement
by `native_decide` in `Check.lean`. That is why the submissions repo's CI is

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

with `&&`: if the table is inadmissible the build fails and this never runs.
Re-deciding the same conditions here would cost the same again and prove
nothing new.

Nothing in this file is edited by a submitter; it reads `Submission.setup`
from the template and `Submission.doc` from `Check.lean`.
-/

-- `2 ^ 2047` and `2 ^ 2048` are the point of this file, so the elaborator's
-- warning that it declined to evaluate an exponent above 256 is noise here.
set_option exponentiation.threshold 4096

open Lean (Json)
open Shor

namespace Submission

/-- The representative benchmark modulus. `submissionTrialCount` is constant
across `[2^2047, 2^2048)` — the bound it is derived from depends on `N` only
through `log₂ N = 2047` — so one member of the range stands for all of it. -/
def benchmarkModulus : ℕ := 2 ^ 2047

theorem benchmarkModulus_is2048Bit : Reference.Is2048Bit benchmarkModulus :=
  ⟨le_refl _, Nat.pow_lt_pow_right (by norm_num) (by norm_num)⟩

/-- The number of independent runs the score is computed over, for the
benchmark. Backed by `Shor.submissionTrialCount_correct`, which
`benchmarkModulus_is2048Bit` discharges the hypothesis of. -/
def benchmarkTrialCount : ℕ := submissionTrialCount benchmarkModulus

/-- Big naturals go out as strings: `submissionPrecision` is a 46-digit
number and JSON consumers routinely parse numbers as doubles. -/
def natStr (n : ℕ) : Json := Json.str (toString n)

def submissionJson : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.submission/v1"),
    ("table", Json.mkObj [
      ("k", (setup.k : Json)),
      ("points", Json.arr (setup.pts.map pointJson).toArray),
      ("ops", progJson setup.ops)
    ]),
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
        "C1 length, C2 det ≠ 0 (proved from pairwise projective distinctness), C3 ordered \
         point consumption + safe adds, C4 returns to start: all four proved in \
         Submission/Template.lean by the submitter, reduced by Lean's kernel at build time, \
         and audited by #assert_axioms Submission.setup in Submission/Check.lean — which \
         fails the build on native_decide (Lean.ofReduceBool), sorry (sorryAx) or any \
         declared axiom"),
      ("correctness", Json.str
        "Shor.submission_correct: proved once, generic in the table; no per-submission proof"),
      ("ir_agreement", Json.str
        s!"Shor.Reflect.submissionChecks: instantiate = real compiled circuit at \
           phase_product/cphase_product widths {Reflect.submissionPPWidths setup} in reserve \
           regimes {Reflect.submissionPPSlacks}, leaf (xw, zw) pairs \
           {Reflect.submissionLeafWidths}, qft widths {Reflect.submissionQFTWidths setup}, and \
           {Reflect.submissionShorInstances.length} reference Shor instances — pinned by \
           native_decide in Submission/Check.lean. The width ladders are derived from this \
           table's own recursion depth, so they are not the same for every submission."),
      ("ir_not_proved", Json.str
        "the IR is NOT proved equal to the circuit at every width; the line above \
         is evaluation at sampled widths, not a theorem")
    ]),
    ("provenance", Json.str
      "extracted by reflection from the named constants; trusted: translation table and Lean \
       normalisation; checked: instantiate = real term at the listed widths; not a theorem."),
    ("ir", IR.docJson doc)
  ]

end Submission

def main : IO Unit :=
  IO.println Submission.submissionJson.compress
