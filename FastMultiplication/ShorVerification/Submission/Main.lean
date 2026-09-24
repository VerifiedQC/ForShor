import FastMultiplication.ShorVerification.Submission.Template
import FastMultiplication.Emit.Json.Common

/-!
# `forshor_submission`: what a submission hands over

`SUBMISSION_PLAN.md` S4.1. Prints one `forshor.submission/v1` JSON document
on stdout: the submitted table, the IR extracted from it (what a resource
estimator reads), the fixed precision, and the trial count the score is
multiplied by.

This executable is a *printer*, not a checker. Everything it reports as
established was established by `lake build Submission` — the four side
conditions by Lean's kernel, the IR agreement by `native_decide` in
`Template.lean`. That is why the submissions repo's CI is

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

with `&&`: if the table is inadmissible the build fails and this never runs.
Re-deciding the same conditions here would cost the same again and prove
nothing new.

Nothing in this file is edited by a submitter; it reads `Submission.doc` and
`Submission.setup` from the template.
-/

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
      ("k", (k : Json)),
      ("points", Json.arr (pts.map pointJson).toArray),
      ("ops", progJson ops)
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
        "C1 length, C2 det ≠ 0, C3 ordered point consumption + safe adds, C4 returns to start: \
         all four decided by Submission/Decide.lean and checked by the kernel at build time"),
      ("correctness", Json.str
        "Shor.submission_correct: proved once, generic in the table; no per-submission proof"),
      ("ir_agreement", Json.str
        "Shor.Reflect.submissionChecks: instantiate = real compiled circuit at n = 8, 16 \
         (phase_product, cphase_product), w = 4, 8 (qft), and the smallest reference Shor \
         instance — pinned by native_decide in Submission/Template.lean"),
      ("ir_not_proved", Json.str
        "the IR is NOT proved equal to the circuit at every width (decision P5); the line above \
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
