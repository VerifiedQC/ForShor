import FastMultiplication.ShorVerification.Submission.PolicyCheck
import FastMultiplication.Emit.Json.Common
import FastMultiplication.Emit.Symbolic.ExactWidthJson
import FastMultiplication.Emit.Balanced.Verify

/-!
# `forshor_policy_submission`: what a policy submission hands over

Prints one `forshor.policy-submission/v1` JSON document on stdout: the bands
in width order, the IR a resource estimator reads, the fixed precision, and
the trial count the score is multiplied by.

Unlike [`Main.lean`](Main.lean), this executable extracts the IR and runs
the evaluation tier itself, natively, before anything is printed.
Everything else it reports as established was established by
`lake build PolicySubmission`: C1–C4 per band by Lean's kernel on the proofs
in `PolicyTemplate.lean`, the thresholds' strict decrease by `decide`, and the
absence of `native_decide`/`sorry` among them by `#assert_axioms`. So the CI
line is

```bash
lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
```

with `&&`: if any band is inadmissible the build fails and this never runs,
and if the IR is not well formed or the evaluation tier fails this prints
nothing on stdout and exits `1`.

The IR is extracted at run time (compiled, heartbeat limit off) with the same
extractor `PolicyCheck.lean` used to run at build time, which refused `k ≥ 5`
tables and most multi-band policies.

## Flags

* none: the policy as submitted, on its width rule (the scan unless the
  template sets `widthRule`), checked by `Shor.Reflect.policySubmissionChecks`.
  The output's `ir` is the document upstream ForShor printed.
* `--exact-widths`: the same bands on the exact width rule
  (`WidthRule.exact`): the compiler grows each level's registers to the least
  width holding every value the table reaches, and the `ir` gains
  `width_rule` (the rule a consumer evaluates `nextWidth` with). The templates
  are the same; the evaluation tier compiles the real circuit at exact widths.
* `--probe-exact`: probe thresholds where the policy's own width rule shrinks
  each table (`policySubmissionChecksOwnRuleProbe`) rather than where the scan
  does. Deeper and much slower; the same checks on the same IR.
* `--probe-scan`: accepted, does nothing (it is the default).
* `--balanced`: implies `--exact-widths`; also runs the balanced tier, and
  prints the balanced document as `ir` and the policy's own as `ir_unbalanced`.
* `--width-table`: print the compiler's widths per band on the chosen rule
  (not a submission document; no extraction, no checks).

`extraction` in the output records the rule and the probe tier that ran.

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

/-- Width range of the `ir.width_rule` tables (covers every phase-product and
QFT width of the 2048-bit reference run; other widths: the rows and formula). -/
def widthTableMax : ℕ := 2560

/-- One band: the width it takes over at, its table, and the advisory shrink
flag for the range it covers. `index` is the band's position in the policy,
which is what `Shor.Policy.bandShrinks` is keyed on. -/
def bandJson (s : ShorPolicySubmission) (i : ℕ) (b : ℕ × ShorLoweringSetup) : Json :=
  Json.mkObj [
    ("index", (i : Json)),
    ("threshold", (b.1 : Json)),
    ("k", (b.2.k : Json)),
    ("points", Json.arr (b.2.pts.map _root_.Shor.pointJson).toArray),
    ("ops", _root_.Shor.progJson b.2.ops),
    ("shrinks", Json.bool (_root_.Shor.Policy.bandShrinks s.policy i))
  ]

def policySubmissionJson (s : ShorPolicySubmission) (doc : _root_.Shor.IR.Doc) : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.policy-submission/v1"),
    ("bands", Json.arr (s.bands.zipIdx.map (fun p => bandJson s p.2 p.1)).toArray),
    ("leaf", Json.str
      s!"widths below the last threshold use the schoolbook leaf; with these bands that is \
         n < {(s.bands.map Prod.fst).getLast?.getD 0}"),
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
    ("ir", match s.widthRule with
      | .scan => _root_.Shor.IR.docJson doc
      | .exact => (_root_.Shor.IR.docJson doc).mergeObj
          (Json.mkObj [("width_rule", _root_.Shor.policyWidthRuleJson s widthTableMax)]))
  ]

end PolicySubmission

open Lean Meta in
/-- Constants `isDefEq`/`whnf` must not unfold during run-time extraction.

The extractor translates each of these *by name* into an opaque IR call
(`nextWidth`, `reserveNeed_x/z`, …) before any reduction
(`Emit/Reflect/Extract.lean`, `translateW`). But `Registry.lookupWidth` /
`lookupReg` compare candidate terms by `isDefEq`, and a failing comparison
unfolds them: on a concrete `k = 4..6` table that is a symbolic evaluation of
the width scan over every operation, through `match` reduction (the heartbeat
wall; profiled: `whnfEasyCases`/`reduceMatcher` under `lookupWidth`). Keeping
them folded makes `isDefEq` decide by their arguments, which is what the
by-name translation assumes anyway. -/
def extractOpaqueNames : List Name :=
  [``Shor.scanNeededWidths, ``Shor.scanNeededWidthsAux, ``Shor.nextSignedWidth,
   ``Shor.commonNeededWidth, ``Shor.updateWidthState, ``Shor.mergeNeededWidths,
   ``Shor.RecursivePhaseWorkspace.nextWidth, ``Shor.RecursivePhaseWorkspace.reserveNeed,
   ``Shor.Policy.reserveNeed, ``Shor.neededWidthsBy, ``Shor.nextSignedWidthBy,
   ``Shor.RecursivePhaseWorkspace.nextWidthBy, ``Shor.RecursivePhaseWorkspace.immediateNeedBy]

open Lean Meta in
def extractCanUnfold (cfg : Meta.Config) (info : ConstantInfo) : CoreM Bool := do
  if extractOpaqueNames.contains info.name then return false
  canUnfoldDefault cfg info

open Lean Meta in
/-- The IR, extracted at run time: the same extractor (`Shor.Reflect.buildPolicyDoc`)
`PolicyCheck.lean` used to run at build time, compiled, with the heartbeat
limit off and bounded registry lookups, against the environment of the oleans
`lake build PolicySubmission` produced. It reads the template's policy as
submitted; the templates do not depend on the width rule (only the width
oracles' values do). -/
unsafe def extractPolicyDoc : IO (Except String _root_.Shor.IR.Doc) := do
  try
    enableInitializersExecution
    _root_.Shor.Reflect.enableBoundedLookups
    initSearchPath (← findSysroot)
    let env ← importModules #[{module := `FastMultiplication.ShorVerification.Submission.PolicyCheck}] {}
      (trustLevel := 0) (loadExts := true)
    let coreCtx : Core.Context :=
      { fileName := "<extract_policy_ir>", fileMap := FileMap.ofString "", maxHeartbeats := 0 }
    let polE := mkApp (mkConst ``_root_.Shor.ShorPolicySubmission.policy)
      (mkConst ``_root_.PolicySubmission.policy)
    let metaCtx : Meta.Context := { customCanUnfoldPredicate? := some extractCanUnfold }
    let (doc, _) ← ((_root_.Shor.Reflect.buildPolicyDoc _root_.PolicySubmission.policy polE).run' metaCtx).toIO
      coreCtx { env := env }
    return .ok doc
  catch e =>
    return .error (toString e)

/-- The balanced splice (`Emit/Balanced/`): `ir` := the balanced document
(`shor` retargeted to `balanced_(c)phase_product`), `ir_unbalanced` := the
policy's own document, both carrying `width_rule`; `balanced` := rule,
theorems, the balanced evaluation tier's record. -/
def balancedFields (s : ShorPolicySubmission) (doc : _root_.Shor.IR.Doc)
    (sites : List (Bool × ℕ × ℕ × Bool)) : List (String × Json) :=
  let wr := Json.mkObj [("width_rule", _root_.Shor.policyWidthRuleJson s _root_.PolicySubmission.widthTableMax)]
  let siteJson (r : Bool × ℕ × ℕ × Bool) : Json :=
    Json.mkObj [("agrees", Json.bool r.1), ("xw", (r.2.1 : Json)), ("zw", (r.2.2.1 : Json)),
      ("split_taken", Json.bool r.2.2.2)]
  [("ir", (_root_.Shor.IR.docJson (_root_.Shor.IR.Balanced.balanceDoc doc)).mergeObj wr),
   ("ir_unbalanced", (_root_.Shor.IR.docJson doc).mergeObj wr),
   ("balanced", Json.mkObj [
      ("rule", Json.str "Shor.Balanced.defaultRule: s = min width, L = max width; if s < 2 or L = s: unchanged; if 2L <= 3s: pad the small operand to L (one product at L x L); else B = ceil(L/s) blocks, B-1 low blocks of width s-1 zero-extended to t, top block L-(B-1)(s-1), all products at t = max s top, block i at angle phi*2^(i(s-1)); applied only if fitsB (existing reserves suffice), else the original site"),
      ("correctness", Json.str "Shor.Balanced.Policy.lowerGate_balance_correctness, Shor.Balanced.balancedShorImplementation (kernel-checked, generic in the policy)"),
      ("ir_agreement", Json.str "Shor.Reflect.Balanced.balancedChecks (evaluation, not a theorem)"),
      ("widths", Json.str "the equal-width core runs at the post-balance operand widths, so nextWidth (exact) is evaluated there"),
      ("sites_2048", Json.arr (sites.map siteJson).toArray)])]

/-- `--width-table`: no extraction, no checks; the compiler's own widths on the
submission's width rule, for a consumer's cross-check (NOT a submission
document): per band `nextWidthBy` and the policy's `reserveNeed` on the
diagonal `1..4400`, at `qft`'s split pairs `(v/2+1, v-v/2+1)` for `v ≤ 4400`,
and at the rectangular sites of the 2048-bit reference run. -/
def widthTableJson (s : ShorPolicySubmission) : Json :=
  let rect : List (ℕ × ℕ) := [(2049, 2348), (2348, 2050), (2348, 4399), (2050, 2348), (2348, 2049), (4399, 2348)]
  let qftPairs := (List.range 4400).map fun i => let v := i + 1; (v / 2 + 1, v - v / 2 + 1)
  let diag := (List.range 4400).map fun i => (i + 1, i + 1)
  let row (p : ℕ × ℕ) : Json :=
    let need := Policy.reserveNeed s.policy p.1 p.2
    Json.arr (#[(p.1 : Json), (p.2 : Json)] ++
      (s.bands.map fun b => (RecursivePhaseWorkspace.nextWidthBy s.widthRule b.2.ops p.1 p.2 : Json)).toArray ++
      #[(need.1 : Json), (need.2 : Json)])
  Json.mkObj [("schema", Json.str "forshor.width-table/v1 (not a submission)"),
    ("width_rule", Json.str (match s.widthRule with | .scan => "scan" | .exact => "exact")),
    ("columns", Json.str "xw, zw, nextWidth per band (band order), reserveNeed_x, reserveNeed_z"),
    ("bands", Json.arr (s.bands.map fun b => Json.mkObj [("threshold", (b.1 : Json)), ("k", (b.2.k : Json)),
      ("ops", _root_.Shor.progJson b.2.ops)]).toArray),
    ("rows", Json.arr ((diag ++ qftPairs ++ rect).map row).toArray)]

/-- Extract the IR, check it (well-formedness, then the evaluation tier; with
`--balanced` also the balanced tier), and print only a document that passed.
A failing submission prints nothing on stdout and exits 1, so
`lake build PolicySubmission && lake exe forshor_policy_submission > policy.json`
produces a document only for a submission that passed every check. -/
unsafe def main (args : List String) : IO UInt32 := do
  let balanced := args.contains "--balanced"
  let exact := balanced || args.contains "--exact-widths"
  -- `--probe-scan` is accepted and does nothing: scan-threshold probes are the default
  let probeOwnRule := args.contains "--probe-exact"
  -- both are top-level constants, so compiled code shares one object per
  -- policy and the evaluation-only memos (keyed on its address) hit
  let s : ShorPolicySubmission :=
    if exact then _root_.PolicySubmission.policyExact else _root_.PolicySubmission.policy
  if args.contains "--width-table" then
    IO.println (widthTableJson s).compress
    return 0
  let t0 ← IO.monoMsNow
  match ← extractPolicyDoc with
  | .error e =>
      IO.eprintln s!"forshor_policy_submission: IR extraction FAILED: {e}; no policy.json printed"
      return 1
  | .ok doc =>
    let t1 ← IO.monoMsNow
    let nto ← _root_.Shor.Reflect.lookupTimeouts.get
    IO.eprintln s!"forshor_policy_submission: IR extracted at run time in {t1 - t0} ms; bounded registry lookups that timed out: {nto}"
    if !(_root_.Shor.IR.Doc.wellFormed doc) then
      IO.eprintln "forshor_policy_submission: extracted IR is NOT well formed; no policy.json printed"
      return 1
    let tierOK := if probeOwnRule then _root_.Shor.Reflect.policySubmissionChecksOwnRuleProbe s doc
      else _root_.Shor.Reflect.policySubmissionChecks s doc
    if !tierOK then
      let tier := if probeOwnRule then "policySubmissionChecksOwnRuleProbe" else "policySubmissionChecks"
      IO.eprintln s!"forshor_policy_submission: evaluation tier FAILED \
        (Shor.Reflect.{tier} policy doc = false); no policy.json printed"
      return 1
    let t2 ← IO.monoMsNow
    IO.eprintln s!"forshor_policy_submission: evaluation tier passed in {t2 - t1} ms"
    let base := (_root_.PolicySubmission.policySubmissionJson s doc).mergeObj (Json.mkObj
        [("extraction", Json.mkObj [("where", Json.str "run time, compiled"),
          ("width_rule", Json.str (if exact then "exact (--exact-widths)" else "scan")),
          ("lookup_timeouts", (nto : Json)),
          ("probe_thresholds", Json.str (if probeOwnRule then "where the policy's own width rule shrinks each table (--probe-exact)"
             else "where the scan shrinks each table (the default)")),
          ("note", Json.str "a timed-out registry isDefEq counts as no match and falls back to structural translation; the evaluation tier above checked the result")])])
    if balanced then
      let (ok, sites) := _root_.Shor.Reflect.Balanced.balancedChecks s doc
      let t3 ← IO.monoMsNow
      if !ok then
        IO.eprintln s!"forshor_policy_submission: balanced tier FAILED; no policy.json printed"
        return 1
      IO.eprintln s!"forshor_policy_submission: balanced tier passed in {t3 - t2} ms"
      IO.println (base.mergeObj (Json.mkObj (balancedFields s doc sites))).compress
    else
      IO.println base.compress
    return 0
