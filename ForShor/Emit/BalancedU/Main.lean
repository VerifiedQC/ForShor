import ForShor.ShorVerification.Submission.PolicyCheck
import ForShor.Emit.Json.Common
import ForShor.Emit.Symbolic.ExactWidthJson
import ForShor.Emit.BalancedU.Verify

/-!
# `forshor_balanced_u`: the unconditionally balanced IR of a policy submission

The `--balanced` path of `forshor_policy_submission`, for `Shor.Balanced.balanceU`: extracts
the policy's IR at run time, checks it is well formed and passes the evaluation tier
(`Shor.Reflect.policySubmissionChecks`), then runs the unconditional tier
(`Shor.Reflect.BalancedU.balancedUChecks`), and prints one JSON document only if every check
passed. As `--balanced`, the policy runs on the exact width rule.

```bash
lake build PolicySubmission && lake exe forshor_balanced_u > balanced_u.json
```

`ir` is the unconditionally balanced document (`shor` retargeted to
`balanced_u_(c)phase_product`), `ir_unbalanced` the policy's own.
-/

open Lean (Json)

namespace BalancedUSubmission

open Lean Meta in
/-- Constants `isDefEq`/`whnf` must not unfold during run-time extraction (as in
`Submission/PolicyMain.lean`). -/
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
/-- The policy's IR, extracted at run time exactly as `forshor_policy_submission` does. -/
unsafe def extractPolicyDoc : IO (Except String _root_.Shor.IR.Doc) := do
  try
    enableInitializersExecution
    _root_.Shor.Reflect.enableBoundedLookups
    initSearchPath (← findSysroot)
    let env ← importModules #[{module := `ForShor.ShorVerification.Submission.PolicyCheck}] {}
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

/-- Width range of the `ir.width_rule` tables, as in `forshor_policy_submission`. -/
def widthTableMax : ℕ := 2560

/-- The document: the bands, both IRs with the width rule, and the unconditional tier's record. -/
def balancedUJson (s : _root_.Shor.ShorPolicySubmission) (doc : _root_.Shor.IR.Doc)
    (sites : List (Bool × ℕ × ℕ × Bool × Bool × Bool)) : Json :=
  let wr := Json.mkObj [("width_rule", _root_.Shor.policyWidthRuleJson s widthTableMax)]
  let siteJson (r : Bool × ℕ × ℕ × Bool × Bool × Bool) : Json :=
    Json.mkObj [("agrees", Json.bool r.1), ("xw", (r.2.1 : Json)), ("zw", (r.2.2.1 : Json)),
      ("split_taken", Json.bool r.2.2.2.1),
      ("split_taken_on_original_reserves", Json.bool r.2.2.2.2.1),
      ("split_taken_where_fitsB_fails", Json.bool r.2.2.2.2.2)]
  Json.mkObj [
    ("schema", Json.str "forshor.balanced-unconditional/v1"),
    ("bands", Json.arr (s.bands.map fun b => Json.mkObj [("threshold", (b.1 : Json)),
      ("k", (b.2.k : Json)), ("ops", _root_.Shor.progJson b.2.ops)]).toArray),
    ("ir", (_root_.Shor.IR.docJson (_root_.Shor.IR.BalancedU.balanceUDoc doc)).mergeObj wr),
    ("ir_unbalanced", (_root_.Shor.IR.docJson doc).mergeObj wr),
    ("balanced_unconditional", Json.mkObj [
      ("rule", Json.str "Shor.Balanced.defaultRule: s = min width, L = max width; if s < 2 or L = s: unchanged; if 2L <= 3s: pad the small operand to L (one product at L x L); else B = ceil(L/s) blocks, B-1 low blocks of width s-1 zero-extended to t, top block L-(B-1)(s-1), all products at t = max s top, block i at angle phi*2^(i(s-1)); applied at every site, with no fit check"),
      ("reserves", Json.str "Shor.Reference.referenceSiteReserve: each site of the reference layout holds the larger of the product's reserveNeed and the default rule's block need (Shor.Balanced.siteNeed), so every plan fits (Shor.Balanced.referenceFits_default)"),
      ("correctness", Json.str "Shor.Balanced.Policy.lowerGate_balanceU_correctness, Shor.Balanced.balancedUShorImplementation (kernel-checked, generic in the policy, no hypothesis)"),
      ("ir_agreement", Json.str "Shor.Reflect.BalancedU.balancedUChecks (evaluation, not a theorem)"),
      ("sites_2048", Json.arr (sites.map siteJson).toArray)])]

end BalancedUSubmission

/-- Extract the IR, run the evaluation tier and the unconditional tier, and print only a
document that passed. -/
unsafe def main (_args : List String) : IO UInt32 := do
  let s : _root_.Shor.ShorPolicySubmission := _root_.PolicySubmission.policyExact
  let t0 ← IO.monoMsNow
  match ← BalancedUSubmission.extractPolicyDoc with
  | .error e =>
      IO.eprintln s!"forshor_balanced_u: IR extraction FAILED: {e}; nothing printed"
      return 1
  | .ok doc =>
    let t1 ← IO.monoMsNow
    IO.eprintln s!"forshor_balanced_u: IR extracted at run time in {t1 - t0} ms"
    if !(_root_.Shor.IR.Doc.wellFormed doc) then
      IO.eprintln "forshor_balanced_u: extracted IR is NOT well formed; nothing printed"
      return 1
    if !(_root_.Shor.Reflect.policySubmissionChecks s doc) then
      IO.eprintln "forshor_balanced_u: evaluation tier FAILED; nothing printed"
      return 1
    let t2 ← IO.monoMsNow
    IO.eprintln s!"forshor_balanced_u: evaluation tier passed in {t2 - t1} ms"
    let (ok, sites) := _root_.Shor.Reflect.BalancedU.balancedUChecks s doc
    let t3 ← IO.monoMsNow
    if !ok then
      IO.eprintln s!"forshor_balanced_u: unconditional tier FAILED; nothing printed"
      return 1
    IO.eprintln s!"forshor_balanced_u: unconditional tier passed in {t3 - t2} ms"
    IO.println (BalancedUSubmission.balancedUJson s doc sites).compress
    return 0
