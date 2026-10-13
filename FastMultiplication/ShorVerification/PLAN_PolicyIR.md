# IR extraction for a policy: per-band templates and a width dispatcher

Follow-up plan 1 of the two §9 of [`PLAN_Policy.md`](PLAN_Policy.md) hands
on. That plan stopped at `policy_submission_correct`: a policy submission
carries its correctness theorem but no resource estimate, and
`forshor_policy_submission` prints `"ir": null` with an `ir_status` naming
this document as the missing work.

The goal is one sentence: **make `extract_ir_doc`'s treatment of a single
table work for a width-indexed list of them**, so a policy submission is
scored the way a table submission is.

Paths are relative to `FastMultiplication/` unless noted. `P/` abbreviates
`ShorVerification/Implementation/PhaseProduct/`.

Baseline: `PLAN_Policy.md` items 2–8 complete, `lake build FastMultiplication
EmitTests Submission PolicySubmission` green with no warnings,
`Emit/Tests.lean` reporting `69084`.

---

## Status (2026-10-13)

**Items 2–8 are done.** `lake build PolicySubmission` is green with the IR
extracted, well-formed and pinned against the real circuit, and
`lake exe forshor_policy_submission` prints an 11-template document:
`phase_product` and `cphase_product` (the dispatchers), `phase_product_0/1`
and `cphase_product_0/1` (the band bodies), `qft`, `shor_gate`, `shor`,
`naive_leaf`, `naive_cleaf`. A policy submission is scored.

Eight things turned out differently from the text below, and the text is
left as written so the reasoning stays readable.

1. **`withLocalDecl`, not `mkSorry`, for the band hypotheses** (§0.4). A free
   variable of the right type is what the registry already walks past, and it
   keeps `sorryAx` out of the produced `Doc` entirely — so **risk 2 does not
   arise**. `Policy.canonicalStep` reduces perfectly well with an opaque
   proof fvar.
2. **Item 2's test became a proof.** `IR.dispatcherCallAt_dispatcherTemplate`
   shows the emitted guard chain picks the same band as `chooseIdx` at
   *every* width, with `chooseIdx_map` tying `chooseIdx` to `choose`. That is
   strictly stronger than the sampled `native_decide` the item asked for, so
   the sampled test was not also written.
3. **The `coeff` oracle *does* need per-band disambiguation** — §0.3's "no
   per-band functions" covered the *width* functions and missed this one.
   Two bands with different `k` have different point lists, so both would
   emit `coeff 0` meaning different numbers. Fixed with a new
   `Registry.coeffOffset`: band `i`'s indices start at `Σ_{j<i} q kⱼ`, making
   the index a position in the bands' point lists concatenated. **No `AExpr`
   change and no schema change**, and the single-table case is the identity
   (one band, offset 0).
4. **`translateLowerGate` needed a parameter change.** It took `opsE` purely
   to carve `Gate.QFT`'s workspace; it now takes a `QFTWorkSource` naming the
   two constants and their owner, so `Shor.lowerGate` and
   `Shor.Policy.lowerGate` share the walk.
5. **Six recognition sites needed policy twins.** `Policy.qftWorkspaceNeed`,
   `Policy.qftXWork` and `Policy.qftZWork` are `abbrev`s, so without cases of
   their own they unfold through `qftXWorkOf` into a `Reg` literal that no
   later case recognises. Two in `translateW`'s `Prod.fst`/`.snd`, two in its
   `regSize`, two in `translateReg`.
6. **Decidability instances** for `Policy.WorkspaceOK`, `Policy.CWorkspaceOK`
   and `Policy.QFTReserveOK` were needed before the evaluation tier could
   write `if hws : … then`. Appended to `Emit/Lower/Decide.lean`, same
   `decidable_of_iff` shape as the fixed-table three.
7. **Item 7 got simpler, not more compositional.** Instantiating the *entry*
   template exercises the dispatcher's guard chain, the band body it routes
   to, and the recursion back through the dispatcher in one — so there is no
   need to check band bodies separately, and a width at the top of the policy
   covers every band the chain descends through. What the ladder adds over a
   table's is the **band boundaries** (`t` and `t-1` for each threshold),
   which is where the chain changes table.
8. **The `qft` ladder had to be trimmed.** Straddling the *top* threshold
   means a `qft` at `w ≈ 2·t₀`, whose embedded phase product starts at `t₀`
   and recurses all the way down: that check alone ran over 15 minutes and
   tests nothing the phase-product ladder does not already test at `t₀`
   directly. Only the lowest threshold is straddled now.

Item 6 landed with one correction worth recording: the first version of
`Doc.reaches` had no visited set, so on a cyclic graph the frontier never
emptied, fuel ran out, and its conservative "assume reachable" default
demanded a guard everywhere — which rejected `shor`. With a visited set the
search terminates properly. The resulting rule is *every* edge of a cycle
guarded, which is stricter than termination needs but is what every extracted
document satisfies; `WellFormed.lean` says so.

Costs, measured: per-band extraction ~65 s for the two-band example (risk 1
was real but mild), and `lake build PolicySubmission` a few minutes including
the `native_decide` evaluation tier.

---

## 0. What the survey established

Checked against the tree as it stands after `PLAN_Policy.md` item 8, not
assumed. Four of these findings make the job **smaller** than §9 projected;
two make it sharper.

### 0.1 The extractor is already on the policy path

`PLAN_Policy.md` item 4 moved the single-table extraction through the policy
machinery at `constPolicy`, so there is no "switch the extractor over to
policies" step left to do:

- `Emit/Reflect/Targets.lean:321` (`extractPhaseProductBody`) already builds
  `polE := constPolicy tblE`, `hwsPE := Policy.workspaceOK_of_const …`,
  `hchooseE := constPolicy_choose tblE sizeE`, and reads
  **`Policy.signedPlanOf.eq_2`** — the dispatcher's `some` branch — for the
  `dite` it walks. Its docstring already says so.
- `Emit/Reflect/Extract.lean:1449–1454` recognises `Shor.Policy.stepPlan`,
  `Shor.Policy.cStepPlan` and `Shor.Policy.phaseProdUsingPlan` as named
  builders to unfold through their `.eq_1`.
- The positional matches at `Extract.lean:1367–1374` are already the policy
  constructors' arities (`signedStep` 11 args, `cSignedStep` 13).

### 0.2 Nested policy plans already translate to a call to the dispatcher

`Extract.lean:1301–1331` matches `Policy.signedPlanOf`, `Policy.signedPlan`
and their controlled twins and emits

```lean
.call "phase_product" [xw, zw, xCap, zCap] [phi] [x, z]
```

So the name `phase_product` is *already* the name a nested plan calls. Keep
it for the **dispatcher** and name the per-band bodies `phase_product_<i>`,
and every existing self-call site, plus `qft`'s call into the phase product,
keeps working with no edit at all.

### 0.3 The opaque width functions do **not** become per-band

§9 projected `nextWidth_<i>`, `reserveNeed_x_<i>`, `reserveNeed_z_<i>`. That
is not needed, and the reserve case is actually *wrong*:

`Policy.reserveNeed` (`P/Compiler/PolicyWorkspace.lean:58`) is

```lean
def reserveNeed (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ × ℕ :=
  match P.choose (max wx wz) with
  | none => (0, 0)
  | some T => … immediateXNeed T.ops wx wz + T.k * (reserveNeed P Wnext Wnext).1 …
```

— a **single** function of `(wx, wz)` for a fixed `P`. The band enters only
through `P.choose (max wx wz)` *inside* it, and the recursion crosses bands,
so there is no per-band reserve to emit: a `reserveNeed_x_<i>` keyed to band
`i`'s table repeated forever would be a different and smaller number than
the reserve the circuit actually carves, which is sized for the whole
descending chain.

`nextWidth T.ops wx wz` *is* band-local (`requiredChildReserve`,
`PolicyWorkspace.lean:224`, mixes the two). But band `i`'s body template is
only ever entered under the dispatcher guard `t_i ≤ max xw zw`, where
`P.choose (max xw zw) = some T_i` — so the policy-keyed function

```lean
fun xw zw => match P.choose (max xw zw) with
             | some T => nextWidth T.ops xw zw
             | none   => max xw zw          -- no table: no step
```

agrees with band `i`'s own `nextWidth` everywhere band `i`'s body can
evaluate it. One 2-ary name covers every band.

**Consequences.** `opaqueFns` is unchanged — same ten names, same arities.
`IR/Syntax.lean` is unchanged. `tableOpaqueW`, `widthTable` and
`splitWidthTable` (`Emit/Symbolic/Width.lean`) keep their shapes and their
published row formats; only the *contents* of the rows become policy-derived.
**`forshor.ir/v1` therefore needs no version bump and no `policy` field**,
which §9 left open — decided here: no bump. What changes is the template
list, and a `Doc` has always carried an arbitrary list of templates.

### 0.4 `hchoose` under a symbolic width is a `mkSorry`, and that is in keeping

The one real obstruction to reusing `extractPhaseProductBody` per band:
`Policy.signedPlanOf.eq_2` needs `P.choose (phaseInputSize x z) = some T`,
and with `x`/`z` symbolic that equation is **not** available for a real
policy — it holds only under the band guard.

The existing extractor already solves the same problem twice, for the shrink
test: it takes both `dite` branches by applying the branch function to
`← mkSorry condE false` and `← mkSorry notCond false` (`Targets.lean:377–378`,
`Extract.lean:1396–1400`). `hchoose` gets the identical treatment — a
`mkSorry` of `P.choose (phaseInputSize x z) = some T_i`, used only to select
which equation lemma's right-hand side to walk.

This does not weaken anything. D7's trust statement is the translation table
and Lean's normaliser, *checked by `instantiate` agreeing with the real term*
— proof terms are already explicitly outside it ("trust is the translation
table, not any particular proof term", `Extract.lean:1440`). The band guard
is then re-established, for real, by the dispatcher emitting it as the
`Node.cond` that routes to this body, and by the evaluation tier of item 7
instantiating each body only at widths inside its own band.

### 0.5 `WellFormed` check 3 goes vacuous, and never tested what the README says

`IR/WellFormed.lean:155` is

```lean
(template != selfName || guarded)
```

— **direct** recursion only. A dispatcher→body→dispatcher cycle has no call
whose target equals its enclosing template, so after this plan check 3
passes without examining anything. It does not fail; it stops saying
anything, which is worse, and is why item 6 below exists.

Separately, and as §9 anticipated: `guardLicensesRecursion` accepts `lt`/`le`/`eq`
with `wLicenses` on *either* side, and `wLicenses` returns `true` for **any**
`WExpr.opaque` whatever (`WellFormed.lean:101`). So `foo(xw) < 0` licenses
recursion exactly as well as `nextWidth(xw, zw) < max(xw, zw)` does. Check 3
is a shape check and has never been a termination check. The README's
wording oversells it today; item 6 fixes the wording as well as the check.

### 0.6 `extract_ir_doc` needs a sibling, not a generalisation

`Reflect/Driver.lean`'s `elabExtractIrDocImpl` hard-codes

```lean
let setupTyE := mkConst ``Shor.ShorLoweringSetup
let setup ← Lean.Meta.evalExpr Shor.ShorLoweringSetup setupTyE (mkConst setupName)
```

`ShorPolicySubmission` is a different type with a different `evalExpr`, and
`buildDoc` takes a `ShorLoweringSetup`. A parallel `buildPolicyDoc` /
`extract_policy_ir_doc` is cleaner than making one command polymorphic over
two unrelated record types, and it keeps the single-table path — which is
shipped and scored — byte-identical.

---

## 1. Discipline

Carried over from `PLAN_Policy.md` §1, because the same hot files are in
play:

- New definitions go in **new leaf files** wherever possible.
  `Emit/Symbolic/Dispatcher.lean` and `Emit/Reflect/PolicyTargets.lean` are
  new; `Extract.lean` (1690 lines, imported by everything in `Reflect/`) is
  edited in exactly one item.
- While iterating, build the **module**, not the target:
  `lake build FastMultiplication.Emit.Reflect.PolicyTargets`.
- `EmitTests` is in every check line. Six extraction sites match constructor
  arities positionally; a miss fails the build rather than silently
  corrupting the printed IR, but only if `EmitTests` is built.
- Each numbered item is one commit and builds all four lake targets green.
- `Emit/Tests.lean`'s gate count assertion (`69084`) must not move in items
  1–6: nothing there yet touches a policy. Item 7 adds new assertions; it
  must not change existing ones.

---

## 2. The dispatcher template — new file `Emit/Symbolic/Dispatcher.lean`

A **pure** function, not a reflected one. The dispatcher has no Lean term to
read: it is `ShorLoweringPolicy.choose`'s chain of guards, which is data.

```lean
def dispatcherTemplate (P : ShorLoweringPolicy) (prefix : String) : IR.Template
```

with `prefix` `"phase_product"` or `"cphase_product"`, producing

```
body = cond (le (lit t₀) (max (var "xw") (var "zw")))
         (call "phase_product_0" [xw, zw, xCap, zCap] [phi] [x, z])
       (cond (le (lit t₁) (max (var "xw") (var "zw")))
         (call "phase_product_1" …)
         … (call "naive_leaf" [xw, zw] [phi] [x, z]))
```

`wParams := ["xw","zw","xCap","zCap"]`, `aParams := ["phi"]`,
`rParams := ["x","z"]` — exactly the parameter lists the existing
`phase_product` template has, so every call site in `qft`, in `shor`, and in
the band bodies type-checks against it unchanged (check 2 is an arity
check).

Three things to get right, each a direct reading of `Framework/Policy.lean`:

- **Guard on `max xw zw`**, because `choose` is keyed on
  `phaseInputSize x z = max x.width z.width` (`Compiler/Widths.lean:41`).
- **Guards in band order, `≤`, first match wins.** `choose` is
  `P.bands.find? (fun b => decide (b.threshold ≤ n))` — a `find?`, so the
  chain must be a right-nested `cond` in list order, not a set of disjoint
  range tests. `sorted` is what makes the two agree.
- **The fallthrough is `naive_leaf`**, matching `choose = none`'s
  `signedBase`.

The controlled twin differs only in `prefix`, in calling `naive_cleaf`, and
in `rParams` gaining `ctrl` — mirroring `extractCPhaseProductBody`'s existing
treatment of `ctrl` as a `RegExpr.var` despite its Lean type being `ℕ`.

**Test in the same commit** (`Emit/Tests.lean`, new section): for the
shipped `PolicySubmission.policy`, `dispatcherTemplate` instantiated at a
width in each band and one below the last threshold selects the band
`P.choose` selects. This is a `native_decide` on two `List`s agreeing, and it
is what stops the chain and `choose` drifting apart later.

---

## 3. Per-band body extraction — new file `Emit/Reflect/PolicyTargets.lean`

`extractPhaseProductBody` is already 85% of this. Generalise its *inputs*
and leave its body alone:

```lean
def extractPolicyPhaseProductBody
    (P : ShorLoweringPolicy) (T : ToomCookTable) (i : ℕ) : MetaM IR.Template
```

Three changes against `Targets.lean:321`:

1. `polE` is `P` (quoted via `toExpr`), not `constPolicy tblE`; `tblE` is
   band `i`'s table.
2. `hchooseE` is `← mkSorry (P.choose (phaseInputSize x z) = some T) false`
   rather than `constPolicy_choose` (§0.4).
3. `hwsPE` is a `mkSorry` of `Policy.WorkspaceOK P x z` rather than
   `workspaceOK_of_const` applied to a `SignedRecursiveWorkspaceOK` local —
   the fixed-table precondition is not the right hypothesis for a band, and
   the extractor never inspects it.
4. `name := s!"phase_product_{i}"`, `provenance := s!"Shor.Policy.stepPlan at band {i}"`.

Everything downstream of `Policy.signedPlanOf.eq_2` — the `dite` walk,
`Policy.canonicalStep`, `precomputePhaseProductSlots`, the registry, both
branches — is untouched, because none of it ever looked at *why* `choose`
returned a table.

The `else` branch of the body's own `dite` (the shrink test failed) stays a
call to `naive_leaf`, as today. This is the second of the two leaf exits and
it is **not** the same as the dispatcher's fallthrough: the dispatcher's
means "no band covers this width", the body's means "this band's table does
not shrink here". `Policy.bandShrinks` is the advisory check that the second
one is unreachable in practice (`Submission/PolicyDecide.lean`); the IR must
keep emitting it regardless, because admissibility does not require it.

**Do not delete** `extractPhaseProductBody`. The single-table path is
shipped and scored, and `Emit/Tests.lean` pins its output.

---

## 4. `buildPolicyDoc` and `extract_policy_ir_doc` — `Emit/Reflect/Driver.lean`

```lean
def buildPolicyDoc (s : Shor.ShorPolicySubmission) : MetaM IR.Doc := do
  let bodies ← s.bands.zipIdx.mapM fun (b, i) =>
    extractPolicyPhaseProductBody s.policy b.2.table i
  let cbodies ← …
  pure { templates := dispatcherTemplate s.policy "phase_product"
                    :: dispatcherTemplate s.policy "cphase_product"
                    :: bodies ++ cbodies ++ [qft, shorGate, shor,
                                             naiveLeafTemplate, naiveCLeafTemplate]
         opaqueFns := …   -- unchanged, §0.3
         entry := "phase_product" }
```

`qft`, `shor_gate` and `shor` are extracted exactly as today except that
their `setup` argument becomes the policy — they reach the phase product
only through `Policy.signedPlan`, which §0.2 already routes to the
dispatcher's name.

`extract_policy_ir_doc <id> <policyIdent>` is `elabExtractIrDocImpl` with
`Shor.ShorPolicySubmission` in place of `Shor.ShorLoweringSetup`. Factor the
shared tail (`addDecl`/`compileDecl` on `toExpr doc`) rather than copying it.

**Cost note.** `buildDoc`'s heaviest targets already need
`set_option maxHeartbeats 4000000` at build time, and `runExtract` disables
the limit entirely. A policy multiplies the phase-product extraction by the
band count. Budget for `PolicyCheck.lean` going from seconds to minutes, and
measure before item 7 rather than after.

---

## 5. Policy-keyed oracles — `Emit/Reflect/Verify.lean`, `Emit/Symbolic/Width.lean`

Shapes unchanged (§0.3); only the definitions move from `ops` to `P`:

```lean
def policyOpaqueDispatch (P : ShorLoweringPolicy) : String → List ℕ → Option ℕ
  | "nextWidth",     [xw, zw] => some (policyNextWidth P xw zw)
  | "reserveNeed_x", [xw, zw] => some (Policy.reserveNeed P xw zw).1
  | "reserveNeed_z", [xw, zw] => some (Policy.reserveNeed P xw zw).2
  | "qftXWork",      [w]      => some (Policy.qftWorkspaceNeed P w).1
  …
```

with `policyNextWidth` the total function of §0.3. The remaining five names
(`log2`, `mod`, `pow`, `modpow`, `step5Const`) are arithmetic and the
modulus, and do not see the table at all.

`widthTable`/`splitWidthTable` take `P` instead of `ops`. Their row formats
and `tableOpaqueW`'s lookup logic are untouched — this is the payoff from
§0.3, and it means a consumer holding only a published bundle needs no new
code to instantiate a policy document.

---

## 6. Well-formedness: make check 3 mean something again — `Emit/IR/WellFormed.lean`

Two changes, and an honest README.

**6a. A two-hop view.** Generalise `guarded` from a `Bool` about the
enclosing template to a check over the call graph: a call to `t'` is
permitted when `t'` is not reachable back to `selfName`, or when the call
sits under a qualifying guard. The dispatcher is the natural place to put
the pass-through marking — it has no body of its own beyond the chain — but
marking it is a *weaker* check than the two-hop view, so prefer the latter
and fall back to the marking only if the call-graph reachability proves
awkward to write in `Bool`.

**6b. Say what it checks.** `WellFormed.lean`'s header and
`Emit/IR/README.md` both describe check 3 in language that suggests it
establishes termination. It does not (§0.5), and did not before this plan.
Reword both to "a recursive call sits under a guard that *mentions* a width
parameter or a tabulated width function" and state plainly that strict
decrease is not tested anywhere in the IR tier — it is a theorem about the
Lean term, carried by `Policy.reserveNeed`'s own `termination_by`.

This item changes no behaviour of the single-table path: its `phase_product`
still recurses directly and still satisfies the stronger reading.

---

## 7. The evaluation tier, compositionally — `Emit/Reflect/Verify.lean`, `Submission/PolicyCheck.lean`

Today `submissionChecks` instantiates `phase_product` down a chain from the
top width, which under one table is one descending ladder. Under a policy
that chain crosses every band, and the deepest instantiation is as expensive
as the whole recursion. Do not do that. Check compositionally:

- **Each band body** at a few widths *inside its own band*: the top of the
  band, the bottom, and one interior width. Each is a single level plus a
  `call` to the dispatcher, which `instantiate` does not unroll further at
  that depth — so each costs what today's `k = 2` check costs, not what the
  full chain costs.
- **The dispatcher** at one width per threshold and one just below each
  threshold — the `2 · bands + 1` widths where the chain's answer changes.
  This is the check that the emitted guards agree with `choose`, and item
  2's test is its build-time twin.
- **`qft` and `shor`** at today's ladders, unchanged.

The reserve regimes (`submissionPPSlacks = [0, 64]`) stay: §1.1 of the
original emitter plan found a real bug that only the `+64` regime exposed,
and a policy does not make that less likely.

`submissionPolicyChecks (s : ShorPolicySubmission) (doc : Doc) : Bool`
mirrors `submissionChecks`' signature so `PolicyCheck.lean` pins it with
`native_decide` the way `Check.lean` does.

**Note the tier boundary does not move.** `native_decide` here is evaluation
at sampled widths, not a theorem, exactly as for a table — and
`#assert_axioms` continues to run on `PolicySubmission.policy`, which is the
*proof* object and does not depend on any of this. `Submission/README.md`'s
"the IR is NOT proved equal to the circuit at every width" applies verbatim.

---

## 8. Turn on the score — `Submission/PolicyCheck.lean`, `Submission/PolicyMain.lean`

- `PolicyCheck.lean` gains `extract_policy_ir_doc doc policy` and the
  `native_decide` pin from item 7.
- `PolicyMain.lean`'s `"ir"` becomes `IR.docJson doc`; `ir_status` is
  deleted; `"score"` stops saying UNSCORED and says what `Main.lean` says.
- `Submission/README.md`: delete "What a policy does not yet get", and move
  the policy into the same two-tier description the table has.
- Top-level `README.md`: the paragraph added by `PLAN_Policy.md` item 8
  saying a policy is "admissible and unscored" comes out.
- `PolicyCheck.lean`'s docstring section "NOT checked by evaluation — and
  this is a gap, not an oversight" comes out.

Doing this as the last item, not the first, is the point: until items 2–7
are green the `"ir": null` text is **true**, and it should stay true until it
is not.

---

## 9. Risks, in order

1. **Extraction cost per band** (§4). The phase-product extraction is the
   expensive one and it now runs once per band. If `PolicyCheck.lean` becomes
   a multi-minute build, the mitigation is to extract bodies for distinct
   *tables* rather than distinct bands (two bands sharing a table share a
   body), and failing that to cap the shipped example at two bands and
   document the cost. Measure at item 4, before item 7 depends on it.
2. **`mkSorry` of `hchoose` reaching the output.** It should be consumed
   entirely by equation-lemma selection. If a `sorryAx` ever appears in a
   *term* the extractor walks into, it will surface as an unrecognised
   construct, not as silent corruption — but add an explicit assertion that
   the produced `Doc` contains no `opaque` named `sorryAx` to be sure. Note
   that `#assert_axioms` cannot help here: it audits `PolicySubmission.policy`,
   and the `Doc` is data produced by an `unsafe` elaborator, outside its
   reach by construction.
3. **The band guard and `choose` drifting apart.** Item 2's test and item 7's
   dispatcher checks are both aimed at this; keep both, since one is
   build-time over the template and the other is evaluation over the
   instantiated circuit.
4. **`policyNextWidth`'s `none` case.** Returning `max wx wz` (no step) is
   the choice that makes the function total; check that no caller reads it
   as a real next width below the last threshold, where the leaf runs and
   there is no next level.
5. **`qft`'s unequal split under a policy.** `splitWidthTable` exists because
   `qft` calls the phase product at `(v/2, v - v/2)`, unequal at odd `v`.
   Under a policy the band is chosen by `max` of those two, so odd widths
   near a threshold can route differently from the diagonal. The table
   already stores the asymmetric row; the risk is a *test* that only exercises
   the diagonal. Item 7's dispatcher widths must include an odd `v` whose
   halves straddle a threshold.

---

## 10. Verification

```bash
lake build FastMultiplication EmitTests Submission PolicySubmission
lake build forshor_emit forshor_submission forshor_policy_submission
lake exe forshor_emit 2 2 15 0 > /dev/null
lake exe forshor_submission        | python3 -c 'import json,sys; json.load(sys.stdin)'
lake exe forshor_policy_submission | python3 -c 'import json,sys; d=json.load(sys.stdin); assert d["ir"] is not None'
lake env lean scripts/AxiomCheck.lean
bash scripts/check_template_lexical.sh FastMultiplication/ShorVerification/Submission/Template.lean
bash scripts/check_template_lexical.sh FastMultiplication/ShorVerification/Submission/PolicyTemplate.lean
python3 scripts/check_layers.py
python3 scripts/gen_docs_graph.py --check && git diff --exit-code docs/data/graph.js
```

plus: `Emit/Tests.lean` still reports **69084** (items 1–6 must not move it,
item 7 only adds assertions), and the single-table `ir.json` is byte-identical
to its pre-plan value — the shipped, scored path must not shift under a
change that is supposed to be additive.
