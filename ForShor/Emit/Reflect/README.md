# `Reflect/`

The extractor: the `MetaM` program that reads the verified lowering
definitions by reflection and translates them into `IR/Syntax.lean`'s
language, the drivers that run it at build time (`extract_ir_doc`,
`extract_policy_ir_doc`) and at run time (`runExtract`), and the
evaluation tiers that check an extracted `Doc` against the real circuit at
sampled widths (`Verify.lean` for a single table, `PolicyVerify.lean` for a
policy).

Import order within the folder: `Extract.lean → Targets.lean →
PolicyTargets.lean → Driver.lean → Verify.lean → PolicyVerify.lean`.
`Extract.lean` imports `IR/Syntax.lean` and the compiler/lowering modules it
reflects over; `PolicyTargets.lean` and `PolicyVerify.lean` also import
`Symbolic/Dispatcher.lean`; `Verify.lean` imports `IR/Instantiate.lean`,
`IR/WellFormed.lean` and `Lower/Registers.lean`. Outside `Emit/`,
`ShorVerification/Submission/Check.lean` imports `Driver.lean` and
`Verify.lean`, and `Submission/PolicyCheck.lean` imports `Driver.lean` and
`PolicyVerify.lean`.

## `Extract.lean` — shared machinery

Everything the per-target files share. The translator is
**registry-driven**: `translateW`/`translateA`/`translateReg` first ask
whether the exact `Expr` they hold is one the target already built and named
(a slot, a width parameter, an angle parameter, …), and only then fall back
to structural recognition of arithmetic, register-slicing constructors and
the opaque-function escape hatch. Everything is keyed by Lean *construct*
(constant name), never by `k`, table or width; an unrecognised shape is a
hard error naming the constant, never a silent guess.

- `Registry` — the named `Expr`s a target registers before translating:
  `regs`, `widths`, `angles` (matched by `isDefEq`, most specific first),
  `phaseCoeffFVar`/`coeffMExpr` (how `AExpr.coeff l m` is produced),
  `coeffOffset` (added to every emitted `coeff` index — `0` for a
  single-table document, `Σ_{j<i} q kⱼ` for band `i` of a policy document, so
  one oracle over the bands' concatenated point lists serves every band),
  `nextWidthArgs` (the fixed arguments emitted for a `commonNeededWidth`
  call — the real argument is never inspected), and `topChunkSlack` (the
  extra reserve the top chunk of a reserve split receives, read when the
  recursive call's capacity arguments are emitted).
- `buildFinFn`, `appFillingSorry` — build a `Fin k → _` record field from `k`
  fresh leaves, and apply a constant filling `Prop` positions with `sorry`
  (those positions are never inspected by translation).
- `unfoldProj`, `unfoldPhaseWorkspace`, `resolvePhaseReserve` — targeted
  unfolding of structure projections and `PhaseProdWorkspace`-style
  workspace records, instead of a general `whnf` that would cascade into
  well-founded-recursion machinery.
- `translateW : Registry → Expr → MetaM WExpr` — widths and indices:
  registry lookup, then `+ - * / max min`, literals, `regSize` of slices,
  and the opaque names (`nextWidth`, `reserveNeed_x/z`, `log2`, `mod`,
  `pow`, `step5Const`, `modpow`), recognised *before* any reduction.
- `translateA : Registry → Expr → MetaM AExpr` — angles: registry lookup,
  the Cramer coefficient application (`coeff`, via `tryCramerCoeffApp`),
  `qftPhi`, negation, and `ℚ` arithmetic on `ℕ`-cast operands (`mul`,
  `div2`, `ratio`). (`signedPair` is produced only by the hand-stated leaf
  templates.)
- `translateReg : Registry → Expr → MetaM RegExpr` — registers: registry
  lookup, `Reg.take`/`drop` slices, `leftReg`/`rightReg`,
  `ExtReg.active`/`reserve`/`grow`/`withReserve`, the `PhaseProdWorkspace`
  projections, `growExtRegTo`, and `qftXWork`/`qftZWork` (table and policy
  forms).
- `translateProp : Registry → Expr → MetaM Prop'` — `dite`/`ite` guards:
  `Eq`/`LT.lt`/`LE.le` between two `WExpr`s. A matcher-generated guard would
  need its own case; no target handled here produces one.
- `translateQubitIndex` — a qubit-valued operand as a single-qubit
  `RegExpr.qubit`.
- `translateAnnotatedOps`/`translateAnnotatedOpsGo` — the **hand-stated**
  replay of `annotatePhaseTermsAux` + `planCompileAnnotatedOpsToSignedGateAux`
  over the table's own op list, emitting one node per op and a `Node.call`
  per `phaseProduct` checkpoint. Its `.phaseProduct` case's dependent match
  cannot be reduced on symbolic slots, which is why this is written by name.
- `translateNode : Registry → Expr → MetaM Node` — the `Gate`/`LowGate`
  walk: every constructor by name, `seq` flattened (`flattenGateSeq`/
  `flattenLowGateSeq`), `adj`, `dite` → `Node.cond`, the symbolic-length
  folds (`H_reg`, `initY1`, `modExpApproxValid`, `lowerCopyConstFromUnit`)
  as `Node.loop` by name, `Naive_SignedPhaseProd`/`Naive_CSignedPhaseProd`
  as calls to `naive_leaf`/`naive_cleaf`, and a nested `lowerGateRec
  (standardSignedPhaseLoweringPlan …)` as the recursive `Node.call`.
- `translatePlan`, `translateQFTPlan` — `PhaseLoweringPlan`/`QFTLoweringPlan`
  values translated constructor by constructor, mirroring `lowerGateRec`'s
  and `lowerQFTPlan`'s own match tables (neither is `@[reducible]`, so
  `whnfR` never exposes them).
- `translateLowerGate` — `Shor.lowerGate`'s structural walk over a `Gate`,
  for the `shor` target: `Gate.QFT`/`SignedPhaseProd`/`CSignedPhaseProd`
  leaves become `Node.call`s into `qft`/`phase_product`/`cphase_product`.
  `QFTWorkSource` (`ofOps`/`ofPolicy`) says how the QFT workspace is named.

## `Targets.lean` — the single-table extraction targets

One function per template, each specialising a real definition to a
concrete `Shor.ShorLoweringSetup` (quoted with `ToExpr`, so every `match ops
with …` collapses), introducing the symbolic inputs as local constants,
registering what it already knows, and calling `translateNode`.

- `precomputeSideSlots`, `precomputePhaseProductSlots` — the **hand-stated**
  layout bookkeeping: the per-chunk slot registers and widths
  (`initSignedLayoutState`/`targetSignedLayoutState`) and the per-side
  reserve split (`ReserveBudget.ofRequirements`/`fillSlack`, including the
  top chunk's slack), built by calling the real functions and registered
  against the `RegExpr`/`WExpr` formulas they are known to equal — reducing
  them through a `LayoutState` projection chain gets stuck.
- `setupPtsExprs (setup) (kE)` — the setup's own points, quoted, with a
  `decide` proof of `pts.length = q k`.
- `extractPPBody (setup)` — `pp_body`: one level of `compileOpsToSignedGate`
  with the layout left symbolic (per-child reserve variables). Test-only;
  not shipped.
- `naiveLeafTemplate`, `naiveCLeafTemplate` — `naive_leaf`/`naive_cleaf`,
  the schoolbook double loop over `signedTerms x`/`signedTerms z`, **stated
  by hand** (a `List.flatMap` over a symbolic-length list has no equation
  lemma to unfold) and checked by evaluation like everything else.
- `extractPhaseProductBody (setup)`, `extractCPhaseProductBody (setup)` —
  `phase_product`/`cphase_product`: `standardSignedPhaseLoweringPlan`'s
  `.eq_1` unfolded exactly once, the recursion guard `nextWidth(xw, zw) <
  max(xw, zw)` as `Node.cond`, the step branch through
  `translateAnnotatedOps`, the base branch a call to the leaf. Width
  parameters `xw, zw, xCap, zCap`; angle `phi`; registers `x, z` (and
  `ctrl`).
- `extractQFTBody (setup)` — `qft`: `standardQFTLoweringPlan`'s `.eq_1`,
  two nested `dite`s (`regSize r = 0` / `= 1` / recurse), with the two
  workspace pools `xWork`/`zWork` threaded through unchanged.
- `extractShorGateBody` — `shor_gate`: `orderFindingApprox` as a `Gate`
  tree, table-independent; the `H_reg`, `initY1` and per-exponent-bit loops
  are the hand-stated `Node.loop`s.
- `extractShorBody (setup)` — `shor`: `lowerGate k hk ops (orderFindingApprox
  …)`, the fully lowered reference circuit, through `translateLowerGate`.

## `PolicyTargets.lean` — per-band targets

A policy document has one `phase_product_<i>`/`cphase_product_<i>` body per
band, routed between by the dispatcher (`Symbolic/Dispatcher.lean`). A band's
body is the body of its table: `Policy.signedPlanOf.eq_2`'s right-hand
side read through `Policy.canonicalStep`, with the recursive child left as
a `Node.call "phase_product"` — the same route `Targets.lean` takes at
`constPolicy`.

- `extractPolicyPhaseProductBody (polE) (setup) (i) (offset)`,
  `extractPolicyCPhaseProductBody …` — band `i`'s body, with
  `Registry.coeffOffset := offset`. The two hypotheses `eq_2` needs
  (`hchoose : P.choose … = some T`, `hws : Policy.WorkspaceOK P x z`) are
  introduced as local constants, not `sorry`: a free variable is what the
  registry walks past, and it keeps `sorryAx` out of the `Doc`. What
  re-establishes `hchoose` is the dispatcher's guard, proved to pick band
  `i` exactly where `chooseIdx` does.
- `extractPolicyQFTBody (polE)`, `extractPolicyShorBody (polE)` — `qft` and
  `shor` for a policy: `Policy.qftPlan.eq_1` as `extractQFTBody` does, and
  `extractShorBody`'s walk with `QFTWorkSource.ofPolicy`. Both call
  `phase_product` by name, which in a policy document is the dispatcher.

## `Driver.lean` — `ToExpr` and the entry points

- `ToExpr WExpr`, `ToExpr Node` — written by hand (`wexprToExpr`/
  `nodeToExpr` paired with a `List`-of-self helper) because `deriving
  ToExpr` rejects the nested-`List` shape; `AExpr`, `RegExpr`, `Prop'`,
  `Template`, `Doc` derive theirs.
- `buildDoc (setup) (includePPBody := false) : MetaM Doc` — the single-table
  `Doc`: `phase_product`, `cphase_product`, `qft`, `shor_gate`, `shor`,
  `naive_leaf`, `naive_cleaf`; `entry := "phase_product"`; `opaqueFns` the
  ten opaque names with their arities. `pp_body` only when asked.
- `sameTable`, `policyBandBodies (controlled) (polE) (bands, offsets)` —
  band bodies, extracting each distinct table once: a band whose table
  already occurred reuses the earlier body with `IR.shiftCoeffN` applied
  and the template renamed. (Body extraction is minutes per band; policies
  at large `n` repeat a few tables over many bands.)
- `buildPolicyDoc (s : ShorPolicySubmission) (polE) : MetaM Doc` — the policy
  `Doc`: `IR.dispatcherTemplate` for both flavours, the band bodies, and the
  shared `qft`/`shor_gate`/`shor`/leaf templates. `polE` must name the
  declared policy constant (a `ShorLoweringPolicy` carries a proof field, so
  it cannot be quoted with `ToExpr`).
- `extract_ir_doc <id> <setup>`, `extract_ir_doc_with_pp_body <id> <setup>`,
  `extract_policy_ir_doc <id> <submission>` — build-time commands: resolve
  the identifier, `evalExpr` it, run the extractor, and register `def <id> :
  IR.Doc` directly with `addDecl`/`compileDecl` (a `Doc` is too large to
  round-trip through delaborated syntax). `Tests.lean` and
  `Submission/Check.lean`/`PolicyCheck.lean` pin their `Doc`s this way.
- `runExtract (k) : IO (Except String Doc)` — the run-time entry point behind
  `forshor_emit template`/`bundle`/`pp`/`cpp`/`qft`: `importModules` on
  `Reflect.Targets` with `loadExts := true` (hence `unsafe`), `maxHeartbeats
  := 0`, and `buildDoc (standardLoweringSetup k h)`. Standard table only;
  a custom table is a build-time path.

## `Verify.lean` — the single-table evaluation tier

Checks an extracted `Doc` against the real circuit by evaluation:
`instantiate`/`instantiateGate` with an `Env` built from the real opaque
functions, compared with the real compiled or reference term. This is a
canary over a ladder of widths derived from the table, not a theorem and
not an exhaustive scan.

- `flattenLowGate`, `flattenGate` — flatten a `;;` chain, recursing into
  `.adj` bodies.
- `GateTok`, `tokenizeLowGate`, `tokenizeGate`, **`lowGateAgrees`**,
  **`gateAgrees`** — the comparison: two trees agree iff their flat
  leaf-token streams (with adjoint boundaries marked) are equal.
  Tail-recursive, so a circuit of hundreds of thousands of tokens compares
  without deep recursion; the derived `BEq LowGate` is not stack-safe on a
  deep adjoint.
- `opaqueDispatch (ops)`, `coeffDispatch (k) (pts) (hpts)` — the `Env`
  oracles: the opaque width functions evaluated directly, and
  `cramerCoeffFromPtsWidth` over the setup's own points.
- `phaseProductAgrees`, `cPhaseProductAgrees`, `qftAgrees` — one template
  instantiated at concrete registers against the real term;
  `checkPhaseProductAt (setup) (n) (doc) (slack)`, `checkCPhaseProductAt`,
  `checkQftAt (setup) (w) (doc)` build those registers with
  `Lower/Registers.lean`.
- `canaryInst` (`a = 2, N = 15`), `largeInst` (`a = 2, N = 143`), `shorEnv`,
  `checkShorGateAt (setup) (inst) (m) (doc)`, `checkShorAt …` — `shor_gate`
  against `orderFindingApprox` and `shor` against `referenceShorCircuit` at
  a reference instance and precision.
- `checkNaiveLeafAt (doc) (xw zw)`, `checkNaiveCLeafAt` — the hand-stated
  leaves at one `(xw, zw)` pair.
- `ppRecursionDepth`, `qftPPRecursionDepth`, `widthSearchBound`,
  **`ppWidthLadder (ops)`**, **`qftWidthLadder (ops)`** — the sampled widths,
  derived from the table's own `nextWidth` chain: the largest base-case
  width plus the smallest widths reaching one, two and three levels of
  recursion (three is what makes a grandchild of the top-level call exist);
  for `qft`, `4`, `8`, `9` and the smallest odd width whose embedded phase
  product recurses.
- `submissionPPWidths`, `submissionPPSlacks` (`[0, 64]` — the two reserve
  regimes, since `fillSlack` gives the whole remainder to the top chunk),
  `submissionQFTWidths`, `submissionLeafWidths`,
  `submissionShorGateInstances`, `submissionShorInstances` — the lists the
  tier samples.
- **`evaluationChecks`**, **`submissionChecks (setup) (doc) : Bool`** — the
  evaluation tier as one `Bool`: `doc.wellFormed` and every check above over
  those lists. `submissionChecks` is what `Submission/Check.lean` pins with
  `native_decide`.
- `verifyDoc (setup) (doc) : Except String Unit` — the same sampling as an
  `Except` naming the first failed check; the run-time canary.
- `runExtractAndVerify (k)` — `runExtract` then `verifyDoc`; a failure
  refuses `template`/`bundle` with exit 3.

## `PolicyVerify.lean` — the policy evaluation tier

The same kind of check for a policy document, against
`Policy.lowerSignedPhaseProd` and friends. Instantiating the entry template
`phase_product` — the dispatcher — exercises the guard chain, the band body
it routes to, and the recursion back through the dispatcher. What is proved
is the routing (`IR.dispatcherCallAt_dispatcherTemplate`); what is sampled
is whether each band's body matches the circuit.

- `policyNextWidth`, `policyOpaqueDispatch (P)`, `policyCoeffDispatch (s)` —
  the oracles keyed on a policy. The width oracle has `opaqueDispatch`'s
  signature exactly; the coefficient oracle resolves an index against the
  bands' concatenated point lists (`Registry.coeffOffset`).
- `policyPPRegisters (P) (n) (slack)`, `policyQftRegister (P) (w)` —
  registers with reserves sized by `Policy.reserveNeed`/`Policy.qftWorkspaceNeed`.
- `policyPhaseProductAgrees`, `checkPolicyPhaseProductAt`,
  `policyCPhaseProductAgrees`, `checkPolicyCPhaseProductAt`,
  `checkPolicyQftAt`, `policyShorEnv`, `checkPolicyShorGateAt`,
  `checkPolicyShorAt` — the full-depth checks, counterparts of
  `Verify.lean`'s.
- `policyPPRecursionDepth`, `policyQFTWidthLadder`, `policyDepthWidths` —
  sampled widths from the policy's own `nextWidth` chain: the smallest widths
  reaching one, two and three levels of recursion, and the odd QFT widths
  straddling the lowest threshold.
- `shallowLeafCall`, `policyBandBodyAgrees`, `policyCBandBodyAgrees`,
  `checkPolicyBandBodyAt (s) (i) (doc) (slack)`, `checkPolicyCBandBodyAt` —
  band `i`'s body **one level deep**, at the band's own threshold: each child
  call becomes the phase-product leaf the compiler emits there
  (`Env.leafCall`), compared at the `Gate` level with
  `compiledSignedPhaseGate` on `Policy.canonicalStep`'s layout. A call whose
  capacity arguments do not equal the capacities of the registers it passes
  is rejected without unrolling the child.
- `policyLeafCount`, `policyFullDepthLeafBudget` (`100`) — the leaf-count
  budget that decides which full-depth widths are affordable.
- `probeSearchBound`, `probeShrinkWidth`, `probeThresholdsRev`,
  **`probeSubmission (s)`**, `withDispatchers`, `dispatchersAre` — the
  **probe submission**: the same setups in the same band order at the
  smallest thresholds at which each table's step shrinks, so the cost of
  the sampled checks depends on the tables and not on the submitted
  thresholds (which are `Θ(n)` for a best-known policy). Nothing the
  sampled checks test depends on a threshold except the dispatcher, which
  is rebuilt for the probe and tied back to the submitted document by
  `dispatchersAre`.
- `opKey`, `sameSetup`, `bandOffsets`, `firstSameBand`, `bandCopyOK` —
  distinct tables are checked once: a band whose table occurred earlier is
  checked *symbolically* to be exactly the earlier body with `coeff`
  indices shifted (`IR.shiftCoeffN`).
- `policyDepthWidths`, `policyProbeChecks (s') (doc')` — the sampled checks
  on the probe submission and probe document.
- **`policySubmissionChecks (s) (doc) : Bool`** — the policy evaluation
  tier: `doc.wellFormed`, `dispatchersAre doc s.policy`, and
  `policyProbeChecks` on `probeSubmission s`. The `forshor_policy_submission`
  executable (`Submission/PolicyMain.lean`) evaluates it natively.
