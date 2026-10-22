# `Emit/`

The `LowGate` emitter: prints the circuits this repository proves correct,
and an n-free ("symbolic") description of them a resource model can price,
as JSON. Nothing here is imported by the verified core — no theorem in
`Implementation/` or `Framework/` depends on a line of it, and the `Doc` it
extracts is explicitly not a theorem.

It is not *only* output tooling, though. `ShorVerification/Submission/`
sits above this folder: `Template.lean` runs the extractor on a submitted
table at build time and pins the result against the real circuit, which is
the second of the two tiers a submission is accepted on. So a change here can
break a submission's build — see
[`Submission/README.md`](../ShorVerification/Submission/README.md).

**New to this folder?** Read this file top to bottom once, then open each
subfolder's own `README.md` in the order `Json → Table → IR → Reflect →
Symbolic → Lower` (roughly the order the code imports in). Each sub-README
lists every file, what it defines, and how it's used by the rest of the
folder.

## Contents

- [What this tool prints](#what-this-tool-prints)
- [Three artifacts](#three-artifacts)
- [Design rules](#design-rules)
- [What is and is not a theorem](#what-is-and-is-not-a-theorem)
- [What is hand-stated](#what-is-hand-stated)
- [Folder map](#folder-map)
- [What `Tests.lean` checks](#what-testslean-checks)
- [CLI reference](#cli-reference)
- [Using a custom table](#using-a-custom-table)
- [Build](#build)
- [Known limitations](#known-limitations)

## What this tool prints

Three kinds of document, all JSON except `phases`:

- **`template <k>`**: the extracted, n-free symbolic IR —
  `phase_product`/`naive_leaf`, `cphase_product`/`naive_cleaf`, `qft`,
  `shor_gate`, `shor` — obtained by *reflection* over the real, verified
  definitions (see [Three artifacts](#three-artifacts)), except for the
  constructs listed under [What is hand-stated](#what-is-hand-stated).
  (`pp_body` is not shipped: its layout is built from per-child reserve
  variables nothing in the document says how to bind.
  `extract_ir_doc_with_pp_body` still extracts it for the test suite.)
- **`bundle`** (and its per-section commands): an **n-free** document — every
  number in it is a function of `k` (the Toom-Cook table arity) alone, never
  of a modulus bit-length `n`. It bundles the extracted `template` together
  with the opaque value tables (`--no-template` skips the template, which is
  the expensive part — see [CLI reference](#cli-reference)). It's what a
  resource-estimation model reads to price the algorithm at a width it
  hasn't been asked to instantiate yet.
- **`pp` / `cpp` / `qft`**: a **concrete-width instance** — the real,
  verified `LowGate` circuit for one signed (or controlled) phase product or
  QFT at a width you choose, either flat (`--flat`) or annotated with the
  recursion structure (the default, which also re-checks the extracted
  template against this concrete instance — `meta.checks.
  instantiate_eq_real`).
- **`shor`**: the concrete reference order-finding circuit for one Shor
  instance `(k, a, N, m)` — what `Shor.Shor_correct` is a theorem about.

## Three artifacts

Everything in this folder is one of three things:

1. **The extracted templates — the IR** (`IR/`, `Reflect/`). A `MetaM`
   program (`Reflect/Extract.lean`) reads the *definitions* on the
   `referenceProgramAt` call chain — `orderFindingApprox`,
   `standardSignedPhaseLoweringPlan`, `standardQFTLoweringPlan`, … —
   specialises them to a concrete `Shor.ShorLoweringSetup` (so every `match
   ops with …` collapses to one branch), leaves the width/angle/register
   inputs as free variables, normalises, and translates the resulting
   `Expr` into
   `IR/Syntax.lean`'s small first-order language (`WExpr`, `AExpr`,
   `RegExpr`, `Prop'`, `Node`, `Template`, `Doc`). A recursive definition
   becomes one `Template` whose body contains a `Node.call` to itself with
   translated argument expressions — the recursion is never unrolled in
   Lean; a consumer (or `IR/Instantiate.lean`'s own `instantiate`)
   unrolls it at a concrete width.

   The recursion skeleton and the arithmetic are reflected; the loops and
   the workspace bookkeeping around them are **hand-stated** and trusted on
   the sampled comparison. See
   [What is hand-stated](#what-is-hand-stated) — this is the part of the
   folder where a bug can hide.
2. **The opaque value tables** (`Symbolic/{Width,QftPlan,ShorPlan,
   CoeffPoly}.lean`). A handful of functions the templates call by name but
   never evaluate symbolically (`RecursivePhaseWorkspace.nextWidth`,
   `reserveNeed`, `qftWorkspaceNeed`, the interpolation weight `coeff(l, m)`
   `= cramerCoeffFromPtsWidth`, plus a few arithmetic primitives —
   `Nat.log2`, `mod`, `pow`, `step5Constant`, and a hand-built `modpow`).
   These tables are where their values live, evaluated directly off the
   compiler's own definitions, over a width ladder wide enough for a
   consumer's recursive unrolling to look every value up.
3. **The reference instances** (`Lower/`: `pp`, `cpp`, `qft`, `shor`). The
   real, verified circuits evaluated at a chosen concrete `(k, n)`/`(k, w)`/
   `(k, a, N, m)`. These are what the extracted templates are checked
   against — see [What is and is not a theorem](#what-is-and-is-not-a-theorem).

`k` vs. `n`: `k` is the table arity (small, fixed per invocation, e.g.
2–6). `n`/`w` is an operand or register width (can be large). The template
and the value tables are functions of `k` (and a width variable) only;
instances (`pp`/`cpp`/`qft`) and `shor` additionally take a concrete `n`/`w`.

## Design rules

The invariants the extractor and its callers are built to:

- **Run-time extraction.** `forshor_emit template <k>` loads the
  environment with `importModules` and runs the extractor on the standard
  table at `k`. No per-`k` line anywhere in this folder's own code; the
  build-time elaborator command `extract_ir_doc` extracts any
  `ShorLoweringSetup` (not just the standard one) and pins a `Doc` for
  `native_decide` tests.
- **Genericity boundary.** The translation table is keyed by Lean
  *construct* (`Gate.seq`, `dite`, `Reg.interval`, `WellFounded.fix`, …),
  never by `k`, table, or width. A new `k` or table needs no code change. An
  unknown construct is a hard error naming the constant, never a silent
  drop.
- **Recursion is not unrolled in Lean.** A recursive definition yields one
  template whose body is one activation; the recursive call is a
  `Node.call` with its argument expressions. The consumer (and the Lean-side
  `IR/Instantiate.lean`) unrolls at a concrete `n`.
- **Opaque set.** Left unevaluated and tabulated: `nextWidth`,
  `reserveNeed`, `qftWorkspaceNeed`, `coeff(l, m)`, `Nat.log2`, `mod`,
  `pow`, `step5Constant`, `modpow`.
- **A table is a `ShorLoweringSetup`.** The input to the extractor is a
  `Shor.ShorLoweringSetup` value: `k`, `hk`, `ops`, its own interpolation
  points `pts`, and the four proofs (`hpts`/`good`/`consumes`/`returns`)
  the lowering theorems need. A table that can be packaged as one is, by
  definition, a table those theorems cover; a table that cannot be is not a
  table this emitter has anything to say about, which is why there is no
  second "table source" of any kind — see `Table/README.md`. Symbolic:
  `n, m, a, N` (Shor), `W, phi, x, z` (phase product), `w, r` (QFT).
- **Reference instances stay.** `pp`, `cpp`, `qft`, `shor` and their
  annotated views are what the extracted IR is checked against.
- **Not a theorem.** Trusted: the translation table and Lean's normaliser.
  Checked: `instantiate`/`instantiateGate` unrolls the extracted `Doc` at
  concrete widths and agrees with the real term — at build time
  (`Tests.lean`'s `native_decide` suite) and at run time
  (`Reflect/Verify.lean`'s canary, run before `template`/`bundle` ever
  print anything). The provenance strings say exactly this.

## What is and is not a theorem

- The flat circuits printed by `pp`, `cpp`, `qft`, `shor` are the terms
  `lowerSignedPhaseProdWithWorkspace`, `lowerCSignedPhaseProdWithWorkspace`,
  `lowerQFT`, `referenceProgramAt` evaluate to. Their correctness is
  `Shor.lowerSignedPhaseProduct_correct`, `Shor.lowerQFT_correct`,
  `Shor.Policy.lowerGate_correctness`, `Shor.Shor_correct` (the last at
  `m = referenceChosenPrecision N`, which the emitter cannot compute).
- The annotated trees (`pp`/`cpp`/`qft`) are printed from the plan terms
  those functions consume; `annotated_eq_flat` checks the two agree by
  evaluation, and `instantiate_eq_real` checks the extracted template,
  instantiated at the requested width, against the real compiled term. Those
  two plus `Doc.wellFormed` are all the annotated CLI modes check — the full
  width-ladder canary belongs to `template` and `bundle`.
- **The extracted templates are not theorems.** They are checked against
  the real term by evaluation. That comparison is
  `Reflect.lowGateAgrees`/`gateAgrees`, which compares a flat stream of leaf
  tokens with adjoint boundaries marked. The obvious spelling
  (`flattenLowGate a == flattenLowGate b`) is *not* stack-safe — the derived
  `BEq LowGate` walks an adjoint's body one stack frame per nested gate, and
  a circuit of a few thousand gates overflows the interpreter's stack.
  `instantiate_eq_real` on `pp`/`cpp`/`qft` runs the check at whatever width
  the caller asked for; `Reflect/Verify.lean`'s canary runs it at a ladder
  of widths derived from whatever table `template`/`bundle` was asked to
  extract, before either prints anything; `Tests.lean` runs it exhaustively
  at small widths (base case and one recursive level, `k = 2, 3`, the
  standard table and a hand-built one) at build time, via `native_decide`.
- The one proved result in this folder is
  `IR.dispatcherCallAt_dispatcherTemplate` (`Symbolic/Dispatcher.lean`): a
  policy document's width dispatcher routes every width to the band
  `ShorLoweringPolicy.choose` picks. The band bodies it routes to are
  extracted and sampled like everything else.
- The opaque value tables (`coeff_poly`, `width`, `qft_plan`,
  `shor_plan`) are the named functions evaluated directly — not
  recomputed, not re-derived. `coeff_poly`'s own Gauss-Jordan `M⁻¹` is the
  one genuinely re-derived quantity, and it is cross-checked against the
  pre-existing `cramerCoeffFromPtsWidth` by evaluation
  (`cramerCoeffFromPtsWidth = phaseCoeffFromPtsWidth` is itself the theorem
  `cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth`).
- Cost-model numbers, where printed, are `shorGateResourceModel` evaluated,
  not proved bounds; the asymptotic statement they evaluate is
  `phaseProductGateCountBound_of_programOK` / `exists_shorGateCountBound`.
- The constant-arithmetic step costs (`lowerCmpGeConst`/`lowerCSubConst`,
  steps U3/U4 of `CmodMulInPlaceCore`) are fitted from concrete `shor`
  emissions outside Lean, not tabulated.

## What is hand-stated

"Extracted by reflection" is true of the recursion skeleton and the
arithmetic. It is not true of everything. Three kinds of construct are
written out by hand in `Reflect/` and trusted on the sampled comparison
instead:

- **Folds over a symbolic-length list.** `naiveSignedPhaseGates`'s double
  fold, `H_reg`'s fold over `regQubits`, `modExpApproxValid`'s per-exponent-bit
  recursion, `lowerCopyConstFromUnit`'s walk over `N.bitIndices`. No equation
  lemma turns these into a visible loop the way `.eq_1` does for
  `WellFounded.fix`, so the extractor recognises each **by name** and
  emits the `Node.loop` it knows the function to be.
- **Workspace and slot bookkeeping.** `precomputeSideSlots` and
  `precomputePhaseProductSlots` (`Reflect/Targets.lean`) restate
  `PhaseSplitLayout.child`, `ReserveBudget.ofRequirements` and `fillSlack`
  as `RegExpr`/`WExpr` formulas, because reducing the real ones through a
  `LayoutState` projection cascades.
- **The annotated-ops walk.** `translateAnnotatedOps`
  (`Reflect/Extract.lean`) replays `annotatePhaseTermsAux` +
  `planCompileAnnotatedOpsToSignedGateAux` over the table's own op list by
  hand, for the same reason.

A hand mirror is only as complete as the cases its author had in mind, and
the sampled comparison is the only detector. The reserve split, for
instance, gives the *top* chunk every leftover qubit; a capacity formula
that omits that is wrong only at a grandchild of the top-level call and
only when the parent has slack to split, which is what the width ladder and
the two reserve regimes below are there to reach.

Each of these is covered by at least one check in
`Reflect/Verify.lean`'s `evaluationChecks`:

| hand-stated construct | covered by |
|---|---|
| `naiveLeafTemplate` (`naiveSignedPhaseGates`) | `checkNaiveLeafAt` at `(13, 7)`, `(7, 13)`, `(6, 5)`, and `checkPhaseProductAt`'s base-case width |
| `naiveCLeafTemplate` | `checkNaiveCLeafAt` at the same pairs |
| `H_reg` loop | `checkShorGateAt` at both reference instances (`N = 143`, `m = 1` is the one with a long loop) |
| `initY1` | `checkShorGateAt`, both instances |
| `modExpApproxValid` per-exponent-bit loop | `checkShorGateAt`, both instances; `checkShorAt` at the small one for its lowering |
| `lowerCopyConstFromUnit` bit loop | `checkShorAt` (it appears only in the lowered circuit) |
| `precomputeSideSlots` (`pp_body`'s layout) | `Tests.lean`'s `pp_body` section — the only consumer, and not shipped |
| `precomputePhaseProductSlots` (reserve split) | `checkPhaseProductAt`/`checkCPhaseProductAt` across the width ladder **and both slack regimes** — the slack regime is what makes the top-chunk row of the split observable |
| `translateAnnotatedOps` (annotated-ops walk) | the same, plus `Tests.lean`'s `TopChunkReserve` anchors |

The widths and instances those checks use are not fixed: `ppWidthLadder`
and `qftWidthLadder` derive them from the table's own `nextWidth` chain, so
a table that recurses later is checked later. See `Reflect/Verify.lean`.

## Folder map

| folder | contents | see |
|---|---|---|
| `Json/` | JSON printers only — one spelling per value type, no proof obligations of their own (though `PlanJson.lean` walks proof-carrying plan terms). | [`Json/README.md`](Json/README.md) |
| `Table/` | The `(ops, points)` view of a `ShorLoweringSetup` the value tables read. (The `Decidable` instances that let a user discharge a table's side conditions live in `ShorVerification/Submission/Decide.lean`.) | [`Table/README.md`](Table/README.md) |
| `IR/` | The extracted-IR language (`Syntax.lean`), its JSON printer, decidable well-formedness, and the interpreter (`instantiate`/`instantiateGate`) — which is also the only definition of what the shipped `Doc` *means*. | [`IR/README.md`](IR/README.md) |
| `Reflect/` | The `MetaM` extractor (`Extract.lean`, `Targets.lean`, and `PolicyTargets.lean` for per-band bodies), the build-time/run-time drivers (`Driver.lean`), the run-time instance-check canary and single-table evaluation tier (`Verify.lean`), and the policy evaluation tier (`PolicyVerify.lean`). | [`Reflect/README.md`](Reflect/README.md) |
| `Symbolic/` | The opaque value tables (`CoeffPoly.lean`, `Width.lean`, `QftPlan.lean`, `ShorPlan.lean`), the built (not extracted) policy width dispatcher and its agreement theorem (`Dispatcher.lean`), plus the assembly file `Bundle.lean`. | [`Symbolic/README.md`](Symbolic/README.md) |
| `Lower/` | Concrete-width instances (`pp`/`cpp`/`qft`/`shor`), the `Decidable` instances that let the emitter discharge workspace preconditions on the fly, and shared register construction. | [`Lower/README.md`](Lower/README.md) |
| `Main.lean` | The `forshor_emit` executable: argument parsing and subcommand dispatch only — no logic of its own lives here, everything is a call into one of the folders above. | — |
| `Tests.lean` (`lean_lib EmitTests`) | Acceptance anchors: `native_decide` on the pure functions the folders above export, the extraction checks listed below, the `TopChunkReserve` regression tables and the `TableOracle` consumer check. | [below](#what-testslean-checks) |

Internal import order is mostly `Json → Table → IR → Reflect → Symbolic →
Lower → Main`, but not a strict per-folder layering: `Lower/Registers.lean`
(concrete register construction) has no proof/reflection dependencies of
its own, so `Reflect/Verify.lean` imports it directly rather than importing
back through `Lower/PhaseProduct.lean`/`Lower/Qft.lean` — which is exactly
what lets those two files import `Reflect/Verify.lean` in turn, for their
own `instantiate_eq_real` check, without an import cycle (see
`Lower/README.md`). `Tests` imports anything.

Outside `Emit/`, only `ShorVerification/Submission/` imports from here:
`Check.lean` and `PolicyCheck.lean` import `Reflect/Driver.lean`,
`Reflect/Verify.lean` (or `Reflect/PolicyVerify.lean`) and `IR/Json.lean`;
`Main.lean` and `PolicyMain.lean` import `Json/Common.lean`. Nothing in
`Implementation/` or `Framework/` imports anything here.

## What `Tests.lean` checks

Beyond `native_decide` checks on the pure JSON builders (`buildBundleCore`,
`buildSection`, `buildPhases`, the `coeff_poly` checks at `k = 2, 3, 5`),
the suite pins a `Doc` per table with `extract_ir_doc` at build time and
checks each template against the real term. "Equals" means
`instantiate`/`instantiateGate` of the extracted template, with `Env` built
from the real opaque functions, agrees with the real term after flattening.

| target | check |
|---|---|
| `pp_body`, `k = 2` standard | equals `compileOpsToSignedGate` for `x, z` of width 4 with enough reserve |
| `phase_product` | equals `standardSignedPhaseLoweringPlan` + `lowerGateRec` at `n = 8` (base case) and `n = 16` (recurses once) |
| `naive_leaf` | equals `Naive_SignedPhaseProd` at six `(xw, zw)` pairs covering widths 1..6 |
| `cphase_product`, `naive_cleaf` | as the two rows above, controlled |
| `qft` | equals `lowerQFT` at `w = 4` (two recursion levels) and `w = 8` (three) |
| `shor_gate`, `shor` | `shor_gate` equals `orderFindingApprox` as `Gate`; `shor` equals `Reference.referenceShorCircuit`, both at `k = 2, a = 2, N = 15, m = 0` |
| genericity | the `phase_product` and `qft` checks hold at `k = 3` standard and at a hand-built `k = 2` `ShorLoweringSetup` whose `ops` differ from the standard table's, with no code path keyed on either |
| `TopChunkReserve` | anchors for the top chunk's reserve capacity: tables whose last `phaseProduct` checkpoint sits on register `k - 1`, at widths where the top-chunk child recurses, in both slack regimes |
| `TableOracle` | a consumer holding only the bundle's published `width`/`split_width`/`qft_plan` rows (no call into `nextWidth`/`reserveNeed`/`qftWorkspaceNeed`) can instantiate `qft` at odd widths |
| comparison contract | `lowGateAgrees` is stack-safe on a deep adjoint and exactly as discriminating as a flat-list comparison |

## CLI reference

| command | prints |
|---|---|
| `forshor_emit template <k> [--w-max W]` | the extracted `Doc` alone, after `Doc.wellFormed` and the instance-check canary pass (refuses with exit 3 otherwise) |
| `forshor_emit bundle <k> [--m-max M] [--w-max W] [--check-cramer] [--no-template]` | `forshor.emit/v1`: the n-free document (`schedule, coeff_poly, width, split_width, qft_plan, shor_plan`, plus `template` unless `--no-template`) |
| `forshor_emit <schedule\|coeff_poly\|width\|split_width\|qft_plan\|shor_plan> <k> [same opts as bundle]` | one pure section of the above, in the same envelope |
| `forshor_emit phases <k> <m> <phiNum/phiDen>` | exactly `q k` plain-text lines, `c_l(2^m)·phi` as reduced `num/den` |
| `forshor_emit pp <k> <n> <phiNum/phiDen> [--flat]` | the signed phase product at width `n`: annotated (default, with embedded `meta.checks`) or flat `forshor.lowgate/v2` |
| `forshor_emit cpp <k> <n> <phiNum/phiDen> [--flat]` | same, controlled |
| `forshor_emit qft <k> <w> [--flat]` | same, for the QFT at width `w` |
| `forshor_emit shor <k> <a> <N> <m>` | the reference order-finding circuit, plus a `layout` block (`allocateReferenceLayout`'s registers) |
| `forshor_emit <k> <a> <N> <m>` | alias of `shor` |

Exit codes: `0` complete; `2` refused (bad input — nothing on stdout); `3`
internal check failed (a blocking check — the extracted `Doc`'s
well-formedness/instance-check canary, or `pp`/`cpp`/`qft`'s own
`instantiate_eq_real` check — failed; nothing usable on stdout). `n` never
appears on the `bundle`/per-section/`template` command lines (they are
n-free by construction).

`phi` is always given as an integer ratio `num/den` (`den` defaults to `1`
if omitted, e.g. `pp 2 8 1` for `phi = π`).

`template`/`bundle` (unless `--no-template`) load a fresh `Environment` via
`importModules` to run the extractor — this is the one place run time and
memory cost noticeably rises; `--no-template` skips it
entirely.

`--w-max` must reach at least the largest width the canary itself checks
(`Symbolic/Bundle.lean`'s `templateCheckWidth`, derived from the table's own
recursion ladder), or `template`/`bundle` refuses: otherwise the published
value tables would have a gap exactly where the check looked. The default
`64` covers `k = 2` and `k = 3`; larger `k` needs an explicit `--w-max`, and
the refusal says how much.

## Using a custom table

If what you want is to *submit* a table, you are in the wrong folder: copy
`ShorVerification/Submission/Template.lean`, edit its three definitions, and
run `lake build Submission && lake exe forshor_submission > ir.json`. That
path runs this folder's extractor for you, checks the result against the real
circuit at sampled widths, and prints the IR alongside the precision and
trial count a score needs. See
[`Submission/README.md`](../ShorVerification/Submission/README.md).

What follows is the lower-level entry point the template is built on, for
when you want the `Doc` and nothing else.

The run-time CLI (`template`/`bundle`) only ever extracts the standard
table — there is deliberately no way to name a table on the command line,
since a table's side-condition proofs need the kernel, not a parser. To
extract a table of your own, write it as a `Shor.ShorLoweringSetup` in a
Lean file that imports `FastMultiplication.Emit.Reflect.Driver`, and use the
build-time `extract_ir_doc` command:

```lean
def myTable : Shor.ShorLoweringSetup :=
  { k := 3, hk := by decide
    pts := Shor.genInterpolationPoints 3
    hpts := Shor.generatedInterpolationPoints_length 3
    good := Shor.genInterpolationPoints_good 3
    ops := myOps
    consumes := by decide +kernel   -- Submission/Decide.lean's instances make this work
    returns := by decide +kernel }

extract_ir_doc myDoc myTable
#eval IO.println (Shor.IR.docJson myDoc).compress
```

A table is the pair `(ops, pts)` plus four conditions on it: `hpts :
pts.length = q k`, `good : GoodToomCookPoints k pts hpts` (the points
interpolate a degree-`2k-2` polynomial), `consumes : ProgConsumesPtsSafe hk
State.start_state myOps pts` (running `myOps` from the start state, the
`i`-th `phaseProduct` checkpoint finds exactly `pts[i]`'s row, all points are
consumed, and no `addScaled` has `dst = src`), and `returns : run? myOps
State.start_state = some State.start_state`. All four are stated in
`Framework/ToomCookTable.lean` and all four are `Decidable` at a concrete
`k`/`ops`/`pts` (`ShorVerification/Submission/Decide.lean`), so `by decide
+kernel` closes them directly — no hand-written proof needed, the same as the
standard table's own `k`-generic proofs
(`genOpsWithProduct_ProgConsumesPtsSafe`/`_returns_to_original`) are for
`standardLoweringSetup`. Points of your own are fine; citing
`genInterpolationPoints_good` as above is just the shortcut when you reuse
the canonical ladder — for points of your own, `good :=
Shor.goodToomCookPoints_of_distinct hpts (by decide +kernel)` is the cheap
route (the `GoodToomCookPoints` determinant has `(2k-1)!` terms; pairwise
projective distinctness is equivalent to it and quadratic). A table that
cannot be packaged this way is, correctly, one the extractor refuses to
accept — see [Design rules](#design-rules).

## Build

```bash
lake build forshor_emit
lake build EmitTests          # the build-time acceptance suite; slow (tens of minutes)
lake exe forshor_emit template 2
lake exe forshor_emit bundle 2 --m-max 24 --w-max 96
lake exe forshor_emit shor 2 2 15 0
```

This folder's own `lakefile.lean` entries are `lean_exe forshor_emit` and
`lean_lib EmitTests`; it is not part of the default target, so a plain `lake
build` does not touch it. The `Submission` library and the
`forshor_submission` executable are separate targets that consume it.

## Known limitations

- **`coeff_poly`'s `M⁻¹`** is computed by exact Gauss-Jordan elimination
  over `ℚ` (`gaussJordanInverseRows`, `O(n³)`), not via Mathlib's
  `Matrix.adjugate`/`Matrix.det`. Those are Leibniz-formula sums over
  `Equiv.Perm`, meant for proofs: evaluating one adjugate entry is an `O(n!)`
  determinant, so a whole inverse that way is `O(n²·n!)` — impractical from
  `k = 5` on. The eliminator lives in the compiler
  (`ShorVerification/Implementation/PhaseProduct/Compiler/GaussJordan.lean`),
  because the compiler's own `cramerCoeffFromPts` is `@[csimp]`-compiled
  through it (`gjCoeffFromPts`, `Compiler/Coefficients.lean`): eliminate,
  re-multiply to verify `M · M⁻¹ = I`, fall back to Cramer if that fails, and
  a proof that the result equals Cramer's rule unconditionally. The kernel
  still sees Cramer; only compiled code — `native_decide`, the oracles here,
  the executables — runs the cubic path.
- **`check2`** (cross-checking the polynomials against
  `cramerCoeffFromPtsWidth`) runs unconditionally at every `k`, since both
  sides are cubic; `--check-cramer` is accepted and ignored, and the `m ≤ 6`
  cap stays only because nothing above it teaches anything new.
  `Tests.lean` runs it at `k = 5`.
- **Point *order* is part of a table, not a detail.** A table's
  `phaseProduct` checkpoints consume its points from the front, one per
  checkpoint, and leaf `l` receives coefficient `l` — so a permutation of
  the same point set is a different table. `ShorLoweringSetup.consumes` is
  the ordered statement, and `ShorVerification/Submission/Decide.lean`
  decides it.
- **`Reflect/Verify.lean`'s canary is a ladder, not an exhaustive scan**:
  `ppWidthLadder`/`qftWidthLadder` on the caller's own table — the largest
  base-case width plus the smallest widths reaching one, two and three levels
  of recursion — with each phase-product width run in two reserve regimes.
  Three levels and two regimes are what it takes to observe the top chunk's
  reserve capacity: it is visible only at a grandchild of the top-level call
  and only when the parent has slack to split. Exhaustive coverage across
  base and recursive cases at small widths is `Tests.lean`'s compile-time
  suite, and the extractor being keyed by Lean construct, never by `k`, is
  why agreement on the ladder generalizes. The ladder is derived from the
  table, so its cost is too: `k = 3` reaches `n = 35` and runs for roughly
  35 minutes, `k = 4` reaches `n = 87`. Whether to cap the ladder's depth is
  an open decision. The canary runs `shor_gate`/`shor` for *every* table
  reaching it (any `ShorLoweringSetup` is, by construction, one
  `Reference.allocateReferenceLayout`/`referenceShorCircuit` are proven to
  work over).
- **`shor --annotated` is not implemented.** `Lower/Shor.lean` always prints
  the `layout` block, but the `Gate`-tree-of-`orderFindingApprox` annotated
  view needs the raw pre-lowering `Gate` tree (which `referenceProgramAt`
  doesn't expose separately from its already-lowered `LowGate` result) plus
  a per-leaf workspace-discharge walk over `Gate.QFT`/`(C)SignedPhaseProd`/
  `CmpGeConst`/`CSubConst` — the last two needing a new
  `ConstArithmeticWorkspace` `Decidable` instance. Its own
  research-and-implementation arc, beyond what `pp`/`cpp`/`qft` cover.
- **The constant-arithmetic primitives `lowerCmpGeConst`/`lowerCSubConst`**
  (steps U3, U4 of `CmodMulInPlaceCore`) are not tabulated. They are linear
  in register width with no recursion and no table dependence, so their
  per-width counts are meant to be read off concrete `shor` documents and
  fitted outside Lean.
- **The workspace `Prop`s are decided, not proved, at the CLI.**
  `Lower/Decide.lean` is the only place in the repo with `Decidable`
  instances for `SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`/
  `QFTReserveOK`; the emitter discharges them with `if h : … then … else
  refuse` against a concrete width rather than proving them abstractly for
  all widths.
