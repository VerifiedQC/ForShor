# `Emit/`

The `LowGate` emitter: prints the circuits this repository proves correct,
and an n-free ("symbolic") description of them a resource model can price,
as JSON. This folder is output-only tooling. Nothing in it is imported by
the verified core, and nothing under `ShorVerification/` was changed to
support it.

**New to this folder?** Read this file top to bottom once, then open each
subfolder's own `README.md` in the order `Json → Table → IR → Reflect →
Symbolic → Lower` (roughly the order the code imports in). Each sub-README
lists every file, what it defines, and how it's used by the rest of the
folder.

## Contents

- [What this tool prints](#what-this-tool-prints)
- [Three artifacts](#three-artifacts)
- [Decisions](#decisions)
- [What is and is not a theorem](#what-is-and-is-not-a-theorem)
- [R2 exit criteria (the test list)](#r2-exit-criteria-the-test-list)
- [Folder map](#folder-map)
- [CLI reference](#cli-reference)
- [Using a custom table](#using-a-custom-table)
- [Build](#build)
- [Known limitations and deviations from the original design](#known-limitations-and-deviations-from-the-original-design)

## What this tool prints

Three kinds of document, all JSON except `phases`:

- **`template <k>`**: the extracted, n-free symbolic IR — `pp_body`,
  `phase_product`/`naive_leaf`, `cphase_product`/`naive_cleaf`, `qft`,
  `shor_gate`, `shor` — obtained by *reflection* over the real, verified
  definitions (see [Three artifacts](#three-artifacts)), not hand-written.
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
   Lean (D3); a consumer (or `IR/Instantiate.lean`'s own `instantiate`)
   unrolls it at a concrete width. Nothing about a template's shape is
   written by hand: this is what replaced the old hand-transcribed
   `Symbolic/Template.lean`.
2. **The opaque value tables** (`Symbolic/{Width,QftPlan,ShorPlan,
   CoeffPoly}.lean`). A handful of functions the templates call by name but
   never evaluate symbolically (D4: `RecursivePhaseWorkspace.nextWidth`,
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

## Decisions

Confirmed with the owner (`Emit/PLAN.md` §1); these are the invariants the
extractor and its callers are built to:

| # | decision |
|---|---|
| D1 | **Run-time extraction.** `forshor_emit template <k>` loads the environment with `importModules` and runs the extractor on the standard table at `k`. No per-`k` line anywhere in this folder's own code; a build-time elaborator command (`extract_ir_doc`) exists to extract any `ShorLoweringSetup` (not just the standard one) and pin a `Doc` for `native_decide` tests. |
| D2 | **Genericity boundary.** The translation table is keyed by Lean *construct* (`Gate.seq`, `dite`, `Reg.interval`, `WellFounded.fix`, …), never by `k`, table, or width. A new `k` or table needs no code change. An unknown construct is a hard error naming the constant, never a silent drop. |
| D3 | **Recursion is not unrolled in Lean.** A recursive definition yields one template whose body is one activation; the recursive call is a `Node.call` with its argument expressions. The consumer (and the Lean-side `IR/Instantiate.lean`) unrolls at a concrete `n`. |
| D4 | **Opaque set.** Left unevaluated and tabulated: `nextWidth`, `reserveNeed`, `qftWorkspaceNeed`, `coeff(l, m)`, `Nat.log2`, `mod`, `pow`, `step5Constant`, `modpow`. |
| D5 | **Concrete table required, supplied through Lean as a `ShorLoweringSetup`** (amended by R5, §11 — originally `k` and `TableSource`; `TableSource` itself retired by `SUBMISSION_PLAN.md` S1.6). The input to the extractor is a `Shor.ShorLoweringSetup` value: `k`, `hk`, `ops`, its own interpolation points `pts`, and the four proofs (`hpts`/`good`/`consumes`/`returns`) the lowering theorems need. A table that can be packaged as one is, by definition, a table those theorems cover; a table that cannot be is not a table this emitter has anything to say about, which is why there is no longer a second "table source" of any kind — see `Table/README.md`. Symbolic: `n, m, a, N` (Shor), `W, phi, x, z` (phase product), `w, r` (QFT). |
| D6 | **Reference instances stay.** `pp`, `cpp`, `qft`, `shor` and their annotated views remain; they are what the extracted IR is checked against. |
| D7 | **Not a theorem.** Trusted: the translation table and Lean's normaliser. Checked: `instantiate`/`instantiateGate` unrolls the extracted `Doc` at concrete widths and agrees with the real term — at build time (`Tests.lean`'s R2.1–R2.7 `native_decide` suite, §6) and at run time (`Reflect/Verify.lean`'s canary, run before `template`/`bundle` ever print anything). The provenance strings say exactly this. |

## What is and is not a theorem

- The flat circuits printed by `pp`, `cpp`, `qft`, `shor` are the terms
  `lowerSignedPhaseProdWithWorkspace`, `lowerCSignedPhaseProdWithWorkspace`,
  `lowerQFT`, `referenceProgramAt` evaluate to. Their correctness is
  `Shor.lowerSignedPhaseProduct_correct`, `Shor.lowerQFT_correct`,
  `Shor.lowerGate_correctness`, `Shor.Shor_correct` (the last at
  `m = referenceChosenPrecision N`, which the emitter cannot compute).
- The annotated trees (`pp`/`cpp`/`qft`) are printed from the plan terms
  those functions consume; `annotated_eq_flat` checks the two agree by
  evaluation.
- **The extracted templates are not theorems.** They are checked against
  the real term by evaluation (D7): `instantiate_eq_real` on `pp`/`cpp`/
  `qft` re-runs the check at whatever width the caller asked for;
  `Reflect/Verify.lean`'s canary re-runs it at a representative width for
  whatever `(k, src)` `template`/`bundle` was asked to extract, before
  either prints anything; `Tests.lean`'s R2.1–R2.7 suite established it
  exhaustively (base case and one recursive level, `k = 2, 3`, both table
  sources) once, at build time, via `native_decide`.
- The opaque value tables (E2's `coeff_poly`, `width`, `qft_plan`,
  `shor_plan`) are the named functions evaluated directly — not
  recomputed, not re-derived. `coeff_poly`'s own Gauss-Jordan `M⁻¹` is the
  one genuinely re-derived quantity, and it is cross-checked against the
  pre-existing `cramerCoeffFromPtsWidth` by evaluation
  (`cramerCoeffFromPtsWidth = phaseCoeffFromPtsWidth` is itself the theorem
  `cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth`).
- Cost-model numbers, where printed (`Table/README.md`'s op census), are
  `shorGateResourceModel` evaluated, not proved bounds; the asymptotic
  statement they evaluate is `phaseProductGateCountBound_of_programOK` /
  `exists_shorGateCountBound`.
- The constant-arithmetic step costs (`lowerCmpGeConst`/`lowerCSubConst`,
  steps U3/U4 of `CmodMulInPlaceCore`) are fitted from concrete `shor`
  emissions outside Lean, not tabulated.

## R2 exit criteria (the test list)

Each row was one extraction step (`Emit/PLAN.md` §6); "equals" means
`instantiate`/`instantiateGate` of the extracted template, with `Env` built
from the real opaque functions, agrees with the real term after flattening.
Each is a `native_decide` example in `Tests.lean`.

| step | target | exit criterion |
|---|---|---|
| R2.1 | `pp_body`, `k = 2` standard | equals `compileOpsToSignedGate` for `x, z` of width 4 with enough reserve |
| R2.2 | `phase_product` | equals `standardSignedPhaseLoweringPlan` + `lowerGateRec` at `n = 8` (base case) and `n = 16` (recurses once) |
| R2.3 | `naive_leaf` | equals `Naive_SignedPhaseProd` at six `(xw, zw)` pairs covering widths 1..6 |
| R2.4 | `cphase_product`, `naive_cleaf` | as R2.2/R2.3, controlled |
| R2.5 | `qft` | equals `lowerQFT` at `w = 4` (two recursion levels) and `w = 8` (three) |
| R2.6 | `shor_gate`, `shor` | `shor_gate` equals `orderFindingApprox` as `Gate`; `shor` equals `Reference.referenceShorCircuit`, both at `k = 2, a = 2, N = 15, m = 0` |
| R2.7 | genericity | R2.2/R2.5 criteria hold at `k = 3` standard and at a hand-built `k = 2` `ShorLoweringSetup` whose `ops` differ from the standard table's (§11.3), with **no code change** to `Reflect/Extract.lean` or `Reflect/Targets.lean` |

## Folder map

| folder | contents | see |
|---|---|---|
| `Json/` | JSON printers only — one spelling per value type, no proof obligations of their own (though `PlanJson.lean` walks proof-carrying plan terms). | [`Json/README.md`](Json/README.md) |
| `Table/` | The `(ops, points)` view of a `ShorLoweringSetup` the value tables read, plus `Decidable` instances (`Decide.lean`) that let a user discharge a custom table's `ShorLoweringSetup` proofs with `by decide`/`by native_decide`. | [`Table/README.md`](Table/README.md) |
| `IR/` | The extracted-IR language (`Syntax.lean`), its JSON printer, decidable well-formedness, and the interpreter (`instantiate`/`instantiateGate`). | — |
| `Reflect/` | The `MetaM` extractor (`Extract.lean`, `Targets.lean`), the build-time/run-time drivers (`Driver.lean`), and the run-time instance-check canary (`Verify.lean`). | — |
| `Symbolic/` | The opaque value tables (`CoeffPoly.lean`, `Width.lean`, `QftPlan.lean`, `ShorPlan.lean`) plus the assembly file `Bundle.lean`. | [`Symbolic/README.md`](Symbolic/README.md) |
| `Lower/` | Concrete-width instances (`pp`/`cpp`/`qft`/`shor`), the `Decidable` instances that let the emitter discharge workspace preconditions on the fly, and shared register construction. | [`Lower/README.md`](Lower/README.md) |
| `Main.lean` | The `forshor_emit` executable: argument parsing and subcommand dispatch only — no logic of its own lives here, everything is a call into one of the folders above. | — |
| `Tests.lean` (`lean_lib EmitTests`) | Acceptance anchors: `native_decide` on the pure functions the folders above export, plus R2.1–R2.7's extraction exit criteria. | — |

Internal import order is mostly `Json → Table → IR → Reflect → Symbolic →
Lower → Main`, but not a strict per-folder layering: `Lower/Registers.lean`
(concrete register construction) has no proof/reflection dependencies of
its own, so `Reflect/Verify.lean` imports it directly rather than importing
back through `Lower/PhaseProduct.lean`/`Lower/Qft.lean` — which is exactly
what lets those two files import `Reflect/Verify.lean` in turn, for their
own `instantiate_eq_real` check, without an import cycle (see
`Lower/README.md`). `Tests` imports anything. No module here is imported
from outside `Emit/`.

## CLI reference

| command | prints |
|---|---|
| `forshor_emit template <k> [--w-max W]` | the extracted `Doc` alone, after `Doc.wellFormed` and the R2-style instance-check canary pass (refuses with exit 3 otherwise) |
| `forshor_emit bundle <k> [--m-max M] [--w-max W] [--check-cramer] [--no-template]` | `forshor.emit/v1`: the n-free document (`schedule, coeff_poly, width, qft_plan, shor_plan`, plus `template` unless `--no-template`) |
| `forshor_emit <schedule\|coeff_poly\|width\|qft_plan\|shor_plan> <k> [same opts as bundle]` | one pure section of the above, in the same envelope |
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
memory cost noticeably rises (`Emit/PLAN.md` §9); `--no-template` skips it
entirely.

## Using a custom table

The run-time CLI (`template`/`bundle`) only ever extracts the standard
table — there is deliberately no way to name a table on the command line,
since a table's side-condition proofs need the kernel, not a parser. To
extract a table of your own, write it as a `Shor.ShorLoweringSetup` in a
Lean file that imports `FastMultiplication.Emit.Reflect.Driver`, and use
the build-time `extract_ir_doc` command:

```lean
def myTable : Shor.ShorLoweringSetup :=
  { k := 3, hk := by decide
    pts := Shor.genInterpolationPoints 3
    hpts := Shor.generatedInterpolationPoints_length 3
    good := Shor.genInterpolationPoints_good 3
    ops := myOps
    consumes := by native_decide   -- Table/Decide.lean's instances make this work
    returns := by native_decide }

extract_ir_doc myDoc myTable
#eval IO.println (Shor.IR.docJson myDoc).compress
```

`SUBMISSION_PLAN.md` S1 made the interpolation points `pts` submission data
rather than a constant baked into the plan builders' types, so a table is
now the pair `(ops, pts)` plus four conditions on it: `hpts : pts.length =
q k`, `good : GoodToomCookPoints k pts hpts` (the points interpolate a
degree-`2k-2` polynomial), `consumes : ProgConsumesPtsSafe hk
State.start_state myOps pts` (running `myOps` from the start state, the
`i`-th `phaseProduct` checkpoint finds exactly `pts[i]`'s row, all points
are consumed, and no `addScaled` has `dst = src`), and `returns : run?
myOps State.start_state = some State.start_state`.

`consumes` and `returns` are `Decidable` at a concrete `k`/`ops`/`pts`
(`Table/Decide.lean`'s instances for `ProgConsumesPts`/`SafeProg`), so `by
decide`/`by native_decide` closes them directly — no hand-written proof
needed, the same as the standard table's own `k`-generic proofs
(`genOpsWithProduct_ProgConsumesPtsSafe`/`_returns_to_original`) are for
`standardLoweringSetup`. `good` does not have a `Decidable` instance yet
(`SUBMISSION_PLAN.md` S2.1 adds one, via the interpolation matrix's
determinant); until then, points of your own need their own invertibility
proof, and reusing the canonical ladder as above lets you cite
`genInterpolationPoints_good` instead. A table that cannot be packaged this
way is, correctly, one the extractor refuses to accept — see D5.

## Build

```bash
lake build forshor_emit
lake build EmitTests
lake exe forshor_emit template 2
lake exe forshor_emit bundle 2 --m-max 24 --w-max 96
lake exe forshor_emit shor 2 2 15 0
```

The only edits outside this folder are two `lakefile.lean` entries
(`lean_exe forshor_emit`, `lean_lib EmitTests`). `FastMultiplication.lean` is
not changed; the emitter builds via its own targets.

## Known limitations and deviations from the original design

- **E2's `M⁻¹`** (`Symbolic/CoeffPoly.lean`) is computed by exact Gauss-Jordan
  elimination over `ℚ` (`gaussJordanInverseRows`, `O(n³)`), not via Mathlib's
  `Matrix.adjugate`/`Matrix.det`. Those are Leibniz-formula sums over
  `Equiv.Perm`, meant for proofs: evaluating one adjugate entry is an `O(n!)`
  determinant, so a whole inverse that way is `O(n²·n!)` — impractical from
  `k = 5` on.
- **`check2`** (cross-checking the polynomials against the pre-existing
  `cramerCoeffFromPtsWidth`) is gated tightly: unconditional for `k ≤ 3`,
  opt-in via `--check-cramer` for `k = 4`, always skipped from `k = 5` up,
  capped at `m ≤ 6` even when it runs. At `k = 5`, evaluating
  `Matrix.det`'s generic `Equiv.Perm` construction overflows the stack almost
  immediately — a recursion-depth limit in Mathlib's machinery, confirmed
  with the OS stack limit raised, not merely slow.
- **Point *order* is part of a table, not a detail.** A table's
  `phaseProduct` checkpoints consume its points from the front, one per
  checkpoint, and leaf `l` receives coefficient `l` — so a permutation of
  the same point set is a different table. (This bit the retired `generate`
  source: its `k = 2, 3` precomputed programs consume the canonical points
  in their own order, and pairing them with the plain `(List.range (q
  k)).map streamPoint` enumeration made the ordered-coverage check fail at
  `k = 3`.) `ShorLoweringSetup.consumes` is the ordered statement, and
  `Table/Decide.lean` decides it.
- **`Reflect/Verify.lean`'s canary is representative, not exhaustive**: one
  width per template (`4 * k`), not a scan over every base/recursive
  combination for the caller's own table. Exhaustive coverage across base
  and recursive cases is what `Tests.lean`'s R2.1–R2.7 compile-time suite
  already established, and D2 (the extractor is keyed by Lean construct,
  never by `k`) is why agreement at one representative width generalizes.
  Since R5 (§11), the canary runs `shor_gate`/`shor` for *every* table
  reaching it (any `ShorLoweringSetup` is, by construction, one
  `Reference.allocateReferenceLayout`/`referenceShorCircuit` are proven to
  work over) — it is no longer `.standard`-only the way it was before D5's
  amendment.
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
- **No `Decidable` instance for the workspace `Prop`s existed anywhere in
  the repo** before `Lower/Decide.lean` (needed so the emitter can discharge
  `SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`/`QFTReserveOK`
  with `if h : … then … else refuse` against a concrete width, rather than
  proving them abstractly for all widths).
