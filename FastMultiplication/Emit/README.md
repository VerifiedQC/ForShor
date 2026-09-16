# `Emit/`

The `LowGate` emitter: prints the circuits this repository proves correct,
and an n-free ("symbolic") description of them a resource model can price,
as JSON. This folder is output-only tooling. Nothing in it is imported by
the verified core, and nothing under `ShorVerification/` was changed to
support it.

**New to this folder?** Read this file top to bottom once, then open each
subfolder's own `README.md` in the order `Json → Table → Symbolic → Lower`
(the same order the code imports in). Each sub-README lists every file, what
it defines, and how it's used by the rest of the folder.

## Contents

- [What this tool prints](#what-this-tool-prints)
- [Key concepts](#key-concepts)
- [How the pieces fit together](#how-the-pieces-fit-together)
- [Folder map](#folder-map)
- [CLI reference](#cli-reference)
- [Build](#build)
- [Design principles](#design-principles)
- [Known limitations and deviations from the original design](#known-limitations-and-deviations-from-the-original-design)
- [What is and is not a theorem](#what-is-and-is-not-a-theorem)

## What this tool prints

Three kinds of document, all JSON except `phases`:

- **`bundle`** (and its per-section commands): an **n-free** document — every
  number in it is a function of `k` (the Toom-Cook table arity) alone, never
  of a modulus bit-length `n`. It's what a resource-estimation model reads to
  price the algorithm at a width it hasn't been asked to instantiate yet.
- **`pp` / `cpp` / `qft`**: a **concrete-width instance** — the real,
  verified `LowGate` circuit for one signed (or controlled) phase product or
  QFT at a width you choose, either flat (`--flat`) or annotated with the
  recursion structure (the default).
- **`shor`**: the concrete reference order-finding circuit for one Shor
  instance `(k, a, N, m)` — what `Shor.Shor_correct` is a theorem about.

## Key concepts

The single biggest thing to understand before reading any file here is the
difference between four representations of "a circuit", each used at a
different point in the pipeline:

| representation | what it is | where it lives |
|---|---|---|
| `Gate` | The abstract op tree `orderFindingApprox` is built from: `QFT`, `SignedPhaseProd`, `CSignedPhaseProd`, `CmpGeConst`, `CSubConst`, and structural/primitive constructors. Phase products and QFTs are still atomic nodes here. | `ShorVerification/Framework/AbstractMachine/Gates.lean` |
| `LowGate` | The fully lowered, flat circuit: every `Gate` leaf has been expanded (`lowerGate`) down to `H`/`X`/`CNOT`/`Toffoli`/`Phase`/register ops. This is what actually gets executed, and what the correctness theorems (`Shor.Shor_correct`, etc.) are about. Nothing marks where a phase product began — it's just nested `seq` blocks of adder ops around clusters of `Phase`/`CNOT`. | `ShorVerification/Framework/AbstractMachine/LowGate.lean` |
| `PhaseLoweringPlan` / `QFTLoweringPlan` | A `Type`-valued inductive that carries the *same* term as `LowGate`, but keeps the recursion visible: a `signedStep`/`cSignedStep` node still has its layout, coefficients, and child plan attached, instead of having already been flattened away. `lowerGateRec`/`lowerQFTPlan` erase a plan down to its `LowGate`. | `ShorVerification/Implementation/PhaseProduct/Lowering/Plan.lean`, `.../QFT/Lowering/Plan.lean` |
| Template (`WExpr`) | A **symbolic** IR: the same op sequence as a plan, but with the width left as a variable `W` and slot widths/allocations printed as small typed expressions instead of numbers. This is the only one of the four that is n-free. | `Symbolic/Template.lean` |

`Json/PlanJson.lean` prints the plan (annotated); `Json/LowGateJson.lean`
prints the `LowGate` (flat); `Symbolic/Template.lean` prints the template
(symbolic). `Lower/Instantiate.lean` checks that all three agree at a
concrete checked width.

Two other concepts recur throughout:

- **Table.** The phase-product compiler is driven by a Toom-Cook table: an
  arithmetic program `ops : Prog k` over `k` limb registers plus a list of
  `q = 2k − 1` interpolation points, consumed in order by `phaseProduct` ops.
  Two sources exist and are **not the same object** — see `Table/README.md`.
- **`k` vs. `n`.** `k` is the table arity (small, fixed per invocation, e.g.
  2–6). `n`/`w` is an operand or register width (can be large). The symbolic
  `bundle` document is a function of `k` only; instances (`pp`/`cpp`/`qft`)
  and `shor` additionally take a concrete `n`/`w`.

## How the pieces fit together

`referenceProgramAt lowering m inst` is the term `Shor.Shor_correct` is about
(at `m = referenceChosenPrecision N`, a noncomputable `Nat.find`, so the
emitter takes `m` as an explicit argument instead). It is a composition, and
each `bundle` section attaches to one function on the chain:

```
referenceProgramAt lowering m inst
= referenceShorProg → referenceShorCircuit
    allocateReferenceLayout ops inst m              E5  referenceXWidth, referenceDataWidth,
                                                         referenceWorkWidth m, referenceScratchWidth,
                                                         referenceWorkspaceNeed → reserve sizes
    orderFindingApproxLow = lowerGate (orderFindingApprox …)
      orderFindingApprox : Gate                     the Shor template: shape is n-free
        = H_reg x ;; initY1 y ;; modExpApproxValid ;; adj (QFT x)
          modExpApproxValid = one CmodMulInPlaceCore per exponent bit e, multiplier (a^(2^e)) mod N
            CmodMulInPlaceCore = U1 ;; U2 ;; U3 ;; U4 ;; U5
              U1, U5 : H_reg ;; CSignedPhaseProd ;; adj QFT
              U2     : QFT ;; SignedPhaseProd ;; adj QFT
              U3, U4 : CmpGeConst, CSubConst
      lowerGate erases each Gate leaf:
        Gate.QFT r             → lowerQFT                       E4  splitM, qftPhi, qftWorkspaceNeed
        Gate.SignedPhaseProd   → lowerSignedPhaseProdWithWorkspace
                                 = lowerGateRec (standardSignedPhaseLoweringPlan …)
                                                                E7  template; E1 table; E2 angles;
                                                                E3 nextWidth; E6 ladder
        Gate.CSignedPhaseProd  → controlled variant of the same
        Gate.CmpGeConst, CSubConst → lowerCmpGeConst, lowerCSubConst   linear primitives, see E5
```

The `E1`–`E7` labels are cross-references into `Symbolic/`: `E1` = op census
(`Table/Census.lean`), `E2` = coefficient polynomials, `E3` = width tables,
`E4` = QFT plan, `E5` = Shor register plan, `E6` = recursion skeleton, `E7` =
the templates. They're used throughout the code comments and this doc as
short names for "the section of the `bundle` document that answers this
question" — see `Symbolic/README.md` for the full mapping.

## Folder map

| folder | contents | see |
|---|---|---|
| `Json/` | JSON printers only — one spelling per value type, no proof obligations of their own (though `PlanJson.lean` walks proof-carrying plan terms). | [`Json/README.md`](Json/README.md) |
| `Table/` | The Toom-Cook table abstraction (`standard` vs `generate`) and the E1 op census. | [`Table/README.md`](Table/README.md) |
| `Symbolic/` | The n-free `bundle` document: E2–E7 plus the assembly file `Bundle.lean`. | [`Symbolic/README.md`](Symbolic/README.md) |
| `Lower/` | Concrete-width instances (`pp`/`cpp`/`qft`/`shor`), the `Decidable` instances that let the emitter discharge workspace preconditions on the fly, and the instantiation checks tying plan/flat/template together. | [`Lower/README.md`](Lower/README.md) |
| `Main.lean` | The `forshor_emit` executable: argument parsing and subcommand dispatch only — no logic of its own lives here, everything is a call into one of the four folders above. | — |
| `Tests.lean` (`lean_lib EmitTests`) | Acceptance anchors, mostly `native_decide`/`#guard` on the functions the folders above export. | — |

Internal import order: `Json → Table → Symbolic → Lower → Main`, with
`Tests` importing anything. No module here is imported from outside `Emit/`.

## CLI reference

| command | prints |
|---|---|
| `forshor_emit bundle <k> [--table standard\|generate] [--m-max M] [--w-max W] [--check-cramer]` | `forshor.emit/v1`: the whole n-free document (`schedule, coeff_poly, width, qft_plan, shor_plan, recursion, template`) |
| `forshor_emit <schedule\|coeff_poly\|width\|qft_plan\|shor_plan\|recursion\|template> <k> [same opts as bundle]` | one section of the above, in the same envelope |
| `forshor_emit phases <k> <m> <phiNum/phiDen>` | exactly `q k` plain-text lines, `c_l(2^m)·phi` as reduced `num/den` |
| `forshor_emit pp <k> <n> <phiNum/phiDen> [--flat]` | the signed phase product at width `n`: annotated (default, with embedded `meta.checks`) or flat `forshor.lowgate/v2` |
| `forshor_emit cpp <k> <n> <phiNum/phiDen> [--flat]` | same, controlled |
| `forshor_emit qft <k> <w> [--flat]` | same, for the QFT at width `w` |
| `forshor_emit shor <k> <a> <N> <m>` | the reference order-finding circuit, plus a `layout` block (`allocateReferenceLayout`'s registers) |
| `forshor_emit <k> <a> <N> <m>` | alias of `shor` |

Exit codes: `0` complete; `2` refused (bad input — nothing on stdout); `3`
internal check failed (a blocking check — `checkTable`, or an
instantiation check on `pp`/`cpp`/`qft` — failed; nothing usable on
stdout). `n` never appears on the `bundle`/per-section command lines (they
are n-free by construction).

`phi` is always given as an integer ratio `num/den` (`den` defaults to `1`
if omitted, e.g. `pp 2 8 1` for `phi = π`).

## Build

```bash
lake build forshor_emit
lake build EmitTests
lake exe forshor_emit bundle 2 --m-max 24 --w-max 96
lake exe forshor_emit shor 2 2 15 0
```

The only edits outside this folder are two `lakefile.lean` entries
(`lean_exe forshor_emit`, `lean_lib EmitTests`). `FastMultiplication.lean` is
not changed; the emitter builds via its own targets.

## Design principles

1. **Computable by construction, no mirrors.** `Angle` is `ℚ`, and every
   function from `Shor.Reference.referenceProgramAt` down to
   `LowGate.Naive_SignedPhaseProd` is a plain `def`. The emitter calls those
   definitions directly, so a printed circuit *is* the verified term. There
   is no `AGate`/`ALowGate` copy of the gate languages and no fidelity
   theorem to maintain.
2. **`k` enters; `n` never does** in the symbolic bundle. Every quantity that
   depends on the operand width is printed either as an expression in a width
   variable, as a rule evaluated from the compiler's own width functions, or
   as a table over a width ladder from which a closed form can be read off.
3. **Three artifacts, one family.** The *template* (E7) is the IR proper:
   the ops with the width left symbolic. The *tables* (E1–E6) supply the
   values of the few functions the template references that have no closed
   form. The *instances* (`pp`, `qft`, `shor` at concrete widths) are the
   verified terms evaluated, and exist to check the template against them.
4. **Every substituted computation is gated by a repo-owned check.** Where
   the emitter recomputes something (interpolation weights as polynomials,
   the template's op sequence), it re-verifies the result against the
   corresponding definition in `ShorVerification/` by evaluation and refuses
   to print on mismatch.
5. **The document says what is and is not a theorem.** Provenance strings
   name the Lean declaration each section evaluates. Cost-model numbers are
   labelled as the model evaluated, not as proved bounds.
6. **One spelling per JSON object.** Registers, angles, points, ops, and
   resources have a single printer each, in `Json/Common.lean`.

## Known limitations and deviations from the original design

These were found necessary or unavoidable while building the folder; each is
also called out where it's relevant in the sub-READMEs.

- **E2's `M⁻¹`** (`Symbolic/CoeffPoly.lean`) is computed by exact Gauss-Jordan
  elimination over `ℚ` (`gaussJordanInverseRows`, `O(n³)`), not via Mathlib's
  `Matrix.adjugate`/`Matrix.det`. Those are Leibniz-formula sums over
  `Equiv.Perm`, meant for proofs: evaluating one adjugate entry is an `O(n!)`
  determinant, so a whole inverse that way is `O(n²·n!)` — impractical from
  `k = 5` on.
- **E2's `check2`** (cross-checking the polynomials against the pre-existing
  `cramerCoeffFromPtsWidth`) is gated tightly: unconditional for `k ≤ 3`,
  opt-in via `--check-cramer` for `k = 4`, always skipped from `k = 5` up,
  capped at `m ≤ 6` even when it runs. At `k = 5`, evaluating
  `Matrix.det`'s generic `Equiv.Perm` construction overflows the stack almost
  immediately — a recursion-depth limit in Mathlib's machinery, confirmed
  with the OS stack limit raised, not merely slow. `cramerCoeffFromPtsWidth`
  itself is not modified, so this can't be sped up the way E2's own `M⁻¹`
  computation was.
- **`Table/Source.lean`'s `generate` table uses `generatePointsInOrder`, not
  a naive `streamPoint` enumeration.** The `k = 2, 3` precomputed tables
  consume interpolation points in their own order; using the plain
  `(List.range (q k)).map streamPoint` sequence instead (which is only
  provably equal to the real order for `k ≥ 4`) made the ordered-coverage
  blocking check fail at `k = 3`.
- **Instantiation checks are one level, not multi-level byte-for-byte**
  (`Lower/Instantiate.lean`). Fully replaying the template recursively and
  reproducing physical qubit assignment via `PhaseSplitLayout.ofBudget`
  would be a new sub-system, not a check. What's implemented instead, at one
  level of a checked concrete width: width formulas match the real
  compiler's numbers, and op-*kind* sequences match (a phase-product node
  normalizes to one canonical tag on both sides, since the template's
  `child` interpolation-point index has no counterpart on the real plan's
  node, which carries all `q k` coefficients rather than one selected
  index).
- **`shor --annotated` is not implemented.** `Lower/Shor.lean` always prints
  the `layout` block, but the `Gate`-tree-of-`orderFindingApprox` annotated
  view needs the raw pre-lowering `Gate` tree (which `referenceProgramAt`
  doesn't expose separately from its already-lowered `LowGate` result) plus
  a per-leaf workspace-discharge walk over `Gate.QFT`/`(C)SignedPhaseProd`/
  `CmpGeConst`/`CSubConst` — the last two needing a new
  `ConstArithmeticWorkspace` `Decidable` instance. Its own
  research-and-implementation arc, beyond what `pp`/`cpp`/`qft` cover.
- **The constant-arithmetic primitives `lowerCmpGeConst`/`lowerCSubConst`**
  (steps U3, U4 of `CmodMulInPlaceCore`) are not tabulated in E5. They are
  linear in register width with no recursion and no table dependence, so
  their per-width counts are meant to be read off concrete `shor` documents
  and fitted outside Lean.
- **No `Decidable` instance for the workspace `Prop`s existed anywhere in
  the repo** before `Lower/Decide.lean` (needed so the emitter can discharge
  `SignedRecursiveWorkspaceOK`/`CSignedRecursiveWorkspaceOK`/`QFTReserveOK`
  with `if h : … then … else refuse` against a concrete width, rather than
  proving them abstractly for all widths).
- **The `Emit/Symbolic/Template.lean` phase-product template's allocation
  order follows the real compiled term**, which interleaves allocations by
  slot index (`x0, z0, x1, z1, …`), not grouped by side (`x0, x1, z0, z1`) —
  a distinction worth knowing if you're comparing the template's JSON
  against hand-written expectations.

## What is and is not a theorem

- The flat circuits printed by `pp`, `cpp`, `qft`, `shor` are the terms
  `lowerSignedPhaseProdWithWorkspace`, `lowerCSignedPhaseProdWithWorkspace`,
  `lowerQFT`, `referenceProgramAt` evaluate to. Their correctness is
  `Shor.lowerSignedPhaseProduct_correct`, `Shor.lowerQFT_correct`,
  `Shor.lowerGate_correctness`, `Shor.Shor_correct` (the last at
  `m = referenceChosenPrecision N`, which the emitter cannot compute).
- The annotated trees are printed from the plan terms those functions
  consume; annotated = flat is checked by evaluation (`Lower/Instantiate.lean`,
  check 1).
- The E7 templates are checked against the annotated trees by evaluation at
  the checked widths, one recursion level at a time (check 2) — not the
  multi-level byte-for-byte replay first planned. They are not themselves
  theorems.
- The E2 polynomials agree with `cramerCoeffFromPtsWidth` at the checked `m`
  by evaluation, and `cramerCoeffFromPtsWidth = phaseCoeffFromPtsWidth` is
  the theorem `cramerCoeffFromPtsWidth_eq_phaseCoeffFromPtsWidth`.
- The E3/E6 ladders are the compiler's own `nextWidth` iterated; the leaf
  count `q^depth` is checked against the real circuit (check 3).
- The E6 cost numbers are `shorGateCostModel` evaluated. Asymptotic bounds
  are `phaseProductGateCountBound_of_programOK` and
  `exists_shorGateCountBound`; the numbers instantiate the model, they do
  not prove the bound.
- The constant-arithmetic step costs are fitted from concrete emissions
  outside Lean.
- Affine tails and degenerate-`m` lists are detected numerically and are
  advisory.
