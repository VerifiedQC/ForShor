# `Table/`

The Toom-Cook table abstraction (`standard` vs. `generate`) — `Source.lean`
— plus `Decide.lean`'s `Decidable` instances for packaging a custom table
as a `Shor.ShorLoweringSetup`.

`Census.lean` (the old op census / per-op-class `LowGate` resource table,
E1) was deleted in R3/R4 (`Emit/PLAN.md`): those counts now fall out of the
extracted `Doc` (`Reflect/`, `IR/`) plus the repository's own
`shorGateResourceModel`, rather than a separate hand-evaluated table.

**R5 (`Emit/PLAN.md` §11) narrowed what `TableSource`/`tableInstance` are
for.** The *extractor* (`Reflect/`) no longer takes a `TableSource` at all
— it takes a `Shor.ShorLoweringSetup` directly (D5), so `.generate` is no
longer a legitimate extraction input (it has no such value: `.generate`'s
own points don't match what `StandardPhaseLoweringPlan`'s fixed
`genInterpolationPoints k` coefficients assume). `TableSource` remains
useful for the *value tables* (`Symbolic/{CoeffPoly,Width,QftPlan,
ShorPlan}.lean` via `bundle`'s pure sections), which make no such fidelity
claim and are happy to evaluate on either table.

## `Source.lean`

The phase-product compiler is driven by a Toom-Cook table: an arithmetic
program `ops : Prog k` over `k` limb registers and a list of `q = 2k − 1`
interpolation points, consumed in order by the `phaseProduct` ops. **Two
table sources exist in the repository and they are not the same object:**

| source | ops | points | covered by the proofs |
|---|---|---|---|
| `standard` (default) | `genOpsWithProduct k (genInterpolationPoints k)` via `Shor.standardLoweringSetup` | `alternatingPoint`: `0, −1, 1, −2, 2, …` | yes: `ShorLoweringSetup.consumes` / `.returns` are theorems |
| `generate` | `Table_Generation.generate .PhaseProduct k` (precomputed at `k = 2, 3`; parity generator `k ≥ 4`) | `generatePointsInOrder .PhaseProduct k` (the order the precomputed/generated program actually consumes — **not** the naive `streamPoint` enumeration; see below) | no: checked at run time only |

`standard` is the default because it's the table the lowering theorems
(`ShorLoweringSetup`) are about. `generate` is kept for comparison with
tables emitted by older tooling.

- `TableSource` — `inductive | standard | generate`.
- `TableInstance k` — `{ ops : Prog k, points : List Point, hlen :
  points.length = q k, decl : String, srcFile : String }`. The `hlen` field
  exists so downstream interpolation code (`Symbolic/CoeffPoly.lean`) never
  has to re-derive it.
- `tableInstance (src) (k) (hk) : TableInstance k` — resolves a
  `TableSource` at arity `k`. For `.generate`, `points` is built from
  `Table_Generation.generatePointsInOrder`, not a plain `(List.range (q
  k)).map streamPoint` enumeration: the `k = 2, 3` precomputed programs
  consume the canonical points in their own order (a permutation of
  `streamPoint`'s enumeration — `ValidPointOrder`/`generatePointsInOrder_valid`
  in the repo), which is what the `phaseProduct` checkpoints actually see.
  Using the naive enumeration instead made the ordered-coverage check below
  fail at `k = 3` (only `k ≥ 4`'s parity generator is provably in
  `streamPoint` order).
- `progConsumesPtsCheck (hk) : State k → Prog k → List Point → Bool` — a
  computable, ordered mirror of the repo's own `ProgConsumesPts`: walks
  `ops` left to right, consuming `pts` from the *front* at each
  `phaseProduct` checkpoint. This is deliberately stricter than the
  existing `phaseCoverageFrom?`/`List.eraseFirstMatch?` checker (which
  accepts a match anywhere in the remaining point list) — it requires each
  `phaseProduct i` to match exactly the *next* point.
- `checkTable (src) (k) (hk) (inst) : Except String Unit` — the blocking
  check. For `standard`, always `.ok ()`: `genOpsWithProduct_ProgConsumesPtsSafe`
  and `genOpsWithProduct_returns_to_original` are compile-time theorems, so
  there's nothing to recompute. For `generate`, actually runs three checks
  at run time and refuses (`.error`) on any mismatch: `phaseProductCount ops
  = q k`, `run? ops State.start_state = some State.start_state`, and
  `progConsumesPtsCheck`.

## `Decide.lean`

`Decidable` instances for a user's own `Shor.ShorLoweringSetup` proofs
(`Emit/PLAN.md` §11.2 point 5): neither `ProgConsumesPts` nor `SafeProg`
had one anywhere in the repo before this file, so proving `consumes` for a
hand-built table meant writing an abstract proof by hand — exactly the
friction R5's whole point (any table the theorems cover, not just the
standard one) would otherwise run into.

- `decideProgConsumesPts`/`instance decidableProgConsumesPts` — term-mode,
  mirroring `ProgConsumesPts`'s own recursion on `ops` constructor by
  constructor (`phaseProduct i`'s existential witness is `pts`'s own head;
  every other op's is whatever `applyOp?` computes) rather than via a
  separately-proven Boolean mirror — `ProgConsumesPts` is a `def`, not an
  `inductive`, so its own internal `match op with …` only reduces once `op`
  is a literal constructor, which is why `decideProgConsumesPtsOther`
  (the shared "non-`phaseProduct`" case) takes its unfolding proof as an
  argument (`Iff.rfl`, defeq-provable only at each concrete call site)
  rather than proving it once generically.
- `safeProgCheck`, `safeProg_iff_check`, `instance decidableSafeProg` —
  `SafeProg ops` (a `∀` over list decompositions: every `addScaled d s _ _`
  anywhere in `ops` has `d ≠ s`) is equivalent to one Boolean scan over
  `ops` (`List.mem_iff_append` in one direction, `List.mem_append_right`/
  `List.mem_cons_self` in the other), and *that* is directly decidable.
- `instance decidableProgConsumesPtsSafe` — the pair, since
  `ShorLoweringSetup.consumes : ProgConsumesPtsSafe …` bundles both fields
  and callers want to write `consumes := by native_decide` once, not
  `⟨by native_decide, by native_decide⟩`.
