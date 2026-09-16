# `Table/`

The Toom-Cook table abstraction (`standard` vs. `generate`), and E1, the op
census.

Import order: `Source.lean → Census.lean`.

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

## `Census.lean`

E1: op census, and the `LowGate` resources this repository assigns to the
adder-class ops and the naive leaf, at a chosen width `W`.

- `OpCensus` — counts of `phaseProduct`, `addScaled`, `negate`, `shiftL`,
  `shiftR`; `.adderClassTotal := addScaled + negate`.
- `opCensus {k} (ops : Prog k) : OpCensus` — census a `Prog k`.
- `synthReg (n : ℕ) : ExtReg` — a width-only synthetic register (`Reg.interval
  0 n`, no reserve) used to evaluate width-indexed resource functions
  without needing a real layout. Mirrors the `private` `widthShell` pattern
  in `Reference/ReferenceLayout.lean` — that one isn't visible outside its
  file, so this is `Emit/`'s own copy.
- `addScaledResourcesAt`, `negateResourcesAt`, `radixReverseResourcesAt (W :
  ℕ) : GateResources` — the Cuccaro-adder-based resource formulas from
  `Framework/Gatecount/ResourceModel.lean`, evaluated at `synthReg W`.
- `naiveLeafResourcesAt (wx wz : ℕ) : GateResources` — the exact gate census
  of `LowGate.Naive_SignedPhaseProd`, counted on the real term at operand
  widths `(wx, wz)` (the angle is irrelevant to gate counts, so it's fixed
  to `0`).
