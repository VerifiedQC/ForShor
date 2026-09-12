# `Table_Generation/Generator/`

The parity-reset generator: a general-`k` table generator built around
reusable "carrier register" bookkeeping so that a symmetric pair of points
(`+x`, `-x`) can share almost all of their build work, plus hardcoded
programs for the small `k = 2, 3` cases where the general construction
doesn't apply, and the correctness proof tying it all together.

## `Defs.lean`

- **`streamPoint`** — deterministic function generating the `n`-th point of
  the canonical interpolation-point stream `0, ∞, 1, -1, 2, -2, 1/2, -1/2, …`.
- **`generatedPoints`** — the first `mode.pointCount k` points of
  `streamPoint`, for a given product `mode` and register count `k`.
- **`PointPairType`** — inductive: whether a parity-block point is on the
  `integer` or `fraction` side.
- **`twoPowInt`** — `2^e` as an integer.
- **`pairKindOfIndex`, `pairExponentOfIndex`** — decode a pair index `i` into
  its `PointPairType` and exponent.
- **`parityDegree`** — the polynomial degree register `j` contributes for a
  given point type (`j` itself for integer points, `k-1-j` for fraction
  points).
- **`evenCarrier`, `oddCarrier`** — the fixed register indices used to
  accumulate even- and odd-degree contributions for a point type (requires
  `k ≥ 4`).
- **`carrierAdds`** — builds one carrier register's contents by adding in
  every other register whose contribution has matching parity/degree.
- **`combineParityCarriers`** — turns separate even/odd carrier registers
  `E`, `O` into `E - O` and `E + O` in 3 ops, so both a point and its
  negation can be read off the same build.
- **`generateParityInitialBlock`** — the dense initial block handling
  `0, ∞, 1, -1` together (`k ≥ 4`).
- **`generateParityPairBlock`** — one parity-reset block handling a `±x`
  symmetric pair of points at a given exponent.
- **`generateParitySingletonBlock`** — handles one leftover, unpaired point
  directly via `opsForPointWithProduct`.
- **`generateParityPairBlocks`** — concatenates `generateParityPairBlock`
  over the required number of pairs.
- **`generateParityForMode`, `generateParityProduct`,
  `generateParityTripleProduct`** — assemble the full `k ≥ 4` parity-reset
  generator (initial block, then pair blocks, then an optional singleton)
  for a given/each product mode.
- **`generate`** — the top-level entry point: dispatches to the hardcoded
  `PrecomputedTables` programs for `k = 2, 3`, and to the parity generator
  otherwise.
- **`generatePointsInOrder`** — the matching entry point giving the exact
  order in which `generate`'s program consumes its points.
- **`generateParityLayerSizesForMode`, `generateLayerSizes`** — the sizes of
  each "parallel layer" of simultaneous `phaseProduct` checkpoints that
  `generate` emits.

## `WellFormed.lean`

Proves `Prog.WellFormed` (and the related `SafeProg`) for every builder in
`Defs.lean` — `carrierAdds`, `combineParityCarriers`,
`generateParityInitialBlock`, `generateParityPairBlock`,
`generateParitySingletonBlock`, `generateParityPairBlocks`, and
`generateParityForMode` — by structural composition from the corresponding
facts about `addConstFrom` and `opsForPointWithProduct`.

## `Precomputed.lean`

Four namespaces — **`PrecomputedTables.K2Product`**, **`K3Product`**,
**`K2TripleProduct`**, **`K3TripleProduct`** — each hand-written for its `k`
and product mode, giving `targetPoints` (the points the program must cover),
`orderedPoints` (the order the program actually consumes them in),
`program` (the literal `Prog k` instruction list), and `layerSizes`
(parallel-layer sizes). These are hardcoded escape hatches for `k = 2, 3`,
where the general parity generator (which needs `k ≥ 4`) does not apply.

## `Spec.lean`

- **`ProductMode`** — inductive: `PhaseProduct` or `PhaseTripleProduct`, the
  two supported generation targets.
- **`ProductMode.pointCount`** — the number of interpolation points a mode
  needs for a given `k` (`2k-1`, resp. `3k-2`).
- **`canonicalPoint`, `canonicalPoints`** — the specification-level
  interpolation-point stream and its first `pointCount` points (independent
  of, but shown equal to, `streamPoint`/`generatedPoints`).
- **`IsSignedPowerOfTwo`, `AllowedPoint`** — a point's numeric part must be
  `0` or `±2^n`.
- **`ValidPointList`** — a point list is literally equal to
  `canonicalPoints`.
- **`ValidPointOrder`** — a point list is some permutation of
  `canonicalPoints`.

## `Metrics.lean`

- **`arithmeticOperationCount`** — number of non-`phaseProduct` ops in a
  program.
- **`phaseProductCount`** — number of `phaseProduct` ops in a program.
- **`parallelPhaseProductLayerCountAux`, `parallelPhaseProductLayerCount`** —
  number of maximal runs ("layers") of consecutive `phaseProduct` ops, i.e.
  how many rounds of simultaneous phase products the program needs.

## `Examples.lean`

- **`ProductMode.toString`, `pointsToString`, `joinNewline`,
  `progToLinesString`, `generatedPointsString`,
  `generatePointsInOrderString`, `generateString`,
  `generateMetricsString`** — string-rendering helpers for inspecting a
  generated program, its point list, and its metrics via `#eval`.
- **`ExampleK`, `ExampleProductMode`** — the concrete `k` and mode this
  file's `#eval` demonstrations use.

## `Correctness.lean`

Proves the two headline theorems about `generate`/`generatePointsInOrder`:
`generatedPoints_valid` and `generate_ProgConsumesPtsSafe` establish that the
generated program (for every `k ≥ 2` and every `ProductMode`) is well-formed,
safely consumes exactly a permutation of the canonical point list, and
returns every register to `start_state`, while `generate_parallelProductLayerCount_eq`
computes the exact number of parallel `phaseProduct` layers the program
uses. Reaching those results requires an extended argument about the
`generateParity*` construction in `Defs.lean`: it tracks how `carrierAdds`
and `combineParityCarriers` populate each carrier register from
`start_state`, matches the resulting rows against the expected point rows,
and relates the parity-block point order back to the `streamPoint`
enumeration. The file introduces a handful of small definitions in service of
that argument (`carrierTerm`, `carrierContribFrom`, `carrierAddsList`,
`parityCarrierRow`, `positivePointOfPair`, `negativePointOfPair`,
`pairBlockPoints`, `pairBlocksList`) that restate pieces of `Defs.lean`'s
constructions in a form more convenient to induct on.
