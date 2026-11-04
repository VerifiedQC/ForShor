# `Table_Generation/`

Top of the table-generation subsystem: synthesizes and certifies concrete
"table generator" programs — symbolic register/arithmetic programs built from
shifts, negation, scaled-add, and "phase product" leaves — that are checked to
(a) return every register to its starting state and (b) consume a required
list of interpolation points in the structural pattern captured by
`PhaseProductCoverage`/`ProgConsumesPts`. The subtree splits into `Core/`
(the op language, symbolic state, coverage framework, and proof tactics),
`Builders/` (reusable program-fragment builders), `Programs/` (a concrete
generator and its certification), and `Generator/` (the parity-reset
generator, precomputed small-`k` cases, and their correctness proof) — each
with its own README.

## `Examples.lean`

Certifies the example programs declared in `Core/Tactics.lean`
(`example_prog_2`, `example_prog_3`): proves each returns its own start state
and satisfies phase-product coverage against its target point list, using the
`prove_coverage`/`returns_to_original?` tactics. It also records a handful of
state-update helper lemmas (how `setReg`, `shiftLReg`, `negateReg`, and
`addScaledReg` behave on register indices other than the one they touch, plus
an identity relating a negate/shift/add pipeline to a single signed
`addScaled`) that are reused by later synthesis proofs.

## `Generator.lean`

Two-line umbrella that re-exports `Generator/Metrics.lean` and
`Generator/Correctness.lean`.
