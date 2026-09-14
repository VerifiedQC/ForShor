# `Table_Generation/Builders/`

Reusable program-fragment builders — the constant-adder and row-building
blocks that concrete generators (in `Programs/` and `Generator/`) are
assembled out of — together with their correctness lemmas.

## `Fragments.lean`

- **`shiftsOfAux`, `shiftsOf`** — decompose a natural number into the list of
  bit positions where its binary representation has a `1`.
- **`signedPow2Decomp`** — signed power-of-two decomposition of an integer
  `c`: a list of `(neg, shift)` pairs whose signed powers of two sum to `c`.
- **`nonzeroFins`** — all register indices except `0` (`finZero`).
- **`pairToOp`** — turns one `(neg, shift)` pair into an
  `addScaled dst src` operation.
- **`computeLocal`** — fold-based builder: accumulates into register `0` the
  full local-row contribution of point value `z` from every other register,
  with no uncompute.
- **`addConstAux`, `addConstFrom`** — a recursive (non-fold) constant-adder:
  emits `dst += c·src` as a sequence of `addScaled` ops via the binary
  decomposition of `c`.
- **`computeLocalAux`, `computeLocal2`** — the recursive reformulation of
  `computeLocal`, built directly from `addConstFrom` (proved equal to
  `computeLocal` elsewhere in this file).
- **`pointDst`** — the destination register for a point: `finZero` for
  `.int`, `finLast` for `.frac`.
- **`nonlastFins`** — all register indices except the last (`finLast`).
- **`fracCoeff`** — the coefficient of `x_j` in the scaled row for `1/c`,
  i.e. `c^(k-1-j)`.
- **`computeFracLocalAux`, `computeFracLocal2`** — recursive builder analogous
  to `computeLocal2`, but building the fractional-point row into the last
  register.
- **`opsForPointWithProduct`** — the per-point program fragment: build the
  row, emit one `phaseProduct` checkpoint, then run the inverse of the build
  to uncompute (the `.frac 0` case needs no build at all).
- **`genOpsWithProduct`** — concatenates `opsForPointWithProduct` over a
  whole list of points.
- **`rowMatchesProp`** — the Prop-level (decidable) version of "this register
  equals the expected row for this point".
- **`showFin`, `opToString`, `joinComma`, `progToString`, `pointToString`,
  `opsForPointString`, `genOpsString`** — pretty-printers rendering registers,
  single ops, points, and whole programs as strings (for `#eval`-style
  inspection).
- **`AllNe`** — a register index differs from every entry of a list; used to
  state that a builder's source registers never collide with its
  destination.

## `FragmentLemmas.lean`

Correctness lemmas for the builders in `Fragments.lean`. It shows that
`computeLocal`/`computeLocal2` and `computeFracLocal2` always run
successfully and never touch `PhaseProductCoverage`'s point list (i.e. they
are pure arithmetic, coverage-neutral, and — combined with `RunLemmas.lean` —
`NoPhase`), and it computes their exact algebraic effect: after running from
`start_state`, the destination register holds precisely the expected
interpolation row. Along the way it introduces a few small helper
definitions used only to state and drive these proofs — `Block` (one
source's contribution as a program), `wsum`/`wsum1` and `contrib`/
`contribFrom`/`fracContrib` (the corresponding numeric/register-valued sums),
and the relational big-step semantics `ExecCL`, `ExecCL_start`, and
`ExecAddConstAux` (inductive alternatives to reasoning about `run?`
equations directly).
