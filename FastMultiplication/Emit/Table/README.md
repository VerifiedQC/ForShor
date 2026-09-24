# `Table/`

The Toom-Cook table a bundle is built from — `Source.lean` — plus
`Decide.lean`'s `Decidable` instances for packaging a custom table as a
`Shor.ShorLoweringSetup`.

`Census.lean` (the old op census / per-op-class `LowGate` resource table,
E1) was deleted in R3/R4 (`Emit/PLAN.md`): those counts now fall out of the
extracted `Doc` (`Reflect/`, `IR/`) plus the repository's own
`shorGateResourceModel`, rather than a separate hand-evaluated table.

**`SUBMISSION_PLAN.md` S1.6 retired `TableSource`.** R5 had already narrowed
it: the *extractor* (`Reflect/`) stopped taking one, so `.generate` — the
older `Table_Generation` tooling's table — was no longer a legitimate
extraction input, and survived only as a convenience for the *value tables*
(`Symbolic/{CoeffPoly,Width,QftPlan,ShorPlan}.lean` via `bundle`'s pure
sections), which make no fidelity claim. The reason it could never be more
than that was that the lowering chain hard-wired `genInterpolationPoints k`
into the *types* of the plan builders, so a second table's own points
described a circuit the real lowering did not build. S1.2/S1.3 removed that
hard-wiring — the points are a parameter now — which dissolves the
distinction rather than generalising it: a table *is* a `ShorLoweringSetup`
(`ops`, `pts`, and the four side conditions relating them), and a table that
cannot be packaged as one is not a table this emitter has anything to say
about. The inductive, the `--table` flag, `checkTable`'s run-time
re-derivation of what a `ShorLoweringSetup` already proves, and the
`.generate` path are all gone. A table of one's own now enters exactly one
way: as a `ShorLoweringSetup` in a Lean file, via `extract_ir_doc`
(`Reflect/Driver.lean`), with the four conditions discharged by
`Decide.lean`'s instances.

## `Source.lean`

The phase-product compiler is driven by a Toom-Cook table: an arithmetic
program `ops : Prog k` over `k` limb registers and a list of `q = 2k − 1`
interpolation points, consumed in order by the `phaseProduct` ops. Both
halves are fields of `Shor.ShorLoweringSetup`; this file is just the
read-only view of them the JSON value-table builders want.

- `TableInstance k` — `{ ops : Prog k, points : List Point, hlen :
  points.length = q k }`. The `hlen` field exists so downstream
  interpolation code (`Symbolic/CoeffPoly.lean`) never has to re-derive it.
  The `decl`/`srcFile` provenance strings went with `TableSource`: they
  recorded *which* source a instance came from, and nothing read them.
- `ShorLoweringSetup.tableInstance (setup) : TableInstance setup.k` — the
  projection. Total and proof-free: `setup.consumes`/`.returns`/`.good` are
  exactly the conditions `checkTable` used to re-run at run time, and they
  hold by construction.
- `standardTableInstance (k) (hk) : TableInstance k` —
  `Shor.standardLoweringSetup k hk`'s own, the table the lowering theorems
  are about and the only one the CLI builds.

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
