# `Table/`

The Toom-Cook table a bundle is built from: the `(ops, points)` view of a
`Shor.ShorLoweringSetup` that the JSON value-table builders read.

`Census.lean` (the old op census / per-op-class `LowGate` resource table,
E1) was deleted in R3/R4 (see `Emit/README.md`'s round history): those counts now fall out of the
extracted `Doc` (`Reflect/`, `IR/`) plus the repository's own
`shorGateResourceModel`, rather than a separate hand-evaluated table.

**There is one kind of table.** A table *is* a `Shor.ShorLoweringSetup`:
`ops`, `pts`, and the four side conditions relating them. Anything that
cannot be packaged as one is not a table this emitter has anything to say
about, so there is no table-source selector, no `--table` flag, and no
run-time re-derivation of conditions the record already proves.

A table of one's own enters exactly one way: as a `ShorLoweringSetup` in a
Lean file, via `extract_ir_doc` (`Reflect/Driver.lean`), with the four
conditions discharged by `Submission/Decide.lean`'s instances.

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

The `Decidable` instances a submitter discharges a table's four side
conditions with are not here: they need nothing from `Emit/`, so they live in
`ShorVerification/Submission/Decide.lean`, which imports
`Framework/ToomCookTable.lean` and Mathlib and nothing else.
