import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup

/-!
# The Toom-Cook table a bundle is built from

`SUBMISSION_PLAN.md` S1.6 retired `TableSource`. Until S1 the interpolation
points were not a parameter — the lowering chain hard-wired
`genInterpolationPoints k` into the *types* of the plan builders, so a second
table with points of its own (`Table_Generation.generate`, the older
table-generation tooling) could never be more than a value-table curiosity:
it had no `ShorLoweringSetup`, hence no `consumes`/`returns` theorem, hence
nothing the emitter's extraction path was allowed to touch, and
`--table generate` was refused by everything downstream of the pure value
sections. S1 made `pts` submission data, which removes the distinction at its
root: a table *is* a `ShorLoweringSetup` (its `ops`, its `pts`, and the four
side conditions relating them), and anything that cannot be packaged as one
is not a table this emitter has anything to say about. So the inductive, the
`--table` flag, `checkTable`'s run-time re-derivation of what a
`ShorLoweringSetup` already proves, and the `.generate` value-table path are
all gone; `TableInstance` survives as the read-only `(ops, points, hlen)`
projection the JSON value-table builders (`Symbolic/Bundle.lean`) consume.
-/

namespace Shor

open Operations

/-- A concrete `Prog k` / interpolation-point-list pair: the part of a
`ShorLoweringSetup` the `n`-free value tables actually read. `hlen` lets
downstream interpolation code (`Symbolic/CoeffPoly.lean`) consume `points`
without re-deriving its length. -/
structure TableInstance (k : ℕ) where
  ops : Prog k
  points : List Point
  hlen : points.length = q k

/-- The table a `ShorLoweringSetup` carries. Total, and proof-free: S1 made
`pts` a field of the setup, so there is nothing left to resolve or to check
here — `setup.consumes`/`setup.returns`/`setup.good` are exactly the
conditions that used to be re-run at run time by `checkTable`, and they hold
by construction of the setup. -/
def ShorLoweringSetup.tableInstance (setup : ShorLoweringSetup) : TableInstance setup.k :=
  { ops := setup.ops, points := setup.pts, hlen := setup.hpts }

/-- The standard table at arity `k`: `standardLoweringSetup`'s own. -/
def standardTableInstance (k : ℕ) (hk : 1 < k) : TableInstance k :=
  (standardLoweringSetup k hk).tableInstance

end Shor
