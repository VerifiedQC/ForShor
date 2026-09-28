import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup

/-!
# The Toom-Cook table a bundle is built from

A table is a `Shor.ShorLoweringSetup`: an arithmetic program `ops`, the
interpolation points `pts` its `phaseProduct` checkpoints consume, and the
four side conditions relating them. There is no other kind, and nothing that
cannot be packaged as one is a table this emitter has anything to say about.

`TableInstance` is the read-only `(ops, points, hlen)` projection of that
record which the JSON value-table builders (`Symbolic/Bundle.lean`) consume;
they need the data but none of the proofs.
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
