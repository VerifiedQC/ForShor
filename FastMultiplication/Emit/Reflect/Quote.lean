import Lean
import FastMultiplication.Emit.Table.Source

/-!
# Quoting a concrete table

`Extract.lean`'s "Specialise" step needs to splice a `ShorLoweringSetup`'s
concrete `ops : Prog k` — computed with compiled code, at run time — into an
`Expr`, so that the compiler's `match ops with …` collapses under `whnf`.
`Lean.toExpr` (needing `ToExpr (Prog k)`, i.e. `ToExpr (List
(Operations.valid_ops k))`) does exactly that. `ToExpr Operations.Point` is
here for the same reason on the other half of a table: `Targets.lean`'s
`setupPtsExprs` quotes `setup.pts` as a literal (`SUBMISSION_PLAN.md`
S1.6).

Neither `Operations.Point` nor `Operations.valid_ops k` is self-recursive
(no field of either is a `List` of itself — contrast `IR/Syntax.lean`'s
`WExpr`/`Node`), so `deriving instance ToExpr` for them is not subject to
that deriving-handler limitation; both derive cleanly. `ToExpr (Prog k)`
then falls out for free from Lean core's own `ToExpr (List α)` instance —
nothing further is needed here for it. `ToExpr (Fin k)` (both types index
their field-level positions/registers with `Fin k`) is also already a core
instance.
-/

deriving instance Lean.ToExpr for Operations.Point
deriving instance Lean.ToExpr for Operations.valid_ops
