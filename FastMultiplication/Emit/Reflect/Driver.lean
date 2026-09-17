import Lean
import FastMultiplication.Emit.Reflect.Targets

/-!
# The extractor: `ToExpr`, and the build-time/run-time drivers

`IR/Syntax.lean`'s deriving note deferred `ToExpr` to this file: `WExpr`
(`opaque`'s `List WExpr`) and `Node` (`seq`'s `List Node`) are the two types
with a self-referential `List` field, and Lean's `deriving ToExpr` handler
rejects that shape exactly like `DecidableEq`/`LawfulBEq` did in R0. The fix
is the same shape as core's own `ToExpr (List α)` instance
(`List.toExprAux`): a *manual*, plain recursive function pairing the type's
own `toExpr` with a `List`-of-itself `toExpr`, so the recursion is ordinary
structural recursion the equation compiler handles directly, never
typeclass-resolution asking for `ToExpr (List WExpr)` while `ToExpr WExpr`
is still being defined. Every other IR type (`AExpr`, `RegExpr`, `Prop'`,
`Template`, `Doc`) has no such self-reference — once `ToExpr WExpr`/`ToExpr
Node` exist as real instances, `deriving instance ToExpr` on the rest just
works, since core's generic `ToExpr (List α)`/`ToExpr (Option α)` apply
uninhibited to a `List RegExpr`, `List Template`, `Option AExpr`, etc.
-/

namespace Shor.Reflect

open Lean Shor.IR

mutual
partial def wexprToExpr : WExpr → Expr
  | .var name => mkApp (mkConst ``WExpr.var) (toExpr name)
  | .lit n => mkApp (mkConst ``WExpr.lit) (toExpr n)
  | .add a b => mkApp2 (mkConst ``WExpr.add) (wexprToExpr a) (wexprToExpr b)
  | .sub a b => mkApp2 (mkConst ``WExpr.sub) (wexprToExpr a) (wexprToExpr b)
  | .mul a b => mkApp2 (mkConst ``WExpr.mul) (wexprToExpr a) (wexprToExpr b)
  | .div a b => mkApp2 (mkConst ``WExpr.div) (wexprToExpr a) (wexprToExpr b)
  | .max a b => mkApp2 (mkConst ``WExpr.max) (wexprToExpr a) (wexprToExpr b)
  | .min a b => mkApp2 (mkConst ``WExpr.min) (wexprToExpr a) (wexprToExpr b)
  | .opaque fn args => mkApp2 (mkConst ``WExpr.opaque) (toExpr fn) (wexprListToExpr args)

partial def wexprListToExpr : List WExpr → Expr
  | [] => mkApp (mkConst ``List.nil [.zero]) (mkConst ``WExpr)
  | a :: as => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``WExpr) (wexprToExpr a)
      (wexprListToExpr as)
end

instance : ToExpr WExpr where
  toExpr := wexprToExpr
  toTypeExpr := mkConst ``WExpr

deriving instance ToExpr for AExpr
deriving instance ToExpr for RegExpr
deriving instance ToExpr for Prop'

mutual
partial def nodeToExpr : Node → Expr
  | .op name regs nats angle flags =>
      mkAppN (mkConst ``Node.op)
        #[toExpr name, toExpr regs, toExpr nats, toExpr angle, toExpr flags]
  | .seq body => mkApp (mkConst ``Node.seq) (nodeListToExpr body)
  | .adj body => mkApp (mkConst ``Node.adj) (nodeToExpr body)
  | .cond guard ifTrue ifFalse =>
      mkApp3 (mkConst ``Node.cond) (toExpr guard) (nodeToExpr ifTrue) (nodeToExpr ifFalse)
  | .call template wArgs aArgs rArgs =>
      mkApp4 (mkConst ``Node.call) (toExpr template) (toExpr wArgs) (toExpr aArgs) (toExpr rArgs)
  | .loop var lo hi body =>
      mkApp4 (mkConst ``Node.loop) (toExpr var) (toExpr lo) (toExpr hi) (nodeToExpr body)

partial def nodeListToExpr : List Node → Expr
  | [] => mkApp (mkConst ``List.nil [.zero]) (mkConst ``Node)
  | a :: as => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Node) (nodeToExpr a)
      (nodeListToExpr as)
end

instance : ToExpr Node where
  toExpr := nodeToExpr
  toTypeExpr := mkConst ``Node

deriving instance ToExpr for Template
deriving instance ToExpr for Doc

/-- The one-template `Doc` this file's extractors can currently build:
`pp_body` alone (R2.2+ adds more targets to the same `Doc`). -/
def buildDoc (k : Nat) (hk : 1 < k) (src : Shor.TableSource) : MetaM IR.Doc := do
  let t ← extractPPBody k hk src
  pure { templates := [t], opaqueFns := [("nextWidth", 2)], entry := t.name }

open Lean Elab Command in
/-- Build-time command (`PLAN.md` §5.4): run the extractor at concrete `k`
(standard table) and splice the resulting `Doc` in as `def <id> : IR.Doc :=
…`, so `Tests.lean` can `native_decide` against a pinned value instead of
re-running `MetaM` reflection inside a proof. `--table generate` is not
wired into the surface syntax yet (`.standard` only) — R2.7 is what actually
needs it. -/
elab "extract_ir_doc " id:ident k:num : command => do
  let kVal := k.getNat
  if h : 1 < kVal then
    let docStx ← liftTermElabM do
      let doc ← buildDoc kVal h .standard
      PrettyPrinter.delab (toExpr doc)
    elabCommand (← `(def $id : Shor.IR.Doc := $docStx))
  else
    throwError "extract_ir_doc: k = {kVal} must be > 1"

end Shor.Reflect
