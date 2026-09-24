import Lean
import FastMultiplication.Emit.Reflect.Targets
import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup

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

/-- The `Doc` this file's extractors can currently build: `pp_body`,
`phase_product`/`naive_leaf`, `cphase_product`/`naive_cleaf` (each pair
needed together — a phase-product template's base case is a `Node.call` to
its `naive_*leaf` counterpart, so a `Doc` with one but not the other is
never `wellFormed`), and `qft` (which itself `Node.call`s `phase_product`
at each split, so needs it in the same `Doc` too). `entry` stays `pp_body`
for backwards compatibility with `extract_ir_doc`'s existing callers
(`Tests.lean`'s R2.1 section); callers that want `phase_product`/
`cphase_product`/`qft` name it explicitly to `instantiate`.

`Emit/PLAN.md` R5: takes any `Shor.ShorLoweringSetup`, not a `(k, hk, table
source)` triple — D5's amendment. `setup` is a table the lowering theorems
actually cover *by construction* (its four side conditions are exactly those
theorems' hypotheses), so there is no second kind of table to special-case
or reject here: an invalid one simply cannot be packaged as a
`ShorLoweringSetup` in the first place. `SUBMISSION_PLAN.md` S1.6 retired
the `TableSource` inductive that used to be the alternative. -/
def buildDoc (setup : Shor.ShorLoweringSetup) : MetaM IR.Doc := do
  let pp ← extractPPBody setup
  let pp2 ← extractPhaseProductBody setup
  let cpp2 ← extractCPhaseProductBody setup
  let qft ← extractQFTBody setup
  let shorGate ← extractShorGateBody
  let shor ← extractShorBody setup
  pure
    { templates := [pp, pp2, cpp2, qft, shorGate, shor, naiveLeafTemplate, naiveCLeafTemplate]
      opaqueFns := [("nextWidth", 2), ("reserveNeed_x", 2), ("reserveNeed_z", 2),
        ("qftXWork", 1), ("qftZWork", 1), ("log2", 1), ("mod", 2), ("pow", 2),
        ("step5Const", 2), ("modpow", 3)]
      entry := pp.name }

-- `extract_ir_doc <id> <setupIdent>` (`Emit/PLAN.md` §11.2 point 2):
-- `setupIdent` names a `Shor.ShorLoweringSetup` declaration in scope (the
-- *value*, not a numeral — this replaces the old `<id> <k>`/`<id> (<k>,
-- generate)` numeric forms, both removed: with the table itself carrying its
-- own points and coverage proofs, there is nothing left for a table-source
-- argument to select between). Resolved with `resolveGlobalConstNoOverload`, then
-- *evaluated* — not reflected over — with `Lean.Meta.evalExpr`: unlike `k`,
-- which is quoted into an `Expr` `buildDoc`'s callees reflect over,
-- `setupIdent`'s value only needs to be read out to a plain `ShorLoweringSetup`
-- so `extract*Body` can call `.k`/`.hk`/`.ops` on it directly (`evalExpr`
-- compiles and runs the constant the same way `native_decide` does, hence
-- `unsafe`).
--
-- Splices the resulting `Doc` in as `def <id> : IR.Doc := …`, so `Tests.lean`
-- can `native_decide` against a pinned value instead of re-running `MetaM`
-- reflection inside a proof. Registers the declaration directly
-- (`addDecl`/`compileDecl` on the already-computed `Expr`) rather than
-- `PrettyPrinter.delab`-ing it into surface syntax and re-elaborating that via
-- `elabCommand`: `phase_product`'s `Doc` is large enough (thousands of nested
-- `WExpr`/`Node` constructors) that delab starts eliding subterms as
-- unreconstructable placeholders, which then fail to re-elaborate (`buildDoc`
-- grew from `pp_body` alone once R2.2 added `phase_product` + `naive_leaf` to
-- it — confirmed empirically: this is exactly where the delab round-trip
-- stopped scaling). Going straight from the `Expr` `buildDoc` already produced
-- to a declaration sidesteps the surface syntax step entirely.
--
-- `elabExtractIrDocImpl` is `unsafe` (it calls `Lean.Meta.evalExpr`); the
-- `elab` command itself stays a plain, safely-typed `CommandElabM Unit`
-- action by calling it through the term-level `unsafe <expr>` escape (the
-- same pattern Aesop's own config elaborators use,
-- `Aesop/Frontend/Tactic.lean`'s `elabOptions`) rather than needing the
-- whole command elaborator marked `unsafe` (which the `elab` syntax does
-- not accept directly).
open Lean Elab Command in
unsafe def elabExtractIrDocImpl (id : Ident) (setupIdent : Ident) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let declName := ns ++ id.getId
  let setupName ← resolveGlobalConstNoOverload setupIdent
  liftTermElabM do
    let setupTyE := mkConst ``Shor.ShorLoweringSetup
    let setup ← Lean.Meta.evalExpr Shor.ShorLoweringSetup setupTyE (mkConst setupName)
    let doc ← buildDoc setup
    let decl := Declaration.defnDecl
      { name := declName, levelParams := [], type := mkConst ``Shor.IR.Doc
        value := toExpr doc, hints := .regular 0, safety := .safe }
    addDecl decl
    compileDecl decl

open Lean Elab Command in
elab "extract_ir_doc " id:ident setupIdent:ident : command =>
  unsafe elabExtractIrDocImpl id setupIdent

/-- Run-time entry point (`PLAN.md` §5.4): `lake exe forshor_emit`'s own
process has `FastMultiplication.Emit.Reflect.Targets` compiled in already
(it's an ordinary `import`), but not as a first-class `Environment` value
`MetaM` can reflect over — that's exactly what `importModules` builds.
`lake exe` supplies the search path (`initSearchPath`/`findSysroot` resolve
it the same way the `lean` binary itself does), so this needs no extra
configuration at the call site.

`importModules` defaults `loadExts := false` — every environment extension
(the instance-resolution registry among them) then keeps its *initial*
value instead of the imported one, which broke typeclass search for
something as basic as `LT Nat` the first time this ran. Fix, per
`importModules`'s own doc comment: `loadExts := true`, which needs
`enableInitializersExecution` called first — unlike the `lean` binary
itself, a plain `lake exe` process never calls it automatically, hence
`unsafe` here (and up through every caller): running arbitrary
`initialize`-block code from imported modules is exactly what makes this
operation unsafe in the type-theoretic sense (not "will crash", but "the
kernel takes it on faith"), same as `native_decide`.

Every `MetaM`/`CoreM` error (an `unrecognised construct …`, say) is caught
and reported as `Except.error`, never an uncaught `IO` exception.

`Emit/PLAN.md` §11.2 point 4: the run-time CLI (`template`/`bundle`) only
ever extracts the standard table — `standardLoweringSetup k h`, built here
as an ordinary (non-reflected) function call, exactly as it always was
before R5's `ShorLoweringSetup` refactor just moved one level up. A custom
table is a build-time-only path (`extract_ir_doc` above, named in a Lean
file the user writes and compiles); there is deliberately no way to hand
`runExtract` an arbitrary `ShorLoweringSetup` from the command line. -/
unsafe def runExtract (k : Nat) : IO (Except String IR.Doc) := do
  if h : 1 < k then
    try
      enableInitializersExecution
      initSearchPath (← findSysroot)
      let env ← importModules #[{module := `FastMultiplication.Emit.Reflect.Targets}] {}
        (trustLevel := 0) (loadExts := true)
      -- `buildDoc`'s heaviest targets (`shor_gate`/`shor`) needed
      -- `set_option maxHeartbeats 4000000` at *build* time
      -- (`Tests.lean`'s `extract_ir_doc` calls) — that `set_option` is local
      -- to the command elaborator's own context and does not carry over to
      -- this freshly-built `Core.Context`, so without an explicit override
      -- here the same computation hits Lean's plain default (200000) and
      -- fails with a deterministic `whnf` timeout at run time. `0` disables
      -- the limit entirely: unlike the pinned `k` values `Tests.lean`
      -- checks, a run-time `template`/`bundle` request can be any `k`, so
      -- there is no single finite bound to pick instead.
      let coreCtx : Core.Context :=
        { fileName := "<extract_ir>", fileMap := FileMap.ofString "", maxHeartbeats := 0 }
      let coreState : Core.State := { env := env }
      let (doc, _) ← ((buildDoc (Shor.standardLoweringSetup k h)).run').toIO coreCtx coreState
      return .ok doc
    catch e =>
      return .error (toString e)
  else
    return .error s!"runExtract: k = {k} must be > 1"

end Shor.Reflect
