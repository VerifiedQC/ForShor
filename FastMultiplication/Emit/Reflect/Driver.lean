import Lean
import FastMultiplication.Emit.Reflect.Targets
import FastMultiplication.Emit.Reflect.PolicyTargets
import FastMultiplication.ShorVerification.Implementation.Reference.StandardLoweringSetup

/-!
# The extractor: `ToExpr`, and the build-time/run-time drivers

`IR/Syntax.lean`'s deriving note deferred `ToExpr` to this file: `WExpr`
(`opaque`'s `List WExpr`) and `Node` (`seq`'s `List Node`) are the two types
with a self-referential `List` field, and Lean's `deriving ToExpr` handler
rejects that shape exactly as it rejects `DecidableEq`/`LawfulBEq` (see
`IR/Syntax.lean`'s deriving note). The fix
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

/-- The `Doc` this file's extractors build: `phase_product`/`naive_leaf`,
`cphase_product`/`naive_cleaf` (each pair needed together — a phase-product
template's base case is a `Node.call` to its `naive_*leaf` counterpart, so a
`Doc` with one but not the other is never `wellFormed`), `qft` (which itself
`Node.call`s `phase_product` at each split, so needs it in the same `Doc`
too), and `shor_gate`/`shor`. `entry` is `phase_product`.

`pp_body` is *not* among them, and `includePPBody` is how `Tests.lean`'s
`pp_body` section gets it. It is one level of `compileOpsToSignedGate` with
the layout left symbolic, and its `layout` is built from `k` fresh
per-child reserve *variables* (`x0R`, `z1R`, …). Those are free
`RegExpr.var`s with nothing in the bundle that says what to bind them to:
the test binds them by calling `ReserveBudget.childReserve` itself, which
is exactly the thing a consumer holding only the bundle cannot do. Shipping
it would invite a reader to instantiate a template that cannot be
instantiated from the document, so it stays a test artifact.

Takes any `Shor.ShorLoweringSetup`. `setup` is a table the lowering
theorems cover *by construction* — its four side conditions are exactly
those theorems' hypotheses — so there is no kind of table to special-case or
reject here: an invalid one cannot be packaged as a `ShorLoweringSetup` in
the first place. -/
def buildDoc (setup : Shor.ShorLoweringSetup) (includePPBody : Bool := false) : MetaM IR.Doc := do
  let pp2 ← extractPhaseProductBody setup
  let cpp2 ← extractCPhaseProductBody setup
  let qft ← extractQFTBody setup
  let shorGate ← extractShorGateBody
  let shor ← extractShorBody setup
  let core := [pp2, cpp2, qft, shorGate, shor, naiveLeafTemplate, naiveCLeafTemplate]
  let templates ←
    if includePPBody then do
      let pp ← extractPPBody setup
      pure (pp :: core)
    else pure core
  pure
    { templates := templates
      opaqueFns := [("nextWidth", 2), ("reserveNeed_x", 2), ("reserveNeed_z", 2),
        ("qftXWork", 1), ("qftZWork", 1), ("log2", 1), ("mod", 2), ("pow", 2),
        ("step5Const", 2), ("modpow", 3)]
      entry := pp2.name }

/-! ### Reusing a band body for a repeated table

A best-known policy at large `n` reuses a handful of tables across many bands
(34 bands over 7 tables at `n = 50000`), and the body extraction is by far the
most expensive step of the build (minutes per band, all elaboration). A band
body depends on its table, its template name and its `coeff` offset only: the
policy enters through opaque oracle names (`Registry`), never through a
threshold. So a band whose table already occurred at an earlier band reuses
that body, with every `coeff` index shifted by the difference of the two
offsets and the template renamed. The evaluation tier checks every band body
(one level deep, on the probe submission), reused or not. -/

/-- The same table, compared as quoted terms (`k`, points, program). -/
def sameTable (a b : Shor.ShorLoweringSetup) : MetaM Bool := do
  if a.k != b.k then return false
  let kE := Lean.toExpr a.k
  let (pa, _) ← setupPtsExprs a kE
  let (pb, _) ← setupPtsExprs b kE
  return pa == pb && Lean.toExpr a.ops == Lean.toExpr b.ops

/-- Band bodies of one flavour, extracting each distinct table once. -/
def policyBandBodies (controlled : Bool) (polE : Expr)
    (indexed : List ((ℕ × Shor.ShorLoweringSetup) × ℕ) × List ℕ) : MetaM (List IR.Template) := do
  let (bands, offsets) := indexed
  let mut done : Array (Shor.ShorLoweringSetup × ℕ × ℕ × IR.Template) := #[]   -- setup, band, offset, body
  let mut out : Array IR.Template := #[]
  for (((_, setup), i), off) in bands.zip offsets do
    let mut reused : Option IR.Template := none
    for (s', j, off', t') in done do
      if reused.isNone && off' ≤ off then
        if (← sameTable setup s') then
          reused := some { t' with
            name := IR.bandBodyName controlled i
            body := IR.shiftCoeffN (off - off') t'.body
            provenance := s!"{t'.provenance}; reused for band {i} (same table as band {j}), coeff indices +{off - off'}" }
    let t ← match reused with
      | some t => pure t
      | none =>
          if controlled then extractPolicyCPhaseProductBody polE setup i off
          else extractPolicyPhaseProductBody polE setup i off
    if reused.isNone then
      done := done.push (setup, i, off, t)
    out := out.push t
  return out.toList

/-- The `Doc` for a **policy**: one dispatcher per phase-product flavour, one
body template per band, and the shared `qft`/`shor_gate`/`shor`/leaf
templates.

`entry` is `phase_product`, which is now the *dispatcher* rather than a
body — and that is what makes the rest of the document need no edit, since
`qft`, `shor` and every band body reach the phase product by that name
(`Extract.lean`'s `Policy.signedPlan` cases).

`polE` must be the policy of `s`, as an `Expr` naming a declared constant:
`ShorLoweringPolicy` carries a `sorted` proof field, so there is no `ToExpr`
to quote it with, and the band bodies need a `P` whose `choose` the
elaborator can see through. `elabExtractPolicyIrDocImpl` builds it from the
same identifier it reads `s` from, so the two cannot disagree.

`opaqueFns` is **unchanged** from `buildDoc`'s. A policy needs no new opaque
names and no new arities: `Policy.reserveNeed P` is already a function of
`(wx, wz)` alone — the band enters only through `P.choose (max wx wz)` inside
it — and `nextWidth` is evaluated by a band body only at widths where the
dispatcher sent it there, which is where the policy-keyed and band-keyed
answers agree. -/
def buildPolicyDoc (s : Shor.ShorPolicySubmission) (polE : Expr) : MetaM IR.Doc := do
  -- Band `i`'s interpolation points occupy `[offset i, offset i + q kᵢ)` of
  -- the bands' concatenated point lists; see `Registry.coeffOffset`.
  let offsets : List ℕ :=
    (s.bands.foldl (fun (acc, off) b => (acc ++ [off], off + Shor.q b.2.k)) ([], 0)).1
  let bandsIdx := s.bands.zipIdx
  let bodies ← policyBandBodies false polE (bandsIdx, offsets)
  let cbodies ← policyBandBodies true polE (bandsIdx, offsets)
  let qft ← extractPolicyQFTBody polE
  let shorGate ← extractShorGateBody
  let shor ← extractPolicyShorBody polE
  pure
    { templates :=
        IR.dispatcherTemplate s.policy false :: IR.dispatcherTemplate s.policy true ::
          bodies ++ cbodies ++
          [qft, shorGate, shor, naiveLeafTemplate, naiveCLeafTemplate]
      opaqueFns := [("nextWidth", 2), ("reserveNeed_x", 2), ("reserveNeed_z", 2),
        ("qftXWork", 1), ("qftZWork", 1), ("log2", 1), ("mod", 2), ("pow", 2),
        ("step5Const", 2), ("modpow", 3)]
      entry := "phase_product" }

-- `extract_policy_ir_doc <id> <policyIdent>`: `extract_ir_doc`'s sibling for
-- a `Shor.ShorPolicySubmission`. Same mechanism throughout — resolve the
-- identifier, `evalExpr` it to read the bands, splice the resulting `Doc` in
-- as a `def` — with two differences: the evaluated type, and that the
-- identifier is *also* kept as an `Expr` (`polE`), because the band bodies
-- are extracted against the policy as a term and not merely against its
-- values.
open Lean Elab Command in
unsafe def elabExtractPolicyIrDocImpl (id : Ident) (policyIdent : Ident) :
    CommandElabM Unit := do
  let ns ← getCurrNamespace
  let declName := ns ++ id.getId
  let policyName ← resolveGlobalConstNoOverload policyIdent
  liftTermElabM do
    let subTyE := mkConst ``Shor.ShorPolicySubmission
    let sub ← Lean.Meta.evalExpr Shor.ShorPolicySubmission subTyE (mkConst policyName)
    let polE := mkApp (mkConst ``Shor.ShorPolicySubmission.policy) (mkConst policyName)
    let doc ← buildPolicyDoc sub polE
    let decl := Declaration.defnDecl
      { name := declName, levelParams := [], type := mkConst ``Shor.IR.Doc
        value := toExpr doc, hints := .regular 0, safety := .safe }
    addDecl decl
    compileDecl decl

open Lean Elab Command in
elab "extract_policy_ir_doc " id:ident policyIdent:ident : command =>
  unsafe elabExtractPolicyIrDocImpl id policyIdent

-- `extract_ir_doc <id> <setupIdent>`:
-- `setupIdent` names a `Shor.ShorLoweringSetup` declaration in scope (the
-- *value*, not a numeral: with the table itself carrying its own points and
-- coverage proofs, there is nothing for a table-source argument to select
-- between). Resolved with `resolveGlobalConstNoOverload`, then
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
-- unreconstructable placeholders, which then fail to re-elaborate (the
-- `phase_product` template is already past that size). Going straight from the `Expr` `buildDoc` already produced
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
unsafe def elabExtractIrDocImpl (id : Ident) (setupIdent : Ident) (includePPBody : Bool) :
    CommandElabM Unit := do
  let ns ← getCurrNamespace
  let declName := ns ++ id.getId
  let setupName ← resolveGlobalConstNoOverload setupIdent
  liftTermElabM do
    let setupTyE := mkConst ``Shor.ShorLoweringSetup
    let setup ← Lean.Meta.evalExpr Shor.ShorLoweringSetup setupTyE (mkConst setupName)
    let doc ← buildDoc setup includePPBody
    let decl := Declaration.defnDecl
      { name := declName, levelParams := [], type := mkConst ``Shor.IR.Doc
        value := toExpr doc, hints := .regular 0, safety := .safe }
    addDecl decl
    compileDecl decl

open Lean Elab Command in
elab "extract_ir_doc " id:ident setupIdent:ident : command =>
  unsafe elabExtractIrDocImpl id setupIdent false

-- `extract_ir_doc_with_pp_body <id> <setupIdent>`: the same, plus `pp_body`.
-- Only `Tests.lean`'s `pp_body` section wants it — see `buildDoc`.
open Lean Elab Command in
elab "extract_ir_doc_with_pp_body " id:ident setupIdent:ident : command =>
  unsafe elabExtractIrDocImpl id setupIdent true

/-- Run-time entry point: `lake exe forshor_emit`'s own
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

The run-time CLI (`template`/`bundle`) only ever extracts the standard
table — `standardLoweringSetup k h`, built here as an ordinary
(non-reflected) function call. A custom table is a build-time-only path
(`extract_ir_doc` above, named in a Lean file the user writes and compiles);
there is deliberately no way to hand `runExtract` an arbitrary
`ShorLoweringSetup` from the command line, because a table's side-condition
proofs need the kernel rather than a parser. -/
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
