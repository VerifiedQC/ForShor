import ForShor.Emit.IR.Syntax

/-!
# The extracted symbolic IR: well-formedness

A cheap, `Bool`-valued sanity check on an extracted `Doc`, run before it is
trusted anywhere downstream (`Symbolic/Bundle.lean` refuses the whole bundle
if this fails). It is not part of the trust statement — that rests on the
translation table and Lean's normaliser, checked by `instantiate` agreeing
with the real term — this is a much cheaper structural smoke test that would
catch, e.g., a `call` naming a template that does not exist, or a `var`
nobody bound.

Four checks:

1. every `var` is a parameter of its template or an enclosing `loop` variable;
2. every `call` names a template in the `Doc` and matches its arity in all
   three parameter lists;
3. every `call` that can lead back to the enclosing template occurs under a
   `cond` whose guard is `lt`/`le`/`eq` *mentioning* a `wParam` or an
   opaque-function application — `phase_product`'s own guard,
   `nextWidth(xw, zw) < max(xw, zw)`, and the policy dispatcher's
   `t ≤ max(xw, zw)`, are both of this form; `qft`'s is a chain of `eq`s
   ruling out base-case widths rather than an `lt`/`le` at all
   (`regSize r = 0`, then `regSize r = 1`);
4. every `opaque` name is declared (`Doc.opaqueFns`) with the right arity.

**What check 3 is, precisely.** It is a *shape* check: that a recursive
cycle cannot be entered without passing a guard that at least looks at a
width. It does **not** test that the guard makes anything strictly decrease,
and never has — `wLicenses` accepts any opaque application whatever, so
`foo(xw) < 0` licenses recursion exactly as well as
`nextWidth(xw, zw) < max(xw, zw)` does. Termination is a theorem about the
Lean terms these templates were extracted from (`Policy.reserveNeed`'s own
`termination_by`, and the `PhaseLoweringPlan` recursion being structural),
not something the IR tier establishes. What check 3 buys is that an
*unguarded* cycle — which `instantiate` would unroll until it ran out of
fuel — is rejected cheaply and by name.

Until policies arrived the check only looked at *direct* recursion
(`template == selfName`). A policy document's recursion is indirect: the
dispatcher `phase_product` calls `phase_product_i`, which calls
`phase_product` back. Checking only direct self-calls would have passed such
a document without examining anything at all, so check 3 now works over the
call graph's reachability.

The rule is *every* edge of a cycle, not merely one: a call that can lead
back to its enclosing template must itself sit under a qualifying guard.
That is stricter than termination needs — one guarded edge per cycle would
do — but it is what every extracted document satisfies (a band body always
carries its shrink test, a dispatcher always carries its band guards), and
being local it stays a cheap syntactic check. It can only reject, never
wrongly accept.

`Bool`, not `Decidable`/`DecidableEq`: see `IR/Syntax.lean`'s deriving note —
the IR's nested-list recursion (`WExpr.opaque`, `Node.seq`) only has working
`BEq` instances, so every check here is written against `==`/`Bool`, exactly
`Json`'s existing convention in this emitter.
-/

namespace Shor
namespace IR

/-- Is `w` a bound `WExpr.var`, i.e. one of `scope`? `partial`: recursion
through `List WExpr` (the `opaque` case) is a nested-inductive occurrence the
structural/well-founded termination checker does not see through via
`List.all`, matching this file's other recursive checks. -/
partial def WExpr.wellFormed (opaqueFns : List (String × ℕ)) (scope : List String) :
    WExpr → Bool
  | .var name => scope.contains name
  | .lit _ => true
  | .add a b => a.wellFormed opaqueFns scope && b.wellFormed opaqueFns scope
  | .sub a b => a.wellFormed opaqueFns scope && b.wellFormed opaqueFns scope
  | .mul a b => a.wellFormed opaqueFns scope && b.wellFormed opaqueFns scope
  | .div a b => a.wellFormed opaqueFns scope && b.wellFormed opaqueFns scope
  | .max a b => a.wellFormed opaqueFns scope && b.wellFormed opaqueFns scope
  | .min a b => a.wellFormed opaqueFns scope && b.wellFormed opaqueFns scope
  | .opaque fn args =>
      (opaqueFns.any (fun (n, ar) => n == fn && ar == args.length)) &&
      args.all (fun a => a.wellFormed opaqueFns scope)

/-- `aScope` binds angle vars, `wScope` binds the width vars any embedded
`WExpr` may reference (`mul`'s weight, `coeff`'s `m`). -/
partial def AExpr.wellFormed (opaqueFns : List (String × ℕ)) (aScope wScope : List String) :
    AExpr → Bool
  | .var name => aScope.contains name
  | .lit _ => true
  | .mul a w => a.wellFormed opaqueFns aScope wScope && w.wellFormed opaqueFns wScope
  | .coeff phi _ m => phi.wellFormed opaqueFns aScope wScope && m.wellFormed opaqueFns wScope
  | .div2 a => a.wellFormed opaqueFns aScope wScope
  | .neg a => a.wellFormed opaqueFns aScope wScope
  | .signedPair phi xi xw zi zw =>
      phi.wellFormed opaqueFns aScope wScope && xi.wellFormed opaqueFns wScope &&
        xw.wellFormed opaqueFns wScope && zi.wellFormed opaqueFns wScope &&
        zw.wellFormed opaqueFns wScope
  | .qftPhi m => m.wellFormed opaqueFns wScope
  | .ratio num denom => num.wellFormed opaqueFns wScope && denom.wellFormed opaqueFns wScope

/-- `rScope` binds register vars, `wScope` binds the width vars a slice's
bounds may reference. -/
partial def RegExpr.wellFormed (opaqueFns : List (String × ℕ)) (rScope wScope : List String) :
    RegExpr → Bool
  | .var name => rScope.contains name
  | .activeSlice r lo hi =>
      r.wellFormed opaqueFns rScope wScope && lo.wellFormed opaqueFns wScope &&
        hi.wellFormed opaqueFns wScope
  | .reserveSlice r lo hi =>
      r.wellFormed opaqueFns rScope wScope && lo.wellFormed opaqueFns wScope &&
        hi.wellFormed opaqueFns wScope
  | .ext active reserve =>
      active.wellFormed opaqueFns rScope wScope && reserve.wellFormed opaqueFns rScope wScope
  | .qubit r i => r.wellFormed opaqueFns rScope wScope && i.wellFormed opaqueFns wScope
  | .grow r n => r.wellFormed opaqueFns rScope wScope && n.wellFormed opaqueFns wScope

def Prop'.wellFormed (opaqueFns : List (String × ℕ)) (wScope : List String) : Prop' → Bool
  | .lt a b => a.wellFormed opaqueFns wScope && b.wellFormed opaqueFns wScope
  | .le a b => a.wellFormed opaqueFns wScope && b.wellFormed opaqueFns wScope
  | .eq a b => a.wellFormed opaqueFns wScope && b.wellFormed opaqueFns wScope
  | .testBit n i => n.wellFormed opaqueFns wScope && i.wellFormed opaqueFns wScope

/-- Does `w` mention a width parameter or an opaque-function application?

`phase_product`'s own guard is `nextWidth(xw, zw) < max(xw, zw)`: the left
side is the opaque `nextWidth`, which is the quantity that decreases
across the recursive call. The policy dispatcher's guard is
`t ≤ max(xw, zw)`, where the evidence is the *parameters* inside a `max` —
so the search descends through arithmetic rather than looking only at the
head, which is what the single-table-only version did.

Descending makes the check strictly more permissive, and it is worth being
clear that permissiveness is the point: this licenses a guard, it never
claims the guard is a *decreasing* one (see the note at the top of this
file). -/
def wLicenses (tWParams : List String) : WExpr → Bool
  | .var n => tWParams.contains n
  | .opaque _ _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .max a b | .min a b =>
      wLicenses tWParams a || wLicenses tWParams b
  | .lit _ => false

/-- Does this guard license a direct-recursive `call` under it: `lt`/`le`
between a `wParam` (one of `tWParams`) — or an opaque-function application
of the parameters, `wLicenses` — and anything else? -/
-- `qft`'s own recursion guard is a *chain* of `eq`s ruling out base-case
-- widths (`regSize r = 0`, then `regSize r = 1`), not an `lt`/`le` at
-- all — by the time the `else`-of-`else` branch is reached, both have been
-- ruled out and the recursive `rightReg`/`leftReg` calls are on a strictly
-- smaller width, exactly as much evidence of termination as `lt`/`le`
-- against a `wParam`. Marking the `eq`'s own `then` branch (the base case,
-- with nothing to recurse into) as "guarded" too is harmless: rule 3 only
-- ever *permits* a recursive `call`, it never requires one.
def guardLicensesRecursion (tWParams : List String) : Prop' → Bool
  | .lt a b | .le a b | .eq a b => wLicenses tWParams a || wLicenses tWParams b
  -- `testBit` never guards a recursive `call` (`lowerCopyBitPowers`'s
  -- reformulated loop body has no recursion inside its `Node.cond`), so it
  -- carries no termination evidence either way — never licensing is safe.
  | .testBit _ _ => false

/-! ## The call graph

Check 3 needs to know whether a call can lead back to the template it sits
in. For a single-table document that is just `template == selfName`; for a
policy document the cycle runs dispatcher → band body → dispatcher, so the
question is reachability. -/

/-- Every template named by a `call` anywhere in this node. -/
partial def Node.callees : Node → List String
  | .op .. => []
  | .seq body => (body.map Node.callees).flatten
  | .adj body => Node.callees body
  | .cond _ t f => Node.callees t ++ Node.callees f
  | .call t _ _ _ => [t]
  | .loop _ _ _ body => Node.callees body

/-- The templates `name`'s body calls directly. -/
def Doc.directCallees (d : Doc) (name : String) : List String :=
  match d.templates.find? (fun t => t.name == name) with
  | none => []
  | some t => t.body.callees.eraseDups

/-- Can any template in `frontier` reach `tgt` by following calls?

`visited` is what makes this terminate: the graph is cyclic by design — that
is the whole point of check 3 — so without it the frontier never empties and
the search runs until `fuel` is gone. Since a template is never enqueued
twice, the frontier is empty within `templates.length` rounds and the
out-of-fuel branch is unreachable; it answers `true` anyway, which is the
conservative direction (it demands a guard rather than excusing one). -/
def Doc.reaches (d : Doc) : ℕ → List String → List String → String → Bool
  | 0, _, _, _ => true
  | _, [], _, _ => false
  | fuel + 1, frontier, visited, tgt =>
      if frontier.contains tgt then true
      else
        let visited' := visited ++ frontier
        let next := (frontier.flatMap d.directCallees).eraseDups.filter
          (fun n => !visited'.contains n)
        Doc.reaches d fuel next visited' tgt

/-- Does a call to `template` from inside `selfName` participate in a cycle,
and so need a guard above it? -/
def Doc.callNeedsGuard (d : Doc) (selfName template : String) : Bool :=
  template == selfName || d.reaches (d.templates.length + 1) [template] [] selfName

/-- Check 1 (var scoping), 2 (call arity/existence), 3 (guarded recursion)
and 4 (opaque arity) over one template body. `selfName`/`tWParams` are the
enclosing template's name and original width parameters (checked against for
rule 3); `wScope`/`aScope`/`rScope` are the names currently in scope (grown
by `loop`); `guarded` tracks whether the current position is under a
qualifying `cond` (rule 3). -/
partial def Node.wellFormed (d : Doc) (selfName : String) (tWParams : List String)
    (opaqueFns : List (String × ℕ)) (wScope aScope rScope : List String) (guarded : Bool) :
    Node → Bool
  | .op _ regs nats angle _flags =>
      regs.all (RegExpr.wellFormed opaqueFns rScope wScope) &&
      nats.all (WExpr.wellFormed opaqueFns wScope) &&
      (match angle with
        | none => true
        | some a => AExpr.wellFormed opaqueFns aScope wScope a)
  | .seq body =>
      body.all (Node.wellFormed d selfName tWParams opaqueFns wScope aScope rScope guarded)
  | .adj body =>
      Node.wellFormed d selfName tWParams opaqueFns wScope aScope rScope guarded body
  | .cond guard ifTrue ifFalse =>
      let guarded' := guarded || guardLicensesRecursion tWParams guard
      guard.wellFormed opaqueFns wScope &&
      Node.wellFormed d selfName tWParams opaqueFns wScope aScope rScope guarded' ifTrue &&
      Node.wellFormed d selfName tWParams opaqueFns wScope aScope rScope guarded' ifFalse
  | .call template wArgs aArgs rArgs =>
      (match d.templates.find? (fun t => t.name == template) with
        | none => false
        | some t =>
            t.wParams.length == wArgs.length && t.aParams.length == aArgs.length &&
              t.rParams.length == rArgs.length) &&
      (!d.callNeedsGuard selfName template || guarded) &&
      wArgs.all (WExpr.wellFormed opaqueFns wScope) &&
      aArgs.all (AExpr.wellFormed opaqueFns aScope wScope) &&
      rArgs.all (RegExpr.wellFormed opaqueFns rScope wScope)
  | .loop var lo hi body =>
      lo.wellFormed opaqueFns wScope && hi.wellFormed opaqueFns wScope &&
      Node.wellFormed d selfName tWParams opaqueFns (var :: wScope) aScope rScope guarded body

/-- One template is well-formed against its enclosing `Doc`: its body's
scoping/call/recursion/opaque rules all hold, starting from its own
parameter lists and no recursion guard yet in force. -/
def Template.wellFormed (d : Doc) (t : Template) : Bool :=
  Node.wellFormed d t.name t.wParams d.opaqueFns t.wParams t.aParams t.rParams false t.body

/-- A `Doc` is well-formed when every template is, and `entry` names one of
them. -/
def Doc.wellFormed (d : Doc) : Bool :=
  d.templates.all (Template.wellFormed d) && d.templates.any (fun t => t.name == d.entry)

end IR
end Shor
