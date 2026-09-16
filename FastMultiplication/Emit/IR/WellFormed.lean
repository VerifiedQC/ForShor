import FastMultiplication.Emit.IR.Syntax

/-!
# The extracted symbolic IR: well-formedness

A cheap, `Bool`-valued sanity check on an extracted `Doc`, run before it is
trusted anywhere downstream (`Symbolic/Bundle.lean` refuses the whole bundle
if this fails). It is not part of D7's trust statement — that rests on the
translation table and Lean's normaliser, checked by `instantiate` agreeing
with the real term — this is a much cheaper structural smoke test that would
catch, e.g., a `call` naming a template that does not exist, or a `var`
nobody bound.

Four checks, matching `Emit/PLAN.md` §4.3:

1. every `var` is a parameter of its template or an enclosing `loop` variable;
2. every `call` names a template in the `Doc` and matches its arity in all
   three parameter lists;
3. every `call` back to the enclosing template (direct recursion) occurs
   under a `cond` whose guard is `lt`/`le` between a `wParam` and an
   expression;
4. every `opaque` name is declared (`Doc.opaqueFns`) with the right arity.

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

def Prop'.wellFormed (opaqueFns : List (String × ℕ)) (wScope : List String) : Prop' → Bool
  | .lt a b => a.wellFormed opaqueFns wScope && b.wellFormed opaqueFns wScope
  | .le a b => a.wellFormed opaqueFns wScope && b.wellFormed opaqueFns wScope
  | .eq a b => a.wellFormed opaqueFns wScope && b.wellFormed opaqueFns wScope

/-- Does this guard license a direct-recursive `call` under it: `lt`/`le`
between a `wParam` (one of `tWParams`) and anything else? -/
def guardLicensesRecursion (tWParams : List String) : Prop' → Bool
  | .lt a b | .le a b =>
      (match a with | .var n => tWParams.contains n | _ => false) ||
        (match b with | .var n => tWParams.contains n | _ => false)
  | .eq _ _ => false

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
      (template != selfName || guarded) &&
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
