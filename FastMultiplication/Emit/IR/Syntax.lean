import FastMultiplication.ShorVerification.Framework.AbstractMachine.LowGate

/-!
# The extracted symbolic IR: syntax

A small first-order language of parameterised templates that R1's extractor
(`Emit/Reflect/Extract.lean`) produces by reading the verified
`referenceProgramAt` call chain via reflection (see `Emit/PLAN.md` §0–§1).
Nothing here is written by hand per table or per `k`: a `Doc` is data, and
its shape comes entirely from what the extractor found.

`op` names are exactly the `LowGate`/`Gate` constructor names, so the flat
and symbolic documents share one vocabulary (D2). Recursion is never unrolled
in this language: a recursive definition yields one `Template` whose body
contains a `Node.call` to itself (D3); `IR/Instantiate.lean` unrolls at a
concrete width.

**Deriving note.** `WExpr.opaque` and `Node.seq` recurse through `List Self`
("nested inductive" occurrences). Lean's `DecidableEq`/`ToExpr`/`LawfulBEq`
deriving handlers do not support that shape (`deriving DecidableEq` fails
outright on a type like `inductive T | leaf | list (args : List T)`), while
`Repr` and `BEq` do. So every type below derives `Repr, BEq` only, and
structural equality throughout this development is `BEq`'s `==`, exactly the
convention `Json` already uses in this emitter (`Lower/Instantiate.lean`'s
`check1_annotatedEqFlat`, `==` on `Json`) rather than `DecidableEq`/`decide`.
`ToExpr` (needed only by R1's `Reflect/Driver.lean` build-time command, to
splice a `Doc` into a `def`) is deferred to that file, where it can be
written by hand against the concrete recursion shape once that command
exists; nothing in R0–R3 needs it.
-/

namespace Shor
namespace IR

/-- Width- and index-valued expressions: the free variables the extractor
leaves symbolic (`var`), natural literals, arithmetic, and one `opaque`
escape hatch for the functions D4 keeps un-inlined (`nextWidth`,
`reserveNeed_x/z`, `qftWorkspaceNeed`, `log2`, `clog`), applied to their
(already-translated) argument expressions. -/
inductive WExpr
  | var (name : String)
  | lit (n : ℕ)
  | add (a b : WExpr)
  | sub (a b : WExpr)
  | mul (a b : WExpr)
  | div (a b : WExpr)
  | max (a b : WExpr)
  | min (a b : WExpr)
  | opaque (fn : String) (args : List WExpr)
deriving Repr, BEq

/-- Angle-valued expressions, in units of `π`. `mul` is an angle scaled by an
integer/width weight (a two's-complement bit weight, say); `coeff` is the
opaque Cramer interpolation weight `phi * coeff(l, m)` (D4); `div2`/`neg` are
`CPhase`'s `θ/2`/`−θ/2`. -/
inductive AExpr
  | var (name : String)
  | lit (a : Angle)
  | mul (a : AExpr) (w : WExpr)
  | coeff (phi : AExpr) (l : ℕ) (m : WExpr)
  | div2 (a : AExpr)
  | neg (a : AExpr)
deriving Repr, BEq

/-- Register expressions: slice paths back to a template's register
parameter, mirroring `Reg.take`/`Reg.drop`/`ExtReg.withReserve`/single-qubit
indexing on the real registers. `grow` names `ExtReg.grow` directly (rather
than expanding it into slice arithmetic): the grown register's active part
is a genuine append of *two different sources* — the original active slice
and a prefix of whatever the reserve turned out to be — which is not a
single slice of anything nameable, so this is D2's "name the construct, do
not inline its semantics" applied to `ExtReg.grow` itself. -/
inductive RegExpr
  | var (name : String)
  | activeSlice (r : RegExpr) (lo hi : WExpr)
  | reserveSlice (r : RegExpr) (lo hi : WExpr)
  | ext (active reserve : RegExpr)
  | qubit (r : RegExpr) (i : WExpr)
  | grow (r : RegExpr) (n : WExpr)
deriving Repr, BEq

/-- Decidable guards on `WExpr`s: what a `dite`/`Nat.casesOn`/matcher on a
symbolic width translates to (`Node.cond`'s `guard`). -/
inductive Prop'
  | lt (a b : WExpr)
  | le (a b : WExpr)
  | eq (a b : WExpr)
deriving Repr, BEq

/-- One node of a template body.

`op` covers every `LowGate`/`Gate` constructor uniformly by name (D2): `regs`
are its register arguments in declaration order, `nats` its natural-number
arguments (widths/shifts/indices as `WExpr`s), `angle` its `Angle` argument
if it has one, `flags` its `Bool` arguments (e.g. `AddScaled`'s `negSrc`).
`seq` right-folds like `LowGate.sequence`/`Gate.seq`. `call` is a reference
to another template or (recursively) to the enclosing one — never unrolled
here (D3); `IR/Instantiate.lean` performs the unrolling at a concrete width.
`loop` is a bounded iteration over a width-valued range (e.g. the naive
leaf's sum over `signedTerms`, Shor's loop over exponent bits). -/
inductive Node
  | op (name : String) (regs : List RegExpr) (nats : List WExpr) (angle : Option AExpr)
      (flags : List Bool)
  | seq (body : List Node)
  | adj (body : Node)
  | cond (guard : Prop') (ifTrue ifFalse : Node)
  | call (template : String) (wArgs : List WExpr) (aArgs : List AExpr) (rArgs : List RegExpr)
  | loop (var : String) (lo hi : WExpr) (body : Node)
deriving Repr, BEq

/-- One extracted template: a named, parameterised gate-tree schema. Its
`body` may `call` itself (direct recursion, unrolled only by `instantiate`,
D3) or another template on the call chain. `provenance` names the Lean
constant it was extracted from (D7: this is evidence, not a proof). -/
structure Template where
  name : String
  wParams : List String
  aParams : List String
  rParams : List String
  body : Node
  provenance : String
deriving Repr, BEq

/-- The whole extracted symbolic IR: every template on the call chain, the
opaque functions they refer to (name, arity), and which template is the
document's entry point. -/
structure Doc where
  templates : List Template
  opaqueFns : List (String × ℕ)
  entry : String
deriving Repr, BEq

end IR
end Shor
