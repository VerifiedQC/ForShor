import Lean.Data.Json
import FastMultiplication.Emit.Json.Common
import FastMultiplication.Emit.IR.Syntax

/-!
# The extracted symbolic IR: printers

One renderer/printer per inductive in `IR/Syntax.lean`. `WExpr`, `AExpr`,
`RegExpr`, `Prop'` render to a compact, fully-parenthesised formula string —
the same convention the (now-deleted) `Symbolic/Template.lean` used for its
`WExpr`, so a reader comparing old and new documents recognises the shape.
`Node`/`Template`/`Doc` print as structured `Json`, embedding those rendered
strings at the leaves.
-/

namespace Shor
namespace IR

open Lean (Json)

/-- Render a `WExpr` as a compact formula string, fully parenthesised;
`opaque fn args` renders as `fn(args)`. -/
partial def WExpr.render : WExpr → String
  | .var name => name
  | .lit n => toString n
  | .add a b => s!"({a.render} + {b.render})"
  | .sub a b => s!"({a.render} - {b.render})"
  | .mul a b => s!"({a.render} * {b.render})"
  | .div a b => s!"({a.render} div {b.render})"
  | .max a b => s!"max({a.render}, {b.render})"
  | .min a b => s!"min({a.render}, {b.render})"
  | .opaque fn args => s!"{fn}({String.intercalate ", " (args.map WExpr.render)})"

/-- Render an `AExpr`; `coeff phi l m` renders as `phi * coeff(l, m)`. -/
partial def AExpr.render : AExpr → String
  | .var name => name
  | .lit a => s!"{a.num}/{a.den}·π"
  | .mul a w => s!"({a.render} * {w.render})"
  | .coeff phi l m => s!"({phi.render} * coeff({l}, {m.render}))"
  | .div2 a => s!"({a.render} / 2)"
  | .neg a => s!"(-{a.render})"
  | .signedPair phi xi xw zi zw =>
      s!"({phi.render} * signedBitWeight({xw.render}, {xi.render}) * " ++
        s!"signedBitWeight({zw.render}, {zi.render}))"
  | .qftPhi m => s!"qftPhi({m.render})"
  | .ratio num denom => s!"({num.render} / {denom.render})"

/-- Render a `RegExpr` as a slice path, e.g. `x.active[0:4]`,
`ext(x.active[0:4], x.reserve[0:2])`, `x.active[3]`. -/
partial def RegExpr.render : RegExpr → String
  | .var name => name
  | .activeSlice r lo hi => s!"{r.render}.active[{lo.render}:{hi.render}]"
  | .reserveSlice r lo hi => s!"{r.render}.reserve[{lo.render}:{hi.render}]"
  | .ext active reserve => s!"ext({active.render}, {reserve.render})"
  | .qubit r i => s!"{r.render}[{i.render}]"
  | .grow r n => s!"grow({r.render}, {n.render})"

/-- Render a `Prop'` guard, e.g. `(a < b)`. -/
def Prop'.render : Prop' → String
  | .lt a b => s!"({a.render} < {b.render})"
  | .le a b => s!"({a.render} <= {b.render})"
  | .eq a b => s!"({a.render} = {b.render})"
  | .testBit n i => s!"testBit({n.render}, {i.render})"

/-- Serialize a template-body `Node`. Op names are exactly the
`LowGate`/`Gate` constructor names (D2); every width/angle/register operand
is a rendered formula string, never re-derived here. -/
partial def nodeJson : Node → Json
  | .op name regs nats angle flags =>
      Json.mkObj [
        ("op", Json.str name),
        ("regs", Json.arr (regs.map (fun r => Json.str r.render)).toArray),
        ("nats", Json.arr (nats.map (fun w => Json.str w.render)).toArray),
        ("angle", match angle with | none => Json.null | some a => Json.str a.render),
        ("flags", Json.arr (flags.map Json.bool).toArray)
      ]
  | .seq body =>
      Json.mkObj [("op", Json.str "seq"), ("body", Json.arr (body.map nodeJson).toArray)]
  | .adj body =>
      Json.mkObj [("op", Json.str "adj"), ("body", nodeJson body)]
  | .cond guard ifTrue ifFalse =>
      Json.mkObj [
        ("op", Json.str "cond"),
        ("guard", Json.str guard.render),
        ("then", nodeJson ifTrue),
        ("else", nodeJson ifFalse)
      ]
  | .call template wArgs aArgs rArgs =>
      Json.mkObj [
        ("op", Json.str "call"),
        ("template", Json.str template),
        ("wArgs", Json.arr (wArgs.map (fun w => Json.str w.render)).toArray),
        ("aArgs", Json.arr (aArgs.map (fun a => Json.str a.render)).toArray),
        ("rArgs", Json.arr (rArgs.map (fun r => Json.str r.render)).toArray)
      ]
  | .loop var lo hi body =>
      Json.mkObj [
        ("op", Json.str "loop"),
        ("var", Json.str var),
        ("lo", Json.str lo.render), ("hi", Json.str hi.render),
        ("body", nodeJson body)
      ]

/-- Serialize one extracted `Template`. -/
def templateJson (t : Template) : Json :=
  Json.mkObj [
    ("name", Json.str t.name),
    ("wParams", Json.arr (t.wParams.map Json.str).toArray),
    ("aParams", Json.arr (t.aParams.map Json.str).toArray),
    ("rParams", Json.arr (t.rParams.map Json.str).toArray),
    ("body", nodeJson t.body),
    ("provenance", Json.str t.provenance)
  ]

/-- Serialize the whole extracted `Doc`:
`{"schema": "forshor.ir/v1", "entry": …, "opaque": [...], "templates": [...]}`. -/
def docJson (d : Doc) : Json :=
  Json.mkObj [
    ("schema", Json.str "forshor.ir/v1"),
    ("entry", Json.str d.entry),
    ("opaque", Json.arr (d.opaqueFns.map (fun (name, arity) =>
      Json.mkObj [("name", Json.str name), ("arity", (arity : Json))])).toArray),
    ("templates", Json.arr (d.templates.map templateJson).toArray)
  ]

end IR
end Shor
