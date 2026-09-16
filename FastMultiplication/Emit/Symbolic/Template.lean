import Lean.Data.Json
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile

/-!
# E7: symbolic templates

The IR proper: the compiler's op *sequence* is fixed by the table (`Prog k`);
only slot widths, allocation amounts, leaf angles, and the recurse-or-not
decision vary with the width `W`, and each has an n-free rule. This file
prints one level of each template (phase-product, QFT, Shor) with widths as
a small typed expression language rather than as free text, matching the
*shape* of the real compiled term (`Compiler/Compile.lean`'s
`compileOpsToSignedGate`) op-for-op and side-for-side, not an approximation
of it — the exact allocation/body/deallocation order below is read directly
off `compileSignedAllocationsAux`/`compileAnnotatedOpsToSignedGateAux`/
`compileSignedDeallocationsAux`, not off the README's own "schematic"
illustration (that illustration groups allocations by side, x0,x1,z0,z1; the
real compiled term interleaves them by index, x0,z0,x1,z1 — this file follows
the real term).

This is descriptive only: nothing here is checked against the real lowering
(that is Phase 2's job). `nextWidth` is printed as one opaque named function
— its values live in the E3 table/affine tail already in the bundle, not
re-derived here.
-/

namespace Shor

open Operations
open Lean (Json)

/-- A small typed width-expression language: the width variable, natural
constants, `+ − × div`, `max`, and one opaque function `nextWidth` (E3's
`RecursivePhaseWorkspace.nextWidth`, printed as a name — its values live in
the `width` section of the bundle, not re-derived here). -/
inductive WExpr where
  | var (name : String)
  | const (n : ℕ)
  | add (a b : WExpr)
  | sub (a b : WExpr)
  | mul (a b : WExpr)
  | div (a b : WExpr)
  | max (a b : WExpr)
  | nextWidth (a : WExpr)
deriving Repr

/-- Render a `WExpr` as a compact formula string, e.g. `"(W div 2)"`,
`"nextWidth(W)"`. Fully parenthesized (simpler and unambiguous, at the cost
of a few more parens than a minimal-precedence pretty-printer would emit). -/
partial def WExpr.render : WExpr → String
  | .var name => name
  | .const n => toString n
  | .add a b => s!"({a.render} + {b.render})"
  | .sub a b => s!"({a.render} - {b.render})"
  | .mul a b => s!"({a.render} * {b.render})"
  | .div a b => s!"({a.render} div {b.render})"
  | .max a b => s!"max({a.render}, {b.render})"
  | .nextWidth a => s!"nextWidth({a.render})"

/-- Which operand register a slot belongs to. -/
inductive SlotSide where
  | x
  | z
deriving DecidableEq, Repr

def SlotSide.str : SlotSide → String
  | .x => "x"
  | .z => "z"

/-- A slot's symbolic name: `x0 … x{k-1}`, `z0 … z{k-1}` at this level.
Deeper recursion (not unrolled by this file — see the `recursion` field of
each template) would nest as `x0.x1`, parent path dot local name; there is no
existing nested-slot naming in the compiler to reuse, so this convention is
this file's own. -/
def slotName (side : SlotSide) (i : ℕ) : String := side.str ++ toString i

section PhaseProductTemplate

/-- `W` (the operand width) as a `WExpr` variable. -/
def wVar : WExpr := .var "W"

/-- Per-chunk limb width `W div k` (`phaseLimbWidthOfWidth`, `x`/`z` share one
budget in the template since both operands are `W` wide here). -/
def limbWidthExpr (k : ℕ) : WExpr := .div wVar (.const k)

/-- Slot `i`'s own logical width (`phaseSplitLogicalWidth`): the top chunk
absorbs the remainder. -/
def slotWidthExpr (k i : ℕ) : WExpr :=
  if i + 1 = k then .sub wVar (.mul (.const i) (limbWidthExpr k)) else limbWidthExpr k

/-- `nextWidth(W)`, opaque (E3's table has its values). -/
def nextWidthExpr : WExpr := .nextWidth wVar

/-- Allocation/deallocation delta for slot `i`: every slot in
`compileOpsToSignedGate` is grown to the *same* uniform target width
`nextWidth(W)` (`targetSignedLayoutState`/`commonNeededWidth` pick one width
for every slot, not a per-slot value), so this is just `nextWidth(W) − `
slot `i`'s own width. -/
def allocDeltaExpr (k i : ℕ) : WExpr := .sub nextWidthExpr (slotWidthExpr k i)

/-- One allocation gate for slot `i`: `signExtend` for the top (sign) chunk,
`zeroExtend` otherwise (`allocChunkGate`). -/
def allocOpJson (k : ℕ) (side : SlotSide) (i : ℕ) : Json :=
  Json.mkObj [
    ("op", Json.str (if i + 1 = k then "signExtend" else "zeroExtend")),
    ("slot", Json.str (slotName side i)),
    ("n", Json.str (allocDeltaExpr k i).render)
  ]

/-- The matching deallocation gate (`deallocChunkGate`). -/
def deallocOpJson (k : ℕ) (side : SlotSide) (i : ℕ) : Json :=
  Json.mkObj [
    ("op", Json.str (if i + 1 = k then "signDealloc" else "zeroDealloc")),
    ("slot", Json.str (slotName side i)),
    ("n", Json.str (allocDeltaExpr k i).render)
  ]

/-- One `AnnotatedOp`'s printed body gates, matching
`compileAnnotatedOpsToSignedGateAux` exactly: two-sided ops (`shiftL`,
`shiftR`, `negate`, `addScaled`) print their `x` gate then their `z` gate;
`phaseProduct i` with an assigned interpolation term `l` prints one
`(C)PhaseProduct` leaf naming child `l`; an unassigned `phaseProduct` (a
malformed table — more `phaseProduct`s than `q k` points) is dropped, exactly
as the real compiler drops it. -/
def annotatedOpJson (k : ℕ) (isCtrl : Bool) (aop : AnnotatedOp k) : List Json :=
  match aop.op with
  | .shiftL i n =>
      [ Json.mkObj [("op", Json.str "ShiftL"), ("slot", Json.str (slotName .x i)), ("n", (n : Json))],
        Json.mkObj [("op", Json.str "ShiftL"), ("slot", Json.str (slotName .z i)), ("n", (n : Json))] ]
  | .shiftR i n =>
      [ Json.mkObj [("op", Json.str "ShiftR"), ("slot", Json.str (slotName .x i)), ("n", (n : Json))],
        Json.mkObj [("op", Json.str "ShiftR"), ("slot", Json.str (slotName .z i)), ("n", (n : Json))] ]
  | .negate i =>
      [ Json.mkObj [("op", Json.str "Negate"), ("slot", Json.str (slotName .x i))],
        Json.mkObj [("op", Json.str "Negate"), ("slot", Json.str (slotName .z i))] ]
  | .addScaled dst src negSrc sh =>
      [ Json.mkObj [
          ("op", Json.str "AddScaled"), ("dst", Json.str (slotName .x dst)),
          ("src", Json.str (slotName .x src)), ("negSrc", Json.bool negSrc), ("shift", (sh : Json))
        ],
        Json.mkObj [
          ("op", Json.str "AddScaled"), ("dst", Json.str (slotName .z dst)),
          ("src", Json.str (slotName .z src)), ("negSrc", Json.bool negSrc), ("shift", (sh : Json))
        ] ]
  | .phaseProduct i =>
      match aop.phaseTerm? with
      | none => []
      | some l =>
          let base : List (String × Json) := [
            ("op", Json.str (if isCtrl then "CPhaseProduct" else "PhaseProduct")),
            ("child", ((l : ℕ) : Json)),
            ("x", Json.str (slotName .x i)),
            ("z", Json.str (slotName .z i)),
            ("angle", Json.str s!"phi * c_{(l : ℕ)}(2^{(limbWidthExpr k).render})")
          ]
          [Json.mkObj (if isCtrl then base ++ [("ctrl", Json.str "ctrl")] else base)]

/-- The phase-product template (E7), one level: allocate every slot to
`nextWidth(W)`, replay the table's ops (each two-sided op on both operands,
each `phaseProduct` as a `(C)PhaseProduct` leaf carrying `phi · c_l`), then
deallocate. `isCtrl` selects the controlled variant
(`compileOpsToCSignedGate`/`controlPhaseLeaves`): same shape, `CPhaseProduct`
leaves, plus a `ctrl` parameter. -/
def phaseProductTemplateJson {k : ℕ} (ops : Prog k) (isCtrl : Bool) : Json :=
  let annOps := annotatePhaseTermsAux k 0 ops
  -- `compileSignedAllocationsAux`: recurses on the smaller prefix first, so
  -- chunks are emitted in increasing index order; each chunk does x then z.
  let allocs : List Json := (List.range k).flatMap fun i => [allocOpJson k .x i, allocOpJson k .z i]
  -- `compileSignedDeallocationsAux`: recurses *after* the current (largest)
  -- chunk, so chunks are emitted in decreasing index order; each chunk does
  -- z then x.
  let deallocs : List Json :=
    (List.range k).reverse.flatMap fun i => [deallocOpJson k .z i, deallocOpJson k .x i]
  let body : List Json := annOps.flatMap (annotatedOpJson k isCtrl)
  let slots : List (String × Json) :=
    (List.range k).flatMap fun i =>
      [ (slotName .x i, Json.str (slotWidthExpr k i).render),
        (slotName .z i, Json.str (slotWidthExpr k i).render) ]
  let fields : List (String × Json) := [
    ("op", Json.str (if isCtrl then "CSignedPhaseProd" else "SignedPhaseProd")),
    ("param", Json.str "W"),
    ("limb_width", Json.str (limbWidthExpr k).render),
    ("next_width", Json.str nextWidthExpr.render),
    ("slots", Json.mkObj slots),
    ("body", Json.arr (allocs ++ body ++ deallocs).toArray),
    ("recursion", Json.str
      ("each (C)PhaseProduct child is this template at W' = nextWidth(W) if nextWidth(W) < W, " ++
        s!"else Naive{if isCtrl then "C" else ""}SignedPhaseProd(W', W')"))
  ]
  Json.mkObj (if isCtrl then fields ++ [("ctrl", Json.str "ctrl")] else fields)

end PhaseProductTemplate

section QftTemplate

/-- The QFT template (E7): `left = w/2`, `right = w − w/2` (`splitM`'s
convention, same as E4's `Symbolic/QftPlan.lean`), `qftPhi w` symbolic,
radix-reverse cost `3·(w/2)`, recursion `QFT(w) = QFT(right) ;
PhaseProduct(qftPhi w, left, right) ; QFT(left) ; RadixReverse`, base cases
`QFT(0) = id`, `QFT(1) = H`. -/
def qftTemplateJson : Json :=
  let wq : WExpr := .var "w"
  let leftExpr : WExpr := .div wq (.const 2)
  let rightExpr : WExpr := .sub wq leftExpr
  Json.mkObj [
    ("op", Json.str "QFT"),
    ("param", Json.str "w"),
    ("left_width", Json.str leftExpr.render),
    ("right_width", Json.str rightExpr.render),
    ("phi", Json.str "qftPhi(w)"),
    ("radix_reverse_cost", Json.str s!"(3 * {leftExpr.render})"),
    ("recursion", Json.str
      ("QFT(w) = QFT(right) ; PhaseProduct(qftPhi(w), left, right, each zero-extended by 1) ; " ++
        "QFT(left) ; RadixReverse(w, left); QFT(0) = id; QFT(1) = H"))
  ]

end QftTemplate

section ShorTemplate

/-- The Shor template (E7). Fully symbolic — `n`, `m`, `a`, `N` are all named
parameters, never substituted with concrete numbers (this document is
`n_free`, and `bundle` takes no instance data): the `Gate` tree of
`orderFindingApprox`/`modExpApproxValid`/`CmodMulInPlaceCore` with registers
replaced by E5's named width formulas and each atomic leaf (`QFT`,
`(C)SignedPhaseProd`) pointing at the phase-product/QFT templates by name.
`U3`/`U4` (`CmpGeConst`/`CSubConst`, via `lowerCmpGeConst`/`lowerCSubConst`)
are linear in the register width with no recursion and no table dependence,
so they are not tabulated: their per-width counts are meant to be read off
concrete `shor` documents and fitted outside Lean (see `provenance`). -/
def shorTemplateJson : Json :=
  let u1u5Step (name ctrlRef phiFormula : String) : Json :=
    Json.mkObj [
      ("op", Json.str name),
      ("body", Json.str s!"H_reg(work) ;; {ctrlRef}(phi, data, work) ;; IQFT(work)"),
      ("phi", Json.str phiFormula),
      ("phase_product_ref", Json.str "template.controlled_phase_product"),
      ("qft_ref", Json.str "template.qft")
    ]
  Json.mkObj [
    ("op", Json.str "Shor"),
    ("params", Json.arr #[Json.str "n", Json.str "m", Json.str "a", Json.str "N"]),
    ("widths", Json.mkObj [
      ("x_width", Json.str "referenceXWidth(n)"),
      ("data_width", Json.str "referenceDataWidth(n)"),
      ("work_width", Json.str "referenceWorkWidth(n, m)"),
      ("scratch_width", Json.str "referenceScratchWidth(n, m)")
    ]),
    ("body", Json.arr #[
      Json.mkObj [("op", Json.str "H_reg"), ("reg", Json.str "x")],
      Json.mkObj [("op", Json.str "initY1"), ("reg", Json.str "y")],
      Json.mkObj [
        ("op", Json.str "loop"),
        ("var", Json.str "e"), ("range", Json.str "0 .. n-1"),
        ("body", Json.mkObj [
          ("op", Json.str "CmodMulInPlaceCore"),
          ("c", Json.str "(a^(2^e)) mod N"),
          ("ctrl", Json.str "x[e]"),
          ("steps", Json.arr #[
            u1u5Step "U1" "CPhaseProdUsing" "2 * ((c + N - 1) mod N) / N",
            Json.mkObj [
              ("op", Json.str "U2"),
              ("body", Json.str "QFT(work) ;; PhaseProdUsing(phi, work, dataCarry) ;; IQFT(work)"),
              ("phi", Json.str "2 * N / 2^(work_width + data_width + 1)"),
              ("phase_product_ref", Json.str "template.phase_product"),
              ("qft_ref", Json.str "template.qft")
            ],
            Json.mkObj [
              ("op", Json.str "U3"),
              ("body", Json.str "CmpGeConst(N, dataCarry, scratch, flag) ;; CSubConst(N, dataCarry, scratch, flag)"),
              ("note", Json.str
                "linear in width, no recursion, no table dependence — not tabulated here")
            ],
            Json.mkObj [
              ("op", Json.str "U4"),
              ("body", Json.str "cmpLtNW(N, dataCarry, work, scratch, flag)"),
              ("note", Json.str
                "linear in width, no recursion, no table dependence — not tabulated here")
            ],
            u1u5Step "U5" "adj(CPhaseProdUsing)" "2 * (step5Constant(a, N) mod N) / N"
          ])
        ])
      ],
      Json.mkObj [
        ("op", Json.str "IQFT"), ("reg", Json.str "x"), ("qft_ref", Json.str "template.qft")
      ]
    ]),
    ("provenance", Json.str
      ("Gate-tree shape of Shor.Reference.orderFindingApprox / modExpApproxValid / " ++
        "CmodMulInPlaceCore, evaluated structurally (not a theorem). U3/U4 " ++
        "(CmpGeConst/CSubConst, lowered by lowerCmpGeConst/lowerCSubConst) are linear in " ++
        "register width with no recursion and no table dependence; their per-width counts are " ++
        "fitted from concrete `shor` emissions outside Lean, not tabulated in this document."))
  ]

end ShorTemplate

end Shor
