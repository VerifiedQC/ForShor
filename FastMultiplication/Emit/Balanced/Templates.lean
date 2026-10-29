import FastMultiplication.Emit.Symbolic.Dispatcher

/-!
# Balanced phase products in the IR: the two site templates and the document transform

`Shor.Balanced.balance` (Implementation/Reference/Balanced/Defs.lean) rewrites every
Shor-level phase-product site through `siteGate` with `defaultRule`. Its IR form is two
*built* templates (like the dispatchers, not reflected) with the dispatchers' own
signature:

* `balanced_phase_product`  — wParams `[xw, zw, xCap, zCap]`, aParams `[phi]`, rParams `[x, z]`;
* `balanced_cphase_product` — the same with rParams `[ctrl, x, z]`.

Their body is `siteGate P defaultRule c φ x z` written in the IR's existing vocabulary:
guards (`cond`), `loop`, `op zeroExtend/signExtend/signDealloc/zeroDealloc`, and calls to the
existing dispatcher `phase_product` / `cphase_product` at **equal** widths `(t, t)`, with the
block's angle `phi * pow(2, offset)`. The fit check `fitsB` uses the opaque `reserveNeed_x`,
`reserveNeed_z` at `(t, t)`; no new opaque function and no new op kind is introduced.

`balanceDoc` adds the two templates and retargets the `shor` template's calls to
`phase_product`/`cphase_product` (the Steps 1, 2, 4, 5 sites) to them. `qft` keeps calling the
dispatcher directly (its twiddles are not balanced, matching `balance`, which leaves `QFT` gates
to `Policy.lowerQFT`), and `shor_gate` (the high-level source gate) is unchanged.

Agreement with the real balanced lowering is checked by evaluation
(`Emit/Balanced/Verify.lean`), not proved.
-/

namespace Shor
namespace IR
namespace Balanced

def balancedName (controlled : Bool) : String :=
  if controlled then "balanced_cphase_product" else "balanced_phase_product"

private def v (s : String) : WExpr := .var s
private def n (k : ℕ) : WExpr := .lit k
private def rx (t : WExpr) : WExpr := .opaque "reserveNeed_x" [t, t]
private def rz (t : WExpr) : WExpr := .opaque "reserveNeed_z" [t, t]
private def pow2 (e : WExpr) : WExpr := .opaque "pow" [.lit 2, e]

/-- `cond g₁ (cond g₂ (… ok) fb) fb`: all guards, else the fallback. -/
def guarded (gs : List Prop') (ok fb : Node) : Node :=
  gs.foldr (fun g acc => .cond g acc fb) ok

/-- The dispatcher call for one block product, at the common width `t`. -/
def prodCall (controlled : Bool) (t xCapE zCapE : WExpr) (phi : AExpr) (X Z : RegExpr) : Node :=
  .call (dispatcherName controlled) [t, t, xCapE, zCapE] [phi]
    ((if controlled then [RegExpr.var "ctrl"] else []) ++ [X, Z])

/-- Active slice `[lo, hi)` of `X`, owning all of `X`'s reserve (`lowBlock`/`highPart`). -/
def blockReg (X : RegExpr) (lo hi LC : WExpr) : RegExpr :=
  .ext (.activeSlice X lo hi) (.reserveSlice X (.lit 0) LC)

/-- `topGate c φ X' Z t` (`X'` of width `Lx`). -/
def topNode (controlled : Bool) (X' Z : RegExpr) (Lx s LC SC t : WExpr) (phi : AExpr) : Node :=
  let a := WExpr.sub t Lx
  let d := WExpr.sub t s
  .seq [ .op "signExtend" [X'] [a] none [],
         .op "signExtend" [Z] [d] none [],
         prodCall controlled t (.sub LC a) (.sub SC d) phi (.grow X' a) (.grow Z d),
         .op "signDealloc" [Z] [d] none [],
         .op "signDealloc" [X'] [a] none [] ]

/-- `lowGate c φ X_i Z w t` for the low block `X[lo, lo + w)`. -/
def lowNode (controlled : Bool) (X Z : RegExpr) (lo w s LC SC t : WExpr) (phi : AExpr) : Node :=
  let Xi := blockReg X lo (.add lo w) LC
  let a := WExpr.sub t w
  let d := WExpr.sub t s
  .seq [ .op "zeroExtend" [Xi] [a] none [],
         .op "signExtend" [Z] [d] none [],
         prodCall controlled t (.sub LC a) (.sub SC d) phi (.grow Xi a) (.grow Z d),
         .op "signDealloc" [Z] [d] none [],
         .op "zeroDealloc" [Xi] [a] none [] ]

/-- `fitsB P [] t X Z` for an operand of width `Lx`. -/
def topGuards (Lx s LC SC t : WExpr) : List Prop' :=
  [ .le Lx t, .le s t, .le (.add (.sub t Lx) (rx t)) LC, .le (.add (.sub t s) (rz t)) SC ]

/-- `siteGate`'s split branch with `X` the wider operand (width `L`, capacity `LC`) and `Z`
the narrower (`s`, `SC`), following `defaultPlan L s` and `fitsB`. -/
def splitBranch (controlled : Bool) (X Z : RegExpr) (L s LC SC : WExpr) (fb : Node) : Node :=
  let phi := AExpr.var "phi"
  -- padding: plan ⟨[], L⟩
  let padNode := guarded (topGuards L s LC SC L) (topNode controlled X Z L s LC SC L phi) fb
  -- blocks: B = ⌈L/s⌉, w = s - 1, top = L - (B-1)w, t = max s top
  let B := WExpr.div (.add L (.sub s (n 1))) s
  let w := WExpr.sub s (n 1)
  let off := WExpr.mul (.sub B (n 1)) w
  let top := WExpr.sub L off
  let t := WExpr.max s top
  let topBlock := topNode controlled (blockReg X off L LC) Z top s LC SC t
    (.mul phi (pow2 off))
  let lowGuards : List Prop' :=
    [ .lt w (.sub L (.mul (.sub B (n 2)) w)), .le (.add w (n 1)) t, .le s t,
      .le (.add (.sub t w) (rx t)) LC, .le (.add (.sub t s) (rz t)) SC ]
  let withLower := guarded (lowGuards ++ topGuards top s LC SC t)
    (.seq [ .loop "i" (n 0) (.sub B (n 1))
              (lowNode controlled X Z (.mul (v "i") w) w s LC SC t (.mul phi (pow2 (.mul (v "i") w)))),
            topBlock ]) fb
  let topOnly := guarded (topGuards top s LC SC t) topBlock fb
  let blocksNode := Node.cond (.le (n 2) B) withLower topOnly
  .cond (.le (n 2) s) (.cond (.le (.mul (n 2) L) (.mul (n 3) s)) padNode blocksNode) fb

/-- The balanced site template (`siteGate P defaultRule`). -/
def balancedTemplate (controlled : Bool) : Template :=
  let fb : Node := .call (dispatcherName controlled) [v "xw", v "zw", v "xCap", v "zCap"]
    [.var "phi"] (dispatcherRArgs controlled)
  { name := balancedName controlled
    wParams := ["xw", "zw", "xCap", "zCap"]
    aParams := ["phi"]
    rParams := if controlled then ["ctrl", "x", "z"] else ["x", "z"]
    body :=
      .cond (.lt (v "zw") (v "xw"))
        (splitBranch controlled (.var "x") (.var "z") (v "xw") (v "zw") (v "xCap") (v "zCap") fb)
        (.cond (.lt (v "xw") (v "zw"))
          (splitBranch controlled (.var "z") (.var "x") (v "zw") (v "xw") (v "zCap") (v "xCap") fb)
          fb)
    provenance := "Shor.Balanced.siteGate with Shor.Balanced.defaultRule (built, not extracted)" }

/-- Rename the dispatcher calls of a node to the balanced templates. -/
partial def retarget : Node → Node
  | .call t w a r =>
      if t == dispatcherName false then .call (balancedName false) w a r
      else if t == dispatcherName true then .call (balancedName true) w a r
      else .call t w a r
  | .seq b => .seq (b.map retarget)
  | .adj b => .adj (retarget b)
  | .cond g x y => .cond g (retarget x) (retarget y)
  | .loop i lo hi b => .loop i lo hi (retarget b)
  | nd => nd

/-- The balanced document: the two templates added, `shor`'s sites retargeted. -/
def balanceDoc (d : Doc) : Doc :=
  { d with templates :=
      d.templates.map (fun t => if t.name == "shor" then { t with body := retarget t.body } else t)
        ++ [balancedTemplate false, balancedTemplate true] }

end Balanced
end IR
end Shor
