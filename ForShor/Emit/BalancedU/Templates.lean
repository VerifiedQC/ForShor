import ForShor.Emit.Balanced.Templates

/-!
# Unconditionally balanced phase products in the IR

`Shor.Balanced.balanceU` (Implementation/Reference/Balanced/Unconditional.lean) rewrites
every Shor-level phase-product site through `siteGateU` with `defaultRule`: `siteGate`
without the fit check `fitsB`. Its IR form is two built templates with the dispatchers'
signature, as in `Emit/Balanced/Templates.lean`:

* `balanced_u_phase_product`  — wParams `[xw, zw, xCap, zCap]`, aParams `[phi]`, rParams `[x, z]`;
* `balanced_u_cphase_product` — the same with rParams `[ctrl, x, z]`.

Their body is `siteGateU defaultRule c φ x z`: the block nodes of the balanced templates
(`topNode`, `lowNode`), with no guard on the reserves. The original site is kept only where
`defaultPlan` has no plan (equal widths, or a narrow operand under two bits).

`balanceUDoc` adds the two templates and retargets the `shor` template's calls to
`phase_product`/`cphase_product` (the Steps 1, 2, 4, 5 sites) to them; `qft` and `shor_gate`
are unchanged.

Agreement with the real lowering is checked by evaluation (`Emit/BalancedU/Verify.lean`), not
proved.
-/

namespace Shor
namespace IR
namespace BalancedU

open IR.Balanced

def balancedUName (controlled : Bool) : String :=
  if controlled then "balanced_u_cphase_product" else "balanced_u_phase_product"

private def n (k : ℕ) : WExpr := .lit k
private def pow2 (e : WExpr) : WExpr := .opaque "pow" [.lit 2, e]

/-- `siteGateU`'s split with `X` the wider operand (width `L`, capacity `LC`) and `Z` the
narrower (`s`, `SC`), following `defaultPlan L s`. -/
def splitBranchU (controlled : Bool) (X Z : RegExpr) (L s LC SC : WExpr) (fb : Node) : Node :=
  let phi := AExpr.var "phi"
  -- padding: plan ⟨[], L⟩
  let padNode := topNode controlled X Z L s LC SC L phi
  -- blocks: B = ⌈L/s⌉, w = s - 1, top = L - (B-1)w, t = max s top
  let B := WExpr.div (.add L (.sub s (n 1))) s
  let w := WExpr.sub s (n 1)
  let off := WExpr.mul (.sub B (n 1)) w
  let top := WExpr.sub L off
  let t := WExpr.max s top
  let topBlock := topNode controlled (blockReg X off L LC) Z top s LC SC t
    (.mul phi (pow2 off))
  let withLower := Node.seq [ .loop "i" (n 0) (.sub B (n 1))
      (lowNode controlled X Z (.mul (.var "i") w) w s LC SC t (.mul phi (pow2 (.mul (.var "i") w)))),
    topBlock ]
  let blocksNode := Node.cond (.le (n 2) B) withLower topBlock
  .cond (.le (n 2) s) (.cond (.le (.mul (n 2) L) (.mul (n 3) s)) padNode blocksNode) fb

/-- The unconditionally balanced site template (`siteGateU defaultRule`). -/
def balancedUTemplate (controlled : Bool) : Template :=
  let fb : Node := .call (dispatcherName controlled) [.var "xw", .var "zw", .var "xCap", .var "zCap"]
    [.var "phi"] (dispatcherRArgs controlled)
  { name := balancedUName controlled
    wParams := ["xw", "zw", "xCap", "zCap"]
    aParams := ["phi"]
    rParams := if controlled then ["ctrl", "x", "z"] else ["x", "z"]
    body :=
      .cond (.lt (.var "zw") (.var "xw"))
        (splitBranchU controlled (.var "x") (.var "z") (.var "xw") (.var "zw") (.var "xCap")
          (.var "zCap") fb)
        (.cond (.lt (.var "xw") (.var "zw"))
          (splitBranchU controlled (.var "z") (.var "x") (.var "zw") (.var "xw") (.var "zCap")
            (.var "xCap") fb)
          fb)
    provenance := "Shor.Balanced.siteGateU with Shor.Balanced.defaultRule (built, not extracted)" }

/-- Rename the dispatcher calls of a node to the unconditionally balanced templates. -/
partial def retargetU : Node → Node
  | .call t w a r =>
      if t == dispatcherName false then .call (balancedUName false) w a r
      else if t == dispatcherName true then .call (balancedUName true) w a r
      else .call t w a r
  | .seq b => .seq (b.map retargetU)
  | .adj b => .adj (retargetU b)
  | .cond g x y => .cond g (retargetU x) (retargetU y)
  | .loop i lo hi b => .loop i lo hi (retargetU b)
  | nd => nd

/-- The unconditionally balanced document: the two templates added, `shor`'s sites retargeted. -/
def balanceUDoc (d : Doc) : Doc :=
  { d with templates :=
      d.templates.map (fun t => if t.name == "shor" then { t with body := retargetU t.body } else t)
        ++ [balancedUTemplate false, balancedUTemplate true] }

end BalancedU
end IR
end Shor
