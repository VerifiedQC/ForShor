import Lean
import FastMultiplication.Emit.Reflect.Extract

/-!
# The extraction targets

`extractPPBody`: R2.1's target, `Shor.compileOpsToSignedGate` (the `pp_body`
row of `PLAN.md` §5.3's table). Fixed: `k`, `hk`, `ops` (from the given
`TableSource`). Symbolic: `phi` (angle), `x`/`z` (the two operand
registers), and — per the R2.1 spike's Finding 1 — the `layout` argument is
*not* one opaque free variable; it is built from `k` fresh per-child `Reg`
reserve variables plus opaque `Prop`-typed witnesses (`Extract.lean`'s
`appFillingSorry`), so every genuinely-opaque piece is a plain named
variable `RegExpr` can already express.

Per Finding 2, the per-chunk `stInit`/`stFinal` slot values (and their
widths) are *precomputed* here — built the same way `compileOpsToSignedGate`
itself builds them (`initSignedLayoutState`/`targetSignedLayoutState`
applied to the same `layout`/`need`) — and *registered* against the
`IR.RegExpr`/`IR.WExpr` formula each one is already known to equal, rather
than left for `translateReg`/`translateW` to reflectively reverse-engineer
from a `LayoutState.xslot`-projection-of-a-`def`-application chain. The
`Expr`s built here and the ones that actually occur inside the `whnf`'d
`compileOpsToSignedGate` term are defeq by construction (same functions,
same arguments), which is exactly what `isDefEq`-based registry lookup
needs — it does not require them to be syntactically identical.

Other call-chain targets (`phase_product`, `qft`, `shor`, …) are R2.2+ and
are not attempted here: they need `WellFounded.fix`'s `.eq_def` rewrite and
`Nat.casesOn` handling this file does not yet have.
-/

namespace Shor.Reflect

open Lean Lean.Meta

partial def withLocalDeclsAux {α} (names : List Name) (ty : Expr) (acc : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α :=
  match names with
  | [] => k acc
  | n :: rest => withLocalDecl n .default ty fun fv => withLocalDeclsAux rest ty (acc.push fv) k

/-- Introduce `names.length` fresh free variables of type `ty` at once. -/
def withLocalDecls {α} (names : List Name) (ty : Expr) (k : Array Expr → MetaM α) : MetaM α :=
  withLocalDeclsAux names ty #[] k

/-- A literal `Fin k` value at index `i` (`k` and `i` both concrete). -/
def finLit (kE : Expr) (i : Nat) : MetaM Expr := do
  mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, kE])]

/-- One operand side's precomputed per-chunk bookkeeping: `stInit`/`stFinal`
slot `Expr`s (built the same way `compileOpsToSignedGate` builds them) paired
with the `IR.RegExpr`/`IR.WExpr` formula each is already known to equal. -/
structure SideSlots where
  initRegs : Array (Expr × IR.RegExpr)
  initWidths : Array (Expr × IR.WExpr)
  finalRegs : Array (Expr × IR.RegExpr)
  finalWidths : Array (Expr × IR.WExpr)

/-- Precompute side `base` (`x` or `z`, named `varName` in the IR)'s `k`
chunks: chunk `i`'s init slot is `ExtReg.withReserve (phaseChunkActive base k
W i) reserves[i] _`, matching `PhaseSplitLayout.child`/`initSignedLayoutState`
exactly; its final slot is `growExtRegTo` of that, matching
`targetSignedLayoutState`. `widthVar` is this side's own width parameter name
(`"xw"`/`"zw"`) and `nextWidthArgs` the fixed argument list every recognised
`nextWidth` opaque call uses. -/
def precomputeSideSlots (kE wE : Expr) (base : Expr) (varName : String) (widthVar : String)
    (reserves : Array Expr) (reserveNames : List Name) (needE : Expr) (nextWidthArgs : List IR.WExpr)
    (k : Nat) (limbWExpr : IR.WExpr) : MetaM SideSlots := do
  let mut initRegs : Array (Expr × IR.RegExpr) := #[]
  let mut initWidths : Array (Expr × IR.WExpr) := #[]
  let mut finalRegs : Array (Expr × IR.RegExpr) := #[]
  let mut finalWidths : Array (Expr × IR.WExpr) := #[]
  let wworkE ← mkAppM ``Shor.commonNeededWidth #[needE]
  let nextWidthWExpr : IR.WExpr := .opaque "nextWidth" nextWidthArgs
  for i in List.range k do
    let iFin ← finLit kE i
    let activeE ← mkAppM ``Shor.phaseChunkActive #[base, kE, wE, iFin]
    let initE ← appFillingSorry ``Shor.ExtReg.withReserve #[some activeE, some reserves[i]!, none]
    let loW : IR.WExpr := .mul (.lit i) limbWExpr
    let widthW : IR.WExpr := if i + 1 = k then .sub (.var widthVar) loW else limbWExpr
    let hiW := IR.WExpr.add loW widthW
    let initRegExpr : IR.RegExpr :=
      .ext (.activeSlice (.var varName) loW hiW) (.var (toString reserveNames[i]!))
    initRegs := initRegs.push (initE, initRegExpr)
    initWidths := initWidths.push ((← mkAppM ``Shor.ExtReg.width #[initE]), widthW)
    let finalE ← mkAppM ``Shor.growExtRegTo #[initE, wworkE]
    let finalRegExpr : IR.RegExpr := .grow initRegExpr (.sub nextWidthWExpr widthW)
    finalRegs := finalRegs.push (finalE, finalRegExpr)
    finalWidths := finalWidths.push ((← mkAppM ``Shor.ExtReg.width #[finalE]), nextWidthWExpr)
  return { initRegs, initWidths, finalRegs, finalWidths }

/-- Extract the `pp_body` template: `compileOpsToSignedGate` specialised at
concrete `k`/`TableSource`, symbolic in `phi, x, z` (and, internally, the
layout's per-child reserves). -/
def extractPPBody (k : Nat) (hk : 1 < k) (src : Shor.TableSource) : MetaM IR.Template := do
  let ops := (Shor.tableInstance src k hk).ops
  let opsE : Expr := Lean.toExpr ops
  let kE : Expr := Lean.toExpr k
  let hkE ← mkDecideProof (← mkAppM ``LT.lt #[Lean.toExpr (1 : Nat), kE])
  let angleTy : Expr := mkConst ``Shor.Angle
  let extRegTy : Expr := mkConst ``Shor.ExtReg
  let regTy : Expr := mkConst ``Shor.Reg
  let finKTy ← mkAppM ``Fin #[kE]
  let idx := List.range k
  let xReserveNames := idx.map (fun i => Name.mkSimple s!"x{i}R")
  let zReserveNames := idx.map (fun i => Name.mkSimple s!"z{i}R")
  withLocalDecl `phi .default angleTy fun phi =>
  withLocalDecl `x .default extRegTy fun x =>
  withLocalDecl `z .default extRegTy fun z =>
  withLocalDecls xReserveNames regTy fun xReserves =>
  withLocalDecls zReserveNames regTy fun zReserves => do
    let wE ← mkAppM ``Shor.phaseLimbWidth #[x, z, kE]
    let xReserveFn ← buildFinFn finKTy regTy xReserves
    let zReserveFn ← buildFinFn finKTy regTy zReserves
    let xSplit ← appFillingSorry ``Shor.PhaseSplitLayout.mk
      #[some x, some kE, some wE, none, some xReserveFn, none, none, none]
    let zSplit ← appFillingSorry ``Shor.PhaseSplitLayout.mk
      #[some z, some kE, some wE, none, some zReserveFn, none, none, none]
    let layout ← appFillingSorry ``Shor.Gate.PhaseProductLayout.mk
      #[some x, some z, some kE, some xSplit, some zSplit, none]
    let qkE ← mkAppM ``Shor.q #[kE]
    let phaseCoeffTy ← mkArrow (← mkAppM ``Fin #[qkE]) (mkConst ``Rat)
    withLocalDecl `phaseCoeff .default phaseCoeffTy fun phaseCoeff => do
      let xwE ← mkAppM ``Shor.ExtReg.width #[x]
      let zwE ← mkAppM ``Shor.ExtReg.width #[z]
      let widths0 : Array (Expr × IR.WExpr) := #[(xwE, .var "xw"), (zwE, .var "zw")]
      let limbWExpr ← translateW { widths := widths0 } wE
      let needE ← mkAppM ``Shor.scanNeededWidths #[x, z, opsE]
      let nextWidthArgs := [IR.WExpr.var "xw", IR.WExpr.var "zw"]
      let xSlots ← precomputeSideSlots kE wE x "x" "xw" xReserves xReserveNames needE
        nextWidthArgs k limbWExpr
      let zSlots ← precomputeSideSlots kE wE z "z" "zw" zReserves zReserveNames needE
        nextWidthArgs k limbWExpr
      let mut regs : Array (Expr × IR.RegExpr) := #[]
      regs := regs.push (x, .var "x")
      regs := regs.push (z, .var "z")
      for i in idx do
        regs := regs.push (xReserves[i]!, .var s!"x{i}R")
        regs := regs.push (zReserves[i]!, .var s!"z{i}R")
      -- Most-specific first: the `stInit`/`stFinal` slots (before the plain
      -- register parameters, which their own construction also mentions).
      regs := xSlots.initRegs ++ xSlots.finalRegs ++ zSlots.initRegs ++ zSlots.finalRegs ++ regs
      let widths := widths0 ++ xSlots.initWidths ++ xSlots.finalWidths ++ zSlots.initWidths ++
        zSlots.finalWidths
      let angles : Array (Expr × IR.AExpr) := #[(phi, .var "phi")]
      let reg : Registry :=
        { regs := regs, widths := widths, angles := angles
          phaseCoeffFVar := phaseCoeff.fvarId!, coeffMExpr := limbWExpr
          nextWidthArgs := nextWidthArgs }
      let app := mkAppN (mkConst ``Shor.compileOpsToSignedGate)
        #[kE, hkE, phi, x, z, layout, phaseCoeff, opsE]
      let body ← translateNode reg app
      return {
        name := "pp_body"
        wParams := ["xw", "zw"]
        aParams := ["phi"]
        rParams := ["x", "z"] ++ xReserveNames.map toString ++ zReserveNames.map toString
        body := body
        provenance := "Shor.compileOpsToSignedGate"
      }

/-- `naive_leaf` (R2.3): `Shor.LowGate.Naive_SignedPhaseProd`. Unlike
`pp_body`, this target takes no `k`/`TableSource` at all — the function
itself doesn't either, so there is nothing to specialise or reflect over:
`naiveSignedPhaseGates phi x z = (signedTerms x).flatMap fun xTerm =>
(signedTerms z).map fun zTerm => CPhase xTerm.1 zTerm.1 (signedPairAngle phi
xTerm zTerm)` is a `List.flatMap`/`List.map` walk over two registers whose
*length* (`x.width`/`z.width`) is symbolic — there is no equation lemma or
`whnf` step that turns "recursion over a symbolic-length list" into a loop
the way `.eq_1` turns `WellFounded.fix` into a visible self-call (§6.2);
generic reflection has nothing to grab onto here. So this instead
recognises `Naive_SignedPhaseProd` by name (D2's translation table is
*keyed* by construct, and a whole function is as much a "construct" as
`Gate.seq` or `ExtReg.grow` are) and states its known double-loop shape
directly, the same escape hatch already used for one sub-formula at a time
(`RegExpr.grow`, `AExpr.signedPair`) — here for the whole leaf. What makes
this trustworthy is the same D7 standard as everywhere else: not written
once and assumed, but checked against the real `Naive_SignedPhaseProd` by
`native_decide` (`Tests.lean`), at several widths. -/
def naiveLeafTemplate : IR.Template :=
  { name := "naive_leaf"
    wParams := ["xw", "zw"]
    aParams := ["phi"]
    rParams := ["x", "z"]
    provenance := "Shor.LowGate.Naive_SignedPhaseProd"
    body :=
      .loop "i" (.lit 0) (.var "xw")
        (.loop "j" (.lit 0) (.var "zw")
          (.op "CPhase" [.qubit (.var "x") (.var "i"), .qubit (.var "z") (.var "j")] []
            (some (.signedPair (.var "phi") (.var "i") (.var "xw") (.var "j") (.var "zw"))) []))
  }

end Shor.Reflect
