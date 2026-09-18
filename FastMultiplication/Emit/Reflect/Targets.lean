import Lean
import FastMultiplication.Emit.Reflect.Extract
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup

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

/-- `phase_product`'s per-side reserve-split bookkeeping. Unlike `pp_body`'s
`layout` (hand-built from fresh reserve variables, Finding 1),
`canonicalSignedStep`'s layout is the *real* deterministic construction
(`ReserveBudget.ofRequirements`/`fillSlack`, driven by the opaque
`reserveNeed`) — reflecting through its tactic-mode definition gets stuck
the same way `LayoutState.xslot`-composed-with-a-`def` did in R2.1 (a
projection chain, not the outer head, is what's stuck; confirmed by a spike
before writing this). Same fix as Finding 2: precompute the ground-truth
`Expr` (`step.layout.xSplit.child i`, built by calling the real functions)
and register it against a hand-computed `RegExpr`/`WExpr` formula that
replicates `requiredChildReserve`/`fillSlack`'s arithmetic —
`fillSlack`'s "give all slack to the last child" policy means the `i`-th
child's reserve *offset* is always `sum_{j<i} required[j]` (the top index
is never among the `j < i` terms, since `i ≤ k - 1`), and only the *size*
of the last child differs (`required[k-1] + (capacity - sum_all
required)`). `capVar` names this side's reserve *capacity* (`x.capacity`),
a width parameter `pp_body` never needed. -/
def precomputePhaseProductSlots (opsE xE zE layoutE : Expr) (childFieldName : Name) (varName : String)
    (widthVar capVar reserveNeedName : String) (k : Nat) (limbWExpr : IR.WExpr) :
    MetaM SideSlots := do
  let mut initRegs : Array (Expr × IR.RegExpr) := #[]
  let mut initWidths : Array (Expr × IR.WExpr) := #[]
  let mut finalRegs : Array (Expr × IR.RegExpr) := #[]
  let mut finalWidths : Array (Expr × IR.WExpr) := #[]
  let nextWidthWExpr : IR.WExpr := .opaque "nextWidth" [.var "xw", .var "zw"]
  let reserveNeedWExpr : IR.WExpr := .opaque reserveNeedName [nextWidthWExpr, nextWidthWExpr]
  let widthAt (j : Nat) : IR.WExpr :=
    let lo := IR.WExpr.mul (.lit j) limbWExpr
    if j + 1 = k then IR.WExpr.sub (.var widthVar) lo else limbWExpr
  let requiredAt (j : Nat) : IR.WExpr :=
    IR.WExpr.add (IR.WExpr.sub nextWidthWExpr (widthAt j)) reserveNeedWExpr
  let requiredArr : Array IR.WExpr := ((List.range k).map requiredAt).toArray
  let sumRange (lo hi : Nat) : IR.WExpr :=
    (List.range (hi - lo)).foldl (fun acc j => IR.WExpr.add acc (requiredArr.getD (lo + j) (IR.WExpr.lit 0))) (IR.WExpr.lit 0)
  let usedW := sumRange 0 k
  let splitE ← mkAppM childFieldName #[layoutE]
  let needE ← mkAppM ``Shor.scanNeededWidths #[xE, zE, opsE]
  let wworkE ← mkAppM ``Shor.commonNeededWidth #[needE]
  for i in List.range k do
    let iFin ← finLit (Lean.toExpr k) i
    let childE ← mkAppM ``Shor.PhaseSplitLayout.child #[splitE, iFin]
    let loW := IR.WExpr.mul (.lit i) limbWExpr
    let widthW := widthAt i
    let hiW := IR.WExpr.add loW widthW
    let offsetW := sumRange 0 i
    let sizeW :=
      if i + 1 = k then IR.WExpr.add (requiredArr.getD i (IR.WExpr.lit 0)) (IR.WExpr.sub (.var capVar) usedW)
      else (requiredArr.getD i (IR.WExpr.lit 0))
    let initRegExpr : IR.RegExpr :=
      .ext (.activeSlice (.var varName) loW hiW)
        (.reserveSlice (.var varName) offsetW (IR.WExpr.add offsetW sizeW))
    initRegs := initRegs.push (childE, initRegExpr)
    initWidths := initWidths.push ((← mkAppM ``Shor.ExtReg.width #[childE]), widthW)
    let finalE ← mkAppM ``Shor.growExtRegTo #[childE, wworkE]
    let finalRegExpr : IR.RegExpr := .grow initRegExpr (IR.WExpr.sub nextWidthWExpr widthW)
    finalRegs := finalRegs.push (finalE, finalRegExpr)
    finalWidths := finalWidths.push ((← mkAppM ``Shor.ExtReg.width #[finalE]), nextWidthWExpr)
  return { initRegs, initWidths, finalRegs, finalWidths }

/-- Extract the `pp_body` template: `compileOpsToSignedGate` specialised at
the given table (`Emit/PLAN.md` R5: any `ShorLoweringSetup`, not a `(k,
TableSource)` pair — `setup.consumes`/`setup.returns` are exactly what makes
`setup.ops` a table the lowering theorems cover), symbolic in `phi, x, z`
(and, internally, the layout's per-child reserves). -/
def extractPPBody (setup : Shor.ShorLoweringSetup) : MetaM IR.Template := do
  let k := setup.k
  let ops := setup.ops
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

/-- `naive_cleaf` (R2.4): `LowGate.Naive_CSignedPhaseProd`'s controlled
counterpart of `naive_leaf` — same double loop, `CCPhase` instead of
`CPhase`. `ctrl` is a bare qubit index in the real source
(`naiveCSignedPhaseGates ctrl phi x z`), not sliced from any register, but
per `IR/Instantiate.lean`'s `buildLowGate` convention (`CSignedPhaseProd`'s
`ctrl` already established this) it is still a register parameter carrying
a single-qubit `ExtReg`, going through the same `RegExpr.qubit`/`ExtReg.
singleQubit?` path as every other qubit-shaped operand — not a width
parameter, even though it is Nat-valued underneath. -/
def naiveCLeafTemplate : IR.Template :=
  { name := "naive_cleaf"
    wParams := ["xw", "zw"]
    aParams := ["phi"]
    rParams := ["ctrl", "x", "z"]
    provenance := "Shor.LowGate.Naive_CSignedPhaseProd"
    body :=
      .loop "i" (.lit 0) (.var "xw")
        (.loop "j" (.lit 0) (.var "zw")
          (.op "CCPhase"
            [.var "ctrl", .qubit (.var "x") (.var "i"), .qubit (.var "z") (.var "j")] []
            (some (.signedPair (.var "phi") (.var "i") (.var "xw") (.var "j") (.var "zw"))) []))
  }

/-- `phase_product` (R2.2): `standardSignedPhaseLoweringPlan` + `lowerGateRec`
(`PLAN.md` §5.3/§6.2). Symbolic: `phi, x, z`; `xCap`/`zCap` (`x`/`z`'s
*reserve* capacity — new width parameters `pp_body` never needed, since
`canonicalSignedStep`'s reserve split, unlike `pp_body`'s hand-built
`layout`, is a real formula over the parent's actual capacity). Unfolds
`standardSignedPhaseLoweringPlan`'s `.eq_1` exactly once here (D3: one
activation), exposing the recursion guard as `Node.cond` and both branches
as `lowerGateRec` applied to the (now concrete-headed) step/base plan value;
`translateNode` recognises any *further* `lowerGateRec
(standardSignedPhaseLoweringPlan …)` it walks into as the self-call — by
construction those can only be nested occurrences, since this is the only
place the `.eq_1` unfold itself happens. Table-generic (R5): any
`ShorLoweringSetup`. -/
def extractPhaseProductBody (setup : Shor.ShorLoweringSetup) : MetaM IR.Template := do
  let k := setup.k
  let ops := setup.ops
  let opsE : Expr := Lean.toExpr ops
  let kE : Expr := Lean.toExpr k
  let hkE ← mkDecideProof (← mkAppM ``LT.lt #[Lean.toExpr (1 : Nat), kE])
  let angleTy : Expr := mkConst ``Shor.Angle
  let extRegTy : Expr := mkConst ``Shor.ExtReg
  withLocalDecl `phi .default angleTy fun phi =>
  withLocalDecl `x .default extRegTy fun x =>
  withLocalDecl `z .default extRegTy fun z => do
    let hworkTy ← mkAppM ``Shor.SignedRecursiveWorkspaceOK #[opsE, x, z]
    withLocalDecl `hworkspace .default hworkTy fun hworkspace => do
      let eq1App := mkAppN (mkConst ``Shor.standardSignedPhaseLoweringPlan.eq_1)
        #[kE, hkE, phi, x, z, opsE, hworkspace]
      let rhsPlan := (← inferType eq1App).getAppArgs[2]!
      match rhsPlan.getAppFnArgs with
      | (``dite, #[_, condE, _instE, thenFnE, elseFnE]) =>
          withLocalDecl `hrec .default condE fun hrecW => do
            let stepE ← mkAppM ``Shor.canonicalSignedStep #[hkE, opsE, x, z, hrecW, hworkspace]
            let layoutE ← mkAppM ``Shor.CanonicalSignedStep.layout #[stepE]
            let xwE ← mkAppM ``Shor.ExtReg.width #[x]
            let zwE ← mkAppM ``Shor.ExtReg.width #[z]
            let xCapE ← mkAppM ``Shor.ExtReg.capacity #[x]
            let zCapE ← mkAppM ``Shor.ExtReg.capacity #[z]
            let wE ← mkAppM ``Shor.phaseLimbWidth #[x, z, kE]
            let widths0 : Array (Expr × IR.WExpr) :=
              #[(xwE, .var "xw"), (zwE, .var "zw"), (xCapE, .var "xCap"), (zCapE, .var "zCap")]
            let limbWExpr ← translateW { widths := widths0 } wE
            let xSlots ← precomputePhaseProductSlots opsE x z layoutE
              ``Shor.Gate.PhaseProductLayout.xSplit "x" "xw" "xCap" "reserveNeed_x" k limbWExpr
            let zSlots ← precomputePhaseProductSlots opsE x z layoutE
              ``Shor.Gate.PhaseProductLayout.zSplit "z" "zw" "zCap" "reserveNeed_z" k limbWExpr
            let mut regs : Array (Expr × IR.RegExpr) := #[(x, .var "x"), (z, .var "z")]
            regs := xSlots.initRegs ++ xSlots.finalRegs ++ zSlots.initRegs ++ zSlots.finalRegs ++ regs
            let widths := widths0 ++ xSlots.initWidths ++ xSlots.finalWidths ++ zSlots.initWidths ++
              zSlots.finalWidths
            let angles : Array (Expr × IR.AExpr) := #[(phi, .var "phi")]
            let reg : Registry :=
              { regs := regs, widths := widths, angles := angles
                phaseCoeffFVar := none, coeffMExpr := limbWExpr
                nextWidthArgs := [.var "xw", .var "zw"] }
            let guard ← translateProp reg condE
            let notCond ← mkAppM ``Not #[condE]
            let thenPlan ← whnfR (mkApp thenFnE (← mkSorry condE false))
            let elsePlan ← whnfR (mkApp elseFnE (← mkSorry notCond false))
            let thenLowGate ← mkAppM ``Shor.lowerGateRec #[thenPlan]
            let elseLowGate ← mkAppM ``Shor.lowerGateRec #[elsePlan]
            let elseNode ← translateNode reg elseLowGate
            let thenNode ← translateNode reg thenLowGate
            return {
              name := "phase_product"
              wParams := ["xw", "zw", "xCap", "zCap"]
              aParams := ["phi"]
              rParams := ["x", "z"]
              body := .cond guard thenNode elseNode
              provenance := "Shor.standardSignedPhaseLoweringPlan + Shor.lowerGateRec"
            }
      | _ => throwError "extractPhaseProductBody: expected .eq_1's RHS to be a dite, got {rhsPlan}"

/-- `cphase_product` (R2.4): `standardCSignedPhaseLoweringPlan` +
`lowerGateRec`, the controlled counterpart of `extractPhaseProductBody`.
Identical structure throughout — same guard (`nextSignedWidth x z ops <
phaseInputSize x z`, `ctrl` plays no part in it), same reserve-split
bookkeeping (`precomputePhaseProductSlots`, unaware of `ctrl` since only the
*phase* leaves are controlled, not the allocation/deallocation gates) —
with `ctrl : ℕ` threaded through as an extra free variable, registered
against `RegExpr.var "ctrl"` exactly like `x`/`z` even though its Lean type
is `ℕ`, not `ExtReg` (`translateReg`/`Extract.lean`'s registry never
inspects a candidate's type, only its shape — see the `Naive_CSignedPhaseProd`
case's doc comment). Table-generic (R5): any `ShorLoweringSetup`. -/
def extractCPhaseProductBody (setup : Shor.ShorLoweringSetup) : MetaM IR.Template := do
  let k := setup.k
  let ops := setup.ops
  let opsE : Expr := Lean.toExpr ops
  let kE : Expr := Lean.toExpr k
  let hkE ← mkDecideProof (← mkAppM ``LT.lt #[Lean.toExpr (1 : Nat), kE])
  let angleTy : Expr := mkConst ``Shor.Angle
  let extRegTy : Expr := mkConst ``Shor.ExtReg
  withLocalDecl `ctrl .default (mkConst ``Nat) fun ctrl =>
  withLocalDecl `phi .default angleTy fun phi =>
  withLocalDecl `x .default extRegTy fun x =>
  withLocalDecl `z .default extRegTy fun z => do
    let hworkTy ← mkAppM ``Shor.CSignedRecursiveWorkspaceOK #[opsE, ctrl, x, z]
    withLocalDecl `hworkspace .default hworkTy fun hworkspace => do
      let eq1App := mkAppN (mkConst ``Shor.standardCSignedPhaseLoweringPlan.eq_1)
        #[kE, hkE, ctrl, phi, x, z, opsE, hworkspace]
      let rhsPlan := (← inferType eq1App).getAppArgs[2]!
      match rhsPlan.getAppFnArgs with
      | (``dite, #[_, condE, _instE, thenFnE, elseFnE]) =>
          withLocalDecl `hrec .default condE fun hrecW => do
            let stepE ← mkAppM ``Shor.canonicalSignedStep #[hkE, opsE, x, z, hrecW,
              (← mkAppM ``Shor.CSignedRecursiveWorkspaceOK.toSignedRecursiveWorkspaceOK
                #[hworkspace])]
            let layoutE ← mkAppM ``Shor.CanonicalSignedStep.layout #[stepE]
            let xwE ← mkAppM ``Shor.ExtReg.width #[x]
            let zwE ← mkAppM ``Shor.ExtReg.width #[z]
            let xCapE ← mkAppM ``Shor.ExtReg.capacity #[x]
            let zCapE ← mkAppM ``Shor.ExtReg.capacity #[z]
            let wE ← mkAppM ``Shor.phaseLimbWidth #[x, z, kE]
            let widths0 : Array (Expr × IR.WExpr) :=
              #[(xwE, .var "xw"), (zwE, .var "zw"), (xCapE, .var "xCap"), (zCapE, .var "zCap")]
            let limbWExpr ← translateW { widths := widths0 } wE
            let xSlots ← precomputePhaseProductSlots opsE x z layoutE
              ``Shor.Gate.PhaseProductLayout.xSplit "x" "xw" "xCap" "reserveNeed_x" k limbWExpr
            let zSlots ← precomputePhaseProductSlots opsE x z layoutE
              ``Shor.Gate.PhaseProductLayout.zSplit "z" "zw" "zCap" "reserveNeed_z" k limbWExpr
            let mut regs : Array (Expr × IR.RegExpr) := #[(ctrl, .var "ctrl"), (x, .var "x"),
              (z, .var "z")]
            regs := xSlots.initRegs ++ xSlots.finalRegs ++ zSlots.initRegs ++ zSlots.finalRegs ++ regs
            let widths := widths0 ++ xSlots.initWidths ++ xSlots.finalWidths ++ zSlots.initWidths ++
              zSlots.finalWidths
            let angles : Array (Expr × IR.AExpr) := #[(phi, .var "phi")]
            let reg : Registry :=
              { regs := regs, widths := widths, angles := angles
                phaseCoeffFVar := none, coeffMExpr := limbWExpr
                nextWidthArgs := [.var "xw", .var "zw"] }
            let guard ← translateProp reg condE
            let notCond ← mkAppM ``Not #[condE]
            let thenPlan ← whnfR (mkApp thenFnE (← mkSorry condE false))
            let elsePlan ← whnfR (mkApp elseFnE (← mkSorry notCond false))
            let thenLowGate ← mkAppM ``Shor.lowerGateRec #[thenPlan]
            let elseLowGate ← mkAppM ``Shor.lowerGateRec #[elsePlan]
            let elseNode ← translateNode reg elseLowGate
            let thenNode ← translateNode reg thenLowGate
            return {
              name := "cphase_product"
              wParams := ["xw", "zw", "xCap", "zCap"]
              aParams := ["phi"]
              rParams := ["ctrl", "x", "z"]
              body := .cond guard thenNode elseNode
              provenance := "Shor.standardCSignedPhaseLoweringPlan + Shor.lowerGateRec"
            }
      | _ => throwError "extractCPhaseProductBody: expected .eq_1's RHS to be a dite, got {rhsPlan}"

/-- `qft` (R2.5): `standardQFTLoweringPlan` + `lowerQFTPlan`. Symbolic: `r`
(the register being transformed) and `xWork`/`zWork` (the two fixed
workspace pools, threaded through unchanged across the whole recursion —
`QFTWorkspaceOK.phaseWorkspace` reuses them verbatim as each level's own
`xReserve`/`zReserve`, never re-splitting them). Three-way `by_cases`
(`regSize r = 0` / `= 1` / recurse), so `.eq_1` exposes one `dite` nested
inside another; each branch of the outer is `whnfR`'d/applied the same way
`extractPhaseProductBody` does for its single `dite`. Table-generic (R5):
any `ShorLoweringSetup`. -/
def extractQFTBody (setup : Shor.ShorLoweringSetup) : MetaM IR.Template := do
  let k := setup.k
  let ops := setup.ops
  let opsE : Expr := Lean.toExpr ops
  let kE : Expr := Lean.toExpr k
  let hkE ← mkDecideProof (← mkAppM ``LT.lt #[Lean.toExpr (1 : Nat), kE])
  let regTy : Expr := mkConst ``Shor.Reg
  withLocalDecl `r .default regTy fun r =>
  withLocalDecl `xWork .default regTy fun xWork =>
  withLocalDecl `zWork .default regTy fun zWork => do
    let hworkTy ← mkAppM ``Shor.QFTWorkspaceOK #[opsE, r, xWork, zWork]
    withLocalDecl `hworkspace .default hworkTy fun hworkspace => do
      let eq1App := mkAppN (mkConst ``Shor.standardQFTLoweringPlan.eq_1)
        #[kE, hkE, opsE, r, xWork, zWork, hworkspace]
      let rhsOuter := (← inferType eq1App).getAppArgs[2]!
      match rhsOuter.getAppFnArgs with
      | (``dite, #[_, condZeroE, _instZ, thenZeroFnE, elseZeroFnE]) => do
          let notZeroE ← mkAppM ``Not #[condZeroE]
          let innerApp ← whnfR (mkApp elseZeroFnE (← mkSorry notZeroE false))
          match innerApp.getAppFnArgs with
          | (``dite, #[_, condOneE, _instO, thenOneFnE, elseOneFnE]) => do
              let wE ← mkAppM ``Shor.regSize #[r]
              let xWorkWE ← mkAppM ``Shor.regSize #[xWork]
              let zWorkWE ← mkAppM ``Shor.regSize #[zWork]
              let widths0 : Array (Expr × IR.WExpr) :=
                #[(wE, .var "w"), (xWorkWE, .var "xWorkW"), (zWorkWE, .var "zWorkW")]
              let regs0 : Array (Expr × IR.RegExpr) :=
                #[(r, .var "r"), (xWork, .var "xWork"), (zWork, .var "zWork")]
              let reg : Registry :=
                { regs := regs0, widths := widths0, angles := #[]
                  phaseCoeffFVar := none, coeffMExpr := .lit 0
                  nextWidthArgs := [] }
              let guardZero ← translateProp reg condZeroE
              let guardOne ← translateProp reg condOneE
              let emptyPlan ← whnfR (mkApp thenZeroFnE (← mkSorry condZeroE false))
              let notOneE ← mkAppM ``Not #[condOneE]
              let singletonPlan ← whnfR (mkApp thenOneFnE (← mkSorry condOneE false))
              let splitPlan ← whnfR (mkApp elseOneFnE (← mkSorry notOneE false))
              let emptyNode ← translateQFTPlan reg emptyPlan
              let singletonNode ← translateQFTPlan reg singletonPlan
              let splitNode ← translateQFTPlan reg splitPlan
              return {
                name := "qft"
                wParams := ["w", "xWorkW", "zWorkW"]
                aParams := []
                rParams := ["r", "xWork", "zWork"]
                body := .cond guardZero emptyNode (.cond guardOne singletonNode splitNode)
                provenance := "Shor.standardQFTLoweringPlan + Shor.lowerQFTPlan"
              }
          | _ => throwError "extractQFTBody: expected inner .eq_1 branch to be a dite, got {innerApp}"
      | _ => throwError "extractQFTBody: expected .eq_1's RHS to be a dite, got {rhsOuter}"

/-- R2.6's `shor_gate` target: `Shor.orderFindingApprox`, `Gate`-valued and
entirely table-independent (no `k`/`hk`/`ops`, unlike every earlier target —
it is built before any lowering plan exists). A plain (non-tactic-mode) `def`
applied directly to free variables, so — unlike `qft` above — no `.eq_1`
unfolding is needed at all: `translateNode` walks the whole body in one call,
its own `unfoldDefinition?`/named-construct machinery doing all the work
(`H_reg`, `initY1`, `modExpApproxValid`'s per-exponent-bit loop, Algorithm
1's five `CmodMulInPlaceCore` steps, …). -/
def extractShorGateBody : MetaM IR.Template := do
  let natTy : Expr := mkConst ``Nat
  let regTy : Expr := mkConst ``Shor.ExtReg
  withLocalDecl `a .default natTy fun a =>
  withLocalDecl `N .default natTy fun N =>
  withLocalDecl `x .default regTy fun x =>
  withLocalDecl `y .default regTy fun y =>
  withLocalDecl `work .default regTy fun work =>
  withLocalDecl `scratch .default regTy fun scratch =>
  withLocalDecl `flag .default natTy fun flag => do
    let hworkTy ← mkAppM ``Shor.ModMulCircuitWorkspaceOK #[y, work]
    withLocalDecl `hworkspace .default hworkTy fun hworkspace => do
    let yGrow1 ← mkAppM ``Shor.ExtReg.grow #[y, mkNatLit 1]
    let hstep4Ty ← mkAppM ``Shor.CmpLtNWWorkspace #[N, yGrow1, work, scratch, flag]
    withLocalDecl `hstep4 .default hstep4Ty fun hstep4 => do
      let regs : Array (Expr × IR.RegExpr) :=
        #[(x, .var "x"), (y, .var "y"), (work, .var "work"), (scratch, .var "scratch"),
          (flag, .var "flag")]
      let xW ← mkAppM ``Shor.ExtReg.width #[x]
      let xCap ← mkAppM ``Shor.ExtReg.capacity #[x]
      let yW ← mkAppM ``Shor.ExtReg.width #[y]
      let yCap ← mkAppM ``Shor.ExtReg.capacity #[y]
      let workW ← mkAppM ``Shor.ExtReg.width #[work]
      let workCap ← mkAppM ``Shor.ExtReg.capacity #[work]
      let scratchW ← mkAppM ``Shor.ExtReg.width #[scratch]
      let scratchCap ← mkAppM ``Shor.ExtReg.capacity #[scratch]
      let widths : Array (Expr × IR.WExpr) :=
        #[(a, .var "a"), (N, .var "N"), (xW, .var "xW"), (xCap, .var "xCap"),
          (yW, .var "yW"), (yCap, .var "yCap"), (workW, .var "workW"), (workCap, .var "workCap"),
          (scratchW, .var "scratchW"), (scratchCap, .var "scratchCap")]
      let reg : Registry :=
        { regs := regs, widths := widths, angles := #[]
          phaseCoeffFVar := none, coeffMExpr := .lit 0, nextWidthArgs := [] }
      let bodyE ← mkAppM ``Shor.orderFindingApprox
        #[a, N, x, y, work, scratch, flag, hworkspace, hstep4]
      let node ← translateNode reg bodyE
      return {
        name := "shor_gate"
        wParams := ["a", "N", "xW", "xCap", "yW", "yCap", "workW", "workCap", "scratchW", "scratchCap"]
        aParams := []
        rParams := ["x", "y", "work", "scratch", "flag"]
        body := node
        provenance := "Shor.orderFindingApprox"
      }

/-- R2.6's `shor` target: `Shor.lowerGate k hk ops (orderFindingApprox …)
hLowerWorkspace`, `referenceShorCircuit`'s whole body once `allocateReferenceLayout`'s
concrete registers/`k` are supplied — the exit criterion instantiates this at
`k, hk, ops` fixed exactly as `qft`/`phase_product`/`cphase_product` are.
`translateLowerGate` walks the `Gate` structure directly (`orderFindingApprox`
is a plain `def`, no `.eq_1` needed here either); the `Gate.QFT`/
`.SignedPhaseProd`/`.CSignedPhaseProd` leaves it recognises by name become
`Node.call`s into the very templates `qft`/`phase_product`/`cphase_product`
already are, so nothing about the lowering itself is re-derived.
Table-generic (R5): any `ShorLoweringSetup`. -/
def extractShorBody (setup : Shor.ShorLoweringSetup) : MetaM IR.Template := do
  let ops := setup.ops
  let opsE : Expr := Lean.toExpr ops
  let natTy : Expr := mkConst ``Nat
  let regTy : Expr := mkConst ``Shor.ExtReg
  withLocalDecl `a .default natTy fun a =>
  withLocalDecl `N .default natTy fun N =>
  withLocalDecl `x .default regTy fun x =>
  withLocalDecl `y .default regTy fun y =>
  withLocalDecl `work .default regTy fun work =>
  withLocalDecl `scratch .default regTy fun scratch =>
  withLocalDecl `flag .default natTy fun flag => do
    let hworkTy ← mkAppM ``Shor.ModMulCircuitWorkspaceOK #[y, work]
    withLocalDecl `hworkspace .default hworkTy fun hworkspace => do
    let yGrow1 ← mkAppM ``Shor.ExtReg.grow #[y, mkNatLit 1]
    let hstep4Ty ← mkAppM ``Shor.CmpLtNWWorkspace #[N, yGrow1, work, scratch, flag]
    withLocalDecl `hstep4 .default hstep4Ty fun hstep4 => do
      let regs : Array (Expr × IR.RegExpr) :=
        #[(x, .var "x"), (y, .var "y"), (work, .var "work"), (scratch, .var "scratch"),
          (flag, .var "flag")]
      let xW ← mkAppM ``Shor.ExtReg.width #[x]
      let xCap ← mkAppM ``Shor.ExtReg.capacity #[x]
      let yW ← mkAppM ``Shor.ExtReg.width #[y]
      let yCap ← mkAppM ``Shor.ExtReg.capacity #[y]
      let workW ← mkAppM ``Shor.ExtReg.width #[work]
      let workCap ← mkAppM ``Shor.ExtReg.capacity #[work]
      let scratchW ← mkAppM ``Shor.ExtReg.width #[scratch]
      let scratchCap ← mkAppM ``Shor.ExtReg.capacity #[scratch]
      let widths : Array (Expr × IR.WExpr) :=
        #[(a, .var "a"), (N, .var "N"), (xW, .var "xW"), (xCap, .var "xCap"),
          (yW, .var "yW"), (yCap, .var "yCap"), (workW, .var "workW"), (workCap, .var "workCap"),
          (scratchW, .var "scratchW"), (scratchCap, .var "scratchCap")]
      let reg : Registry :=
        { regs := regs, widths := widths, angles := #[]
          phaseCoeffFVar := none, coeffMExpr := .lit 0, nextWidthArgs := [] }
      let gE ← mkAppM ``Shor.orderFindingApprox
        #[a, N, x, y, work, scratch, flag, hworkspace, hstep4]
      let node ← translateLowerGate reg opsE gE
      return {
        name := "shor"
        wParams := ["a", "N", "xW", "xCap", "yW", "yCap", "workW", "workCap", "scratchW", "scratchCap"]
        aParams := []
        rParams := ["x", "y", "work", "scratch", "flag"]
        body := node
        provenance := "Shor.lowerGate ∘ Shor.orderFindingApprox"
      }

end Shor.Reflect
