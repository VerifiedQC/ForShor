import FastMultiplication.Emit.Reflect.Targets
import FastMultiplication.Emit.Symbolic.Dispatcher

/-!
# Per-band extraction targets

`Targets.lean` extracts one `phase_product` template from one table.
This file extracts one `phase_product_<i>` per *band* of a policy, which the
dispatcher (`Emit/Symbolic/Dispatcher.lean`) routes between.

The body of a band is the body of a table: `Policy.signedPlanOf.eq_2`'s
right-hand side, read through `Policy.canonicalStep`, with the recursive
child left as a `Node.call`. `Targets.lean` already goes through exactly
that route — item 4 of `PLAN_Policy.md` moved the single-table path onto the
policy machinery at `constPolicy` — so what is new here is only *which*
policy and *which* table, and the two hypotheses that supplies.

## The two hypotheses, and why they are local constants

`Policy.signedPlanOf.eq_2` needs

```lean
hchoose : P.choose (phaseInputSize x z) = some T
hws     : Policy.WorkspaceOK P x z
```

With `x` and `z` symbolic, neither is *provable* for a real policy: the first
holds only on band `i`'s own width range, and the second is the caller's
obligation. `Targets.lean` can discharge the first with
`constPolicy_choose` because a constant policy chooses the same table at
every width; a banded policy cannot.

They are introduced as **local constants** (`withLocalDecl`), exactly as
`Targets.lean` already introduces `phi`, `x`, `z` and `hworkspace`. Not
`mkSorry`: a free variable of the right type is what the extractor's registry
is built to walk past, it keeps `sorryAx` out of the produced `Doc`
altogether, and it is the same device the file already uses for every other
symbolic input. (`mkSorry` remains in use for the *branch* hypotheses of a
`dite`, where `Targets.lean` applies a branch function to a proof of a guard
it has just split on; that is unchanged and is local to one `whnfR`.)

What re-establishes `hchoose` is not a proof here but the dispatcher: band
`i`'s body is reachable only under the guard `t_i ≤ max xw zw`, and
`IR.dispatcherCallAt_dispatcherTemplate` proves that guard chain picks band
`i` exactly where `chooseIdx` does. The evaluation tier then instantiates
each body only at widths inside its own band.

## What is *not* parameterised

`T` is passed as the band's own `ShorLoweringSetup`, and `tblE` is rebuilt
from it the way `Targets.lean` rebuilds a setup's table — so the table this
body is extracted from is the table the policy carries at that band, by
construction of `buildPolicyDoc`'s caller rather than by a check here.
-/

namespace Shor.Reflect

open Lean Lean.Meta Shor.IR

/-- `phase_product_<i>`: one band's body.

`polE` is the policy as an `Expr` (in practice
`(someSubmission).policy`, a constant application — never a quoted literal,
since `ShorLoweringPolicy` carries a `sorted` proof field and has no
`ToExpr`). `setup` is band `i`'s table. `i` names the template.

Structurally identical to `extractPhaseProductBody`; see that function for
why each step is the way it is. -/
def extractPolicyPhaseProductBody (polE : Expr) (setup : Shor.ShorLoweringSetup)
    (i : ℕ) (coeffOffset : ℕ) : MetaM IR.Template := do
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
    let (ptsE, hptsE) ← setupPtsExprs setup kE
    let tblE ← mkAppM ``Shor.ToomCookTable.mk #[kE, hkE, ptsE, hptsE, opsE]
    let sizeE ← mkAppM ``Shor.phaseInputSize #[x, z]
    let chooseE ← mkAppM ``Shor.ShorLoweringPolicy.choose #[polE, sizeE]
    let someTE ← mkAppOptM ``Option.some #[mkConst ``Shor.ToomCookTable, tblE]
    let hchooseTy ← mkEq chooseE someTE
    let hwsTy ← mkAppM ``Shor.Policy.WorkspaceOK #[polE, x, z]
    withLocalDecl `hchoose .default hchooseTy fun hchooseE =>
    withLocalDecl `hworkspace .default hwsTy fun hwsPE => do
      let eq1App := mkAppN (mkConst ``Shor.Policy.signedPlanOf.eq_2)
        #[polE, phi, x, z, hwsPE, tblE, hchooseE]
      let rhsPlan := (← inferType eq1App).getAppArgs[2]!
      match rhsPlan.getAppFnArgs with
      | (``dite, #[_, condE, _instE, thenFnE, elseFnE]) =>
          withLocalDecl `hrec .default condE fun hrecW => do
            let stepE ← mkAppM ``Shor.Policy.canonicalStep
              #[polE, tblE, x, z, hchooseE, hrecW, hwsPE]
            let layoutE ← mkAppM ``Shor.Policy.CanonicalStep.layout #[stepE]
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
                nextWidthArgs := [.var "xw", .var "zw"]
                topChunkSlack := do pure (← xSlots.topSlack, ← zSlots.topSlack)
                coeffOffset := coeffOffset }
            let guard ← translateProp reg condE
            let notCond ← mkAppM ``Not #[condE]
            let thenPlan ← whnfR (mkApp thenFnE (← mkSorry condE false))
            let elsePlan ← whnfR (mkApp elseFnE (← mkSorry notCond false))
            let thenLowGate ← mkAppM ``Shor.lowerGateRec #[thenPlan]
            let elseLowGate ← mkAppM ``Shor.lowerGateRec #[elsePlan]
            let elseNode ← translateNode reg elseLowGate
            let thenNode ← translateNode reg thenLowGate
            return {
              name := IR.bandBodyName false i
              wParams := ["xw", "zw", "xCap", "zCap"]
              aParams := ["phi"]
              rParams := ["x", "z"]
              body := .cond guard thenNode elseNode
              provenance := s!"Shor.Policy.stepPlan at band {i} + Shor.lowerGateRec"
            }
      | _ => throwError
          "extractPolicyPhaseProductBody: expected eq_2's RHS to be a dite, got {rhsPlan}"

/-- `cphase_product_<i>`: the controlled twin, with `ctrl` threaded through
exactly as `extractCPhaseProductBody` threads it. -/
def extractPolicyCPhaseProductBody (polE : Expr) (setup : Shor.ShorLoweringSetup)
    (i : ℕ) (coeffOffset : ℕ) : MetaM IR.Template := do
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
    let (ptsE, hptsE) ← setupPtsExprs setup kE
    let tblE ← mkAppM ``Shor.ToomCookTable.mk #[kE, hkE, ptsE, hptsE, opsE]
    let sizeE ← mkAppM ``Shor.phaseInputSize #[x, z]
    let chooseE ← mkAppM ``Shor.ShorLoweringPolicy.choose #[polE, sizeE]
    let someTE ← mkAppOptM ``Option.some #[mkConst ``Shor.ToomCookTable, tblE]
    let hchooseTy ← mkEq chooseE someTE
    let hwsTy ← mkAppM ``Shor.Policy.CWorkspaceOK #[polE, ctrl, x, z]
    withLocalDecl `hchoose .default hchooseTy fun hchooseE =>
    withLocalDecl `hworkspace .default hwsTy fun hwsPE => do
      let eq1App := mkAppN (mkConst ``Shor.Policy.cSignedPlanOf.eq_2)
        #[polE, ctrl, phi, x, z, hwsPE, tblE, hchooseE]
      let rhsPlan := (← inferType eq1App).getAppArgs[2]!
      match rhsPlan.getAppFnArgs with
      | (``dite, #[_, condE, _instE, thenFnE, elseFnE]) =>
          withLocalDecl `hrec .default condE fun hrecW => do
            let stepE ← mkAppM ``Shor.Policy.canonicalStep
              #[polE, tblE, x, z, hchooseE, hrecW,
                (← mkAppM ``Shor.Policy.CWorkspaceOK.toWorkspaceOK #[hwsPE])]
            let layoutE ← mkAppM ``Shor.Policy.CanonicalStep.layout #[stepE]
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
                nextWidthArgs := [.var "xw", .var "zw"]
                topChunkSlack := do pure (← xSlots.topSlack, ← zSlots.topSlack)
                coeffOffset := coeffOffset }
            let guard ← translateProp reg condE
            let notCond ← mkAppM ``Not #[condE]
            let thenPlan ← whnfR (mkApp thenFnE (← mkSorry condE false))
            let elsePlan ← whnfR (mkApp elseFnE (← mkSorry notCond false))
            let thenLowGate ← mkAppM ``Shor.lowerGateRec #[thenPlan]
            let elseLowGate ← mkAppM ``Shor.lowerGateRec #[elsePlan]
            let elseNode ← translateNode reg elseLowGate
            let thenNode ← translateNode reg thenLowGate
            return {
              name := IR.bandBodyName true i
              wParams := ["xw", "zw", "xCap", "zCap"]
              aParams := ["phi"]
              rParams := ["ctrl", "x", "z"]
              body := .cond guard thenNode elseNode
              provenance := s!"Shor.Policy.cStepPlan at band {i} + Shor.lowerGateRec"
            }
      | _ => throwError
          "extractPolicyCPhaseProductBody: expected eq_2's RHS to be a dite, got {rhsPlan}"

/-- `qft` for a policy: `Policy.qftPlan.eq_1`, exactly as
`extractQFTBody` reads it, with the workspace hypothesis a local constant
rather than a conversion from the fixed-table one.

The recursive `phase_product` call at each split comes out of
`translateQFTPlan`'s `Policy.signedPlan` case, which already emits
`call "phase_product"` — so the template reaches the dispatcher with no
change here, and the dispatcher routes the split's (generally unequal)
operand widths to whichever band covers their `max`. -/
def extractPolicyQFTBody (polE : Expr) : MetaM IR.Template := do
  let regTy : Expr := mkConst ``Shor.Reg
  withLocalDecl `r .default regTy fun r =>
  withLocalDecl `xWork .default regTy fun xWork =>
  withLocalDecl `zWork .default regTy fun zWork => do
    let hworkTy ← mkAppM ``Shor.Policy.QFTWorkspaceOK #[polE, r, xWork, zWork]
    withLocalDecl `hworkspace .default hworkTy fun hwsPE => do
      let eq1App := mkAppN (mkConst ``Shor.Policy.qftPlan.eq_1)
        #[polE, r, xWork, zWork, hwsPE]
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
                provenance := "Shor.Policy.qftPlan + Shor.lowerQFTPlan"
              }
          | _ => throwError "extractPolicyQFTBody: expected inner branch to be a dite, got {innerApp}"
      | _ => throwError "extractPolicyQFTBody: expected eq_1's RHS to be a dite, got {rhsOuter}"

/-- `shor` for a policy.

`extractShorBody` uses its `ops` for exactly one thing — carving the QFT
workspace at a `Gate.QFT` node — so the policy version is the same walk with
`QFTWorkSource.ofPolicy`. Every other node, `phase_product` and
`cphase_product` among them, is emitted by name and so reaches the dispatcher
unchanged. -/
def extractPolicyShorBody (polE : Expr) : MetaM IR.Template := do
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
      let node ← translateLowerGate reg (QFTWorkSource.ofPolicy polE) gE
      return {
        name := "shor"
        wParams := ["a", "N", "xW", "xCap", "yW", "yCap", "workW", "workCap", "scratchW", "scratchCap"]
        aParams := []
        rParams := ["x", "y", "work", "scratch", "flag"]
        body := node
        provenance := "Shor.Policy.lowerGate ∘ Shor.orderFindingApprox"
      }

end Shor.Reflect
