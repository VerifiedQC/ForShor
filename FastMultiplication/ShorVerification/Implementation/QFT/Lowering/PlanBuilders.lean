import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.QFT.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders

/-!
# QFT Plan Builders

Builds `QFTLoweringPlan`s rather than just interpreting them: the canonical
unsigned phase-product subplan used at each split (`standardPhaseProdUsingPlan`),
and the two public plan constructors, `standardQFTLoweringPlan` (from explicit
workspace registers satisfying `QFTWorkspaceOK`) and `reserveQFTLoweringPlan`
(the bridge from the public reserve precondition `QFTReserveOK` to a concrete
plan, deriving its workspace registers from `qftXWork`/`qftZWork`).
-/

namespace Shor

open Gate
open scoped BigOperators

/-! =========================================================
    Canonical unsigned phase-product subplans

    A split QFT uses an unsigned phase product between the left and right
    halves. This section packages that unsigned gate as a standard
    phase-product lowering plan by zero-extending both operands, lowering the
    resulting signed phase product, and deallocating the extensions.
========================================================= -/

/--
The recursive signed-phase-product input size used by
`Gate.PhaseProdUsing`.
-/
def phaseProdUsingInputSize
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z) :
    ℕ :=
  phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1)

/--
Construct the canonical lowering plan for an unsigned phase product.

The plan follows the definition of `Gate.PhaseProdUsing`:

1. zero-extend `x`;
2. zero-extend `z`;
3. recursively lower the resulting signed phase product;
4. deallocate the `z` extension;
5. deallocate the `x` extension.
-/
def standardPhaseProdUsingPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (phi : Angle)
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace :
      SignedRecursiveWorkspaceOK ops (ws.xExt.grow 1) (ws.zExt.grow 1)) :
    StandardPhaseLoweringPlan k hk ops (phaseProdUsingInputSize ws)
      (Gate.PhaseProdUsing phi x z ws) := by
  let initSize : ℕ := phaseProdUsingInputSize ws
  let xExt : ExtReg := ws.xExt
  let zExt : ExtReg := ws.zExt
  let xSigned : ExtReg := xExt.grow 1
  let zSigned : ExtReg := zExt.grow 1

  let extendXPlan :
      StandardPhaseLoweringPlan k hk ops initSize (Gate.zeroExtend xExt 1) :=
    PhaseLoweringPlan.zeroExtend initSize xExt 1

  let extendZPlan :
      StandardPhaseLoweringPlan k hk ops initSize (Gate.zeroExtend zExt 1) :=
    PhaseLoweringPlan.zeroExtend initSize zExt 1

  let signedPlan :
      StandardPhaseLoweringPlan k hk ops initSize
        (Gate.SignedPhaseProd phi xSigned zSigned) := by
    have hsize : phaseInputSize xSigned zSigned = initSize := by rfl
    simpa [hsize] using
      standardSignedPhaseLoweringPlan k hk phi xSigned zSigned ops hworkspace

  let deallocZPlan :
      StandardPhaseLoweringPlan k hk ops initSize (Gate.zeroDealloc zExt 1) :=
    PhaseLoweringPlan.zeroDealloc initSize zExt 1

  let deallocXPlan :
      StandardPhaseLoweringPlan k hk ops initSize (Gate.zeroDealloc xExt 1) :=
    PhaseLoweringPlan.zeroDealloc initSize xExt 1

  let completePlan :
      StandardPhaseLoweringPlan k hk ops initSize
        (
          Gate.zeroExtend xExt 1 ;;
          Gate.zeroExtend zExt 1 ;;
          Gate.SignedPhaseProd phi xSigned zSigned ;;
          Gate.zeroDealloc zExt 1 ;;
          Gate.zeroDealloc xExt 1
        ) :=
    PhaseLoweringPlan.seq extendXPlan
      (PhaseLoweringPlan.seq extendZPlan
        (PhaseLoweringPlan.seq signedPlan
          (PhaseLoweringPlan.seq deallocZPlan deallocXPlan)))

  simpa [
    Gate.PhaseProdUsing,
    phaseProdUsingInputSize,
    initSize,
    xExt,
    zExt,
    xSigned,
    zSigned
  ] using completePlan

/-! =========================================================
    Canonical plans and public lowerers

    The canonical recursive plan is built from the two selected workspace
    pools. The final public constructors derive those pools from an `ExtReg`
    reserve and erase the plan to a `LowGate`.
========================================================= -/

/--
Build the standard recursive QFT plan from explicit x-side and z-side
workspace pools satisfying `QFTWorkspaceOK`.
-/
def standardQFTLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork) :
    QFTLoweringPlan k hk ops r := by
  by_cases hzero : regSize r = 0
  · exact QFTLoweringPlan.empty r hzero
  · by_cases hone : regSize r = 1
    · exact QFTLoweringPlan.singleton r hone
    · have hlarge : 2 ≤ regSize r := by omega

      let ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r) :=
        hworkspace.phaseWorkspace hlarge

      have hphaseWorkspace :
          SignedRecursiveWorkspaceOK ops (ws.xExt.grow 1) (ws.zExt.grow 1) := by
        simpa [ws] using hworkspace.signedWorkspaceOK hlarge

      have hrightWorkspace : QFTWorkspaceOK ops (rightReg r) xWork zWork :=
        hworkspace.right hlarge

      have hleftWorkspace : QFTWorkspaceOK ops (leftReg r) xWork zWork :=
        hworkspace.left hlarge

      let phasePlan :
          StandardPhaseLoweringPlan k hk ops (phaseProdUsingInputSize ws)
            (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws) :=
        standardPhaseProdUsingPlan k hk ops (qftPhi (regSize r)) ws hphaseWorkspace

      let rightPlan : QFTLoweringPlan k hk ops (rightReg r) :=
        standardQFTLoweringPlan k hk ops (rightReg r) xWork zWork hrightWorkspace

      let leftPlan : QFTLoweringPlan k hk ops (leftReg r) :=
        standardQFTLoweringPlan k hk ops (leftReg r) xWork zWork hleftWorkspace

      exact QFTLoweringPlan.split r hlarge ws (phaseProdUsingInputSize ws)
          phasePlan rightPlan leftPlan
termination_by regSize r
decreasing_by
  · have hhalfPos : 0 < regSize r / 2 := Nat.div_pos (by omega) (by decide)
    have hright : regSize r - regSize r / 2 < regSize r :=
      Nat.sub_lt (by omega) hhalfPos
    simpa [rightReg, halfSplitPoint, splitM] using hright
  · have hleft : regSize r / 2 < regSize r := Nat.div_lt_self (by omega) (by decide)
    simpa [leftReg, halfSplitPoint, splitM] using hleft

/--
Canonical reserve-backed QFT plan.

The canonical plan obtained by splitting the inactive portion of `r`. This is
the bridge from the public reserve predicate `QFTReserveOK` to the recursive
QFT plan used by the low-level lowerer.
-/
def reserveQFTLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    QFTLoweringPlan k hk ops r.active :=
  standardQFTLoweringPlan k hk ops r.active (qftXWork ops r) (qftZWork ops r)
    hworkspace.explicitWorkspace

/--
The canonical lowered QFT. Its workspace is selected deterministically from
`r.reserve`; callers do not supply separate physical workspace registers.
-/
def lowerQFT
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    LowGate :=
  lowerQFTPlan (reserveQFTLoweringPlan k hk ops r hworkspace)

end Shor
