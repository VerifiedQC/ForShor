import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Plan
import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.Workspace
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
open Operations
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
def phaseProdUsingInputSize {x z : Reg} (ws : Gate.PhaseProdWorkspace x z) : ℕ :=
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
def Policy.phaseProdUsingPlan
    (P : ShorLoweringPolicy)
    (phi : Angle) {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace : Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1)) :
    PhaseLoweringPlan P (phaseProdUsingInputSize ws)
      (Gate.PhaseProdUsing phi x z ws) := by
  let initSize : ℕ := phaseProdUsingInputSize ws
  let xExt : ExtReg := ws.xExt
  let zExt : ExtReg := ws.zExt
  let xSigned : ExtReg := xExt.grow 1
  let zSigned : ExtReg := zExt.grow 1

  let extendXPlan : PhaseLoweringPlan P initSize (Gate.zeroExtend xExt 1) :=
    PhaseLoweringPlan.zeroExtend initSize xExt 1

  let extendZPlan : PhaseLoweringPlan P initSize (Gate.zeroExtend zExt 1) :=
    PhaseLoweringPlan.zeroExtend initSize zExt 1

  let signedPlan :
      PhaseLoweringPlan P initSize (Gate.SignedPhaseProd phi xSigned zSigned) := by
    have hsize : phaseInputSize xSigned zSigned = initSize := by rfl
    simpa [hsize] using
      Policy.signedPlan P phi xSigned zSigned hworkspace

  let deallocZPlan : PhaseLoweringPlan P initSize (Gate.zeroDealloc zExt 1) :=
    PhaseLoweringPlan.zeroDealloc initSize zExt 1

  let deallocXPlan : PhaseLoweringPlan P initSize (Gate.zeroDealloc xExt 1) :=
    PhaseLoweringPlan.zeroDealloc initSize xExt 1

  let completePlan :
      PhaseLoweringPlan P initSize
        (Gate.zeroExtend xExt 1 ;;
          Gate.zeroExtend zExt 1 ;;
          Gate.SignedPhaseProd phi xSigned zSigned ;;
          Gate.zeroDealloc zExt 1 ;;
          Gate.zeroDealloc xExt 1) :=
    PhaseLoweringPlan.seq extendXPlan
      (PhaseLoweringPlan.seq extendZPlan
        (PhaseLoweringPlan.seq signedPlan
          (PhaseLoweringPlan.seq deallocZPlan deallocXPlan)))

  simpa [Gate.PhaseProdUsing, phaseProdUsingInputSize, initSize, xExt, zExt, xSigned, zSigned]
    using completePlan

/-- The fixed-table spelling: the policy builder at the constant policy. -/
def standardPhaseProdUsingPlan
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (phi : Angle) {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace : SignedRecursiveWorkspaceOK ops (ws.xExt.grow 1) (ws.zExt.grow 1)) :
    StandardPhaseLoweringPlan k hk pts hpts ops (phaseProdUsingInputSize ws)
      (Gate.PhaseProdUsing phi x z ws) :=
  Policy.phaseProdUsingPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) phi ws
    (Policy.workspaceOK_const_iff.mpr hworkspace)

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
def Policy.qftPlan
    (P : ShorLoweringPolicy)
    (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) :
    QFTLoweringPlan P r := by
  by_cases hzero : regSize r = 0
  · exact QFTLoweringPlan.empty r hzero
  · by_cases hone : regSize r = 1
    · exact QFTLoweringPlan.singleton r hone
    · have hlarge : 2 ≤ regSize r := by omega

      let ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r) :=
        hworkspace.phaseWorkspace hlarge

      have hphaseWorkspace :
          Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1) := by
        simpa [ws] using hworkspace.policySignedWorkspaceOK hlarge

      have hrightWorkspace : Policy.QFTWorkspaceOK P (rightReg r) xWork zWork :=
        hworkspace.right hlarge

      have hleftWorkspace : Policy.QFTWorkspaceOK P (leftReg r) xWork zWork :=
        hworkspace.left hlarge

      let phasePlan : PhaseLoweringPlan P (phaseProdUsingInputSize ws)
          (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws) :=
        Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws hphaseWorkspace

      let rightPlan : QFTLoweringPlan P (rightReg r) :=
        Policy.qftPlan P (rightReg r) xWork zWork hrightWorkspace

      let leftPlan : QFTLoweringPlan P (leftReg r) :=
        Policy.qftPlan P (leftReg r) xWork zWork hleftWorkspace

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

/-- `qftWorkspaceOK_const_iff.mpr` with every argument explicit, so the IR
extractor can build it with `mkAppM`. -/
theorem Policy.qftWorkspaceOK_of_const (T : ToomCookTable) (r xWork zWork : Reg)
    (h : _root_.Shor.QFTWorkspaceOK T.ops r xWork zWork) :
    Policy.QFTWorkspaceOK (ShorLoweringPolicy.constPolicy T) r xWork zWork :=
  Policy.qftWorkspaceOK_const_iff.mpr h

/-- The fixed-table spelling: the policy planner at the constant policy. -/
def standardQFTLoweringPlan
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork) :
    StandardQFTLoweringPlan k hk pts hpts ops r :=
  Policy.qftPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) r xWork zWork
    (Policy.qftWorkspaceOK_const_iff.mpr hworkspace)

/--
Canonical reserve-backed QFT plan.

The canonical plan obtained by splitting the inactive portion of `r`. This is
the bridge from the public reserve predicate `QFTReserveOK` to the recursive
QFT plan used by the low-level lowerer.
-/
def Policy.reserveQftPlan
    (P : ShorLoweringPolicy)
    (r : ExtReg) (hworkspace : Policy.QFTReserveOK P r) :
    QFTLoweringPlan P r.active :=
  Policy.qftPlan P r.active (Policy.qftXWork P r) (Policy.qftZWork P r)
    hworkspace.explicitWorkspace

/-- The fixed-table spelling. Its workspace pools stay the `ops`-keyed
slices, so nothing downstream has to transport along the pool bridges. -/
def reserveQFTLoweringPlan
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (r : ExtReg) (hworkspace : QFTReserveOK ops r) :
    StandardQFTLoweringPlan k hk pts hpts ops r.active :=
  standardQFTLoweringPlan k hk ops pts hpts r.active (qftXWork ops r) (qftZWork ops r)
    hworkspace.explicitWorkspace

/--
The canonical lowered QFT. Its workspace is selected deterministically from
`r.reserve`; callers do not supply separate physical workspace registers.
-/
def Policy.lowerQFT
    (P : ShorLoweringPolicy)
    (r : ExtReg) (hworkspace : Policy.QFTReserveOK P r) :
    LowGate :=
  lowerQFTPlan (Policy.reserveQftPlan P r hworkspace)

/-- The fixed-table spelling. -/
def lowerQFT
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (r : ExtReg) (hworkspace : QFTReserveOK ops r) :
    LowGate :=
  lowerQFTPlan (reserveQFTLoweringPlan k hk ops pts hpts r hworkspace)

end Shor
