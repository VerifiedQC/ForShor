import FastMultiplication.ShorVerification.Implementation.QFT.Split
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Plan

/-!
# Explicit QFT Lowering Plans

`QFTLoweringPlan` is the finite certificate carried by the public QFT
lowerer. It exposes the empty and singleton base cases and the recursive
split case, including the phase-product plan needed between the two
halves, and `lowerQFTPlan`, the interpreter erasing such a plan to a
`LowGate`.
-/

namespace Shor

open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Explicit QFT lowering plans

    `QFTLoweringPlan` is the finite certificate carried by the public lowerer.
    It exposes the empty and singleton base cases and the recursive split case,
    including the phase-product plan needed between the two halves.
========================================================= -/

/--
A complete physical lowering plan for one QFT.

The phase plan is intentionally explicit.  This is the point at which a caller
chooses either a base-case signed phase product or a recursive implementation
with concrete reserve layouts.
-/
inductive QFTLoweringPlan (P : ShorLoweringPolicy) : Reg → Type
  | empty (r : Reg) (hsize : regSize r = 0) : QFTLoweringPlan P r
  | singleton (r : Reg) (hsize : regSize r = 1) : QFTLoweringPlan P r
  | split
      (r : Reg) (hsize : 2 ≤ regSize r) (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
      (phaseInitSize : ℕ)
      (phasePlan :
        PhaseLoweringPlan P
          phaseInitSize (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws))
      (rightPlan : QFTLoweringPlan P (rightReg r))
      (leftPlan : QFTLoweringPlan P (leftReg r)) :
      QFTLoweringPlan P r

/--
The fixed-table spelling of a QFT plan: the policy plan at the constant
policy, exactly as `StandardPhaseLoweringPlan` is for phase products. Every
existing caller keeps its five table arguments.
-/
abbrev StandardQFTLoweringPlan
    (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k) (ops : Prog k)
    (r : Reg) : Type :=
  QFTLoweringPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) r

def lowerQFTPlan
    {P : ShorLoweringPolicy} {r : Reg}
    (plan : QFTLoweringPlan P r) :
    LowGate :=
  match plan with
  | .empty r hsize => LowGate.id
  | .singleton r hsize => LowGate.H (r.lowQubit (by omega))
  | .split r hsize ws phaseInitSize phasePlan rightPlan leftPlan =>
      lowerQFTPlan rightPlan ;;
      lowerGateRec phasePlan ;;
      lowerQFTPlan leftPlan ;;
      LowGate.RadixReverse r (splitM r)

end Shor
