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
inductive QFTLoweringPlan (k : ℕ) (hk : 1 < k) (ops : Prog k) : Reg → Type
  | empty (r : Reg) (hsize : regSize r = 0) : QFTLoweringPlan k hk ops r
  | singleton (r : Reg) (hsize : regSize r = 1) : QFTLoweringPlan k hk ops r
  | split
      (r : Reg) (hsize : 2 ≤ regSize r) (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
      (phaseInitSize : ℕ)
      (phasePlan :
        StandardPhaseLoweringPlan k hk ops
          phaseInitSize (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws))
      (rightPlan : QFTLoweringPlan k hk ops (rightReg r))
      (leftPlan : QFTLoweringPlan k hk ops (leftReg r)) :
      QFTLoweringPlan k hk ops r

def lowerQFTPlan {k : ℕ} {hk : 1 < k} {ops : Prog k} {r : Reg} (plan : QFTLoweringPlan k hk ops r) :
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
