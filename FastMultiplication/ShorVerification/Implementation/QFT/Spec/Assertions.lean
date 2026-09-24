import FastMultiplication.ShorVerification.Implementation.QFT.Lowering.PlanBuilders
import FastMultiplication.ShorVerification.Implementation.QFT.Spec.Cleanliness

/-!
# QFT Public Assertion

The final semantic claim of the QFT implementation, stated as a named
proposition.
-/

namespace Shor
open Gate
open Operations

/--
The canonical recursive lowering of a QFT gate has the same semantics as the
high-level `Gate.QFT` gate on states with valid, clean recursive workspace.
-/
def LowerQFTCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs] [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (r : ExtReg) : Prop :=
  ∀ (ψ : qs.State) (pts : List Point) (hpts : pts.length = q k)
    (hworkspace : QFTWorkspaceStateOK qs ops r ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state),
    LowerGateClass.evalL (qs := qs) (lowerQFT k hk ops pts hpts r hworkspace.static) ψ = qs.eval (Gate.QFT r) ψ

end Shor
