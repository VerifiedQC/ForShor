import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.Lower
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness

/-!
# Phase-Product Public Assertions

The final semantic claims of the phase-product implementation, stated as named
propositions.
-/

namespace Shor
open Gate
open Operations

/--
The canonical recursive lowering of a signed phase-product gate has the same
semantics as the high-level signed phase-product gate on states with valid,
clean recursive workspace.
-/
def LowerSignedPhaseProductCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) : Prop :=
  ∀ (ψ : qs.State) (pts : List Point) (hpts : pts.length = q k)
    (hworkspace : SignedRecursiveWorkspaceStateOK qs ops x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state),
    LowerGateClass.evalL (qs := qs)
        (lowerSignedPhaseProdWithWorkspace k hk phi x z ops pts hpts hworkspace.static) ψ
      =
    qs.eval (Gate.SignedPhaseProd phi x z) ψ

/--
The canonical recursive lowering of a controlled signed phase-product gate has
the same semantics as the high-level controlled signed phase-product gate on
states with valid, clean recursive workspace.
-/
def LowerCSignedPhaseProductCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k) : Prop :=
  ∀ (ψ : qs.State) (pts : List Point) (hpts : pts.length = q k)
    (hworkspace : CSignedRecursiveWorkspaceStateOK qs ops ctrl x z ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state),
    LowerGateClass.evalL (qs := qs)
        (lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops pts hpts hworkspace.static) ψ
      =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ

end Shor
