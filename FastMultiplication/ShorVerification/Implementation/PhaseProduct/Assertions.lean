import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs

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
    [LowerGateGateBridge qs]
    (k : ℕ) (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k) : Prop :=
  ∀ (ψ : qs.State)
    (hworkspace : SignedRecursiveWorkspaceStateOK qs ops x z ψ)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state),
    LowerGateClass.evalL (qs := qs)
        (lowerSignedPhaseProdWithWorkspace k hk phi x z ops hworkspace.static) ψ
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
    [LowerGateGateBridge qs]
    (k : ℕ) (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k) : Prop :=
  ∀ (ψ : qs.State)
    (hworkspace : CSignedRecursiveWorkspaceStateOK qs ops ctrl x z ψ)
    (hC : ProgConsumesPtsSafe
      (k := k)
      (by omega)
      State.start_state
      ops
      (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state),
    LowerGateClass.evalL (qs := qs)
        (lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops hworkspace.static) ψ
      =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ

end Shor
