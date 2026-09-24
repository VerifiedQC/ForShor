import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders

namespace Shor
open Operations

/--
The canonical lowered circuit constructed from the root physical-workspace
assumption.
-/
def lowerSignedPhaseProdWithWorkspace
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hstatic : SignedRecursiveWorkspaceOK ops x z) :
    LowGate :=
  lowerSignedPhaseProd k hk phi x z ops pts hpts
    (standardSignedPhaseLoweringPlan k hk phi x z ops pts hpts hstatic)

/--
The canonical lowered controlled circuit constructed from the root
physical-workspace assumption.
-/
def lowerCSignedPhaseProdWithWorkspace
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    LowGate :=
  lowerCSignedPhaseProd k hk ctrl phi x z ops pts hpts
    (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops pts hpts hstatic)

end Shor
