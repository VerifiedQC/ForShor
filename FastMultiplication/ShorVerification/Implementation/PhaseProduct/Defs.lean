import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.PhaseLoweringPlan
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Spec.Cleanliness

namespace Shor

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
    (hstatic : SignedRecursiveWorkspaceOK ops x z) :
    LowGate :=
  lowerSignedPhaseProd k hk phi x z ops
    (standardSignedPhaseLoweringPlan
      k hk phi x z ops hstatic)

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
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    LowGate :=
  lowerCSignedPhaseProd k hk ctrl phi x z ops
    (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hstatic)

end Shor
