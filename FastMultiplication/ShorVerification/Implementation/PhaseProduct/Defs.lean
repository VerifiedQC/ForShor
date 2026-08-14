import FastMultiplication.ShorVerification.Implementation.PhaseProduct.DefsCore
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.PhaseLoweringPlan

namespace Shor

/--
The canonical lowered circuit constructed from the root physical-workspace
assumption.
-/
noncomputable def lowerSignedPhaseProdWithWorkspace
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
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
noncomputable def lowerCSignedPhaseProdWithWorkspace
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    LowGate :=
  lowerCSignedPhaseProd k hk ctrl phi x z ops
    (standardCSignedPhaseLoweringPlan k hk ctrl phi x z ops hstatic)

end Shor
