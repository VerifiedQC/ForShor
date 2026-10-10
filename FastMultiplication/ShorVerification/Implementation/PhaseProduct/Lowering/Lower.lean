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

/-! =========================================================
    The policy-level lowerers

    The names the Shor layer calls once it lowers through a policy (item 5).
    The fixed-table lowerers above are these at `constPolicy`, which is what
    `Policy.workspaceOK_const_iff` says.
========================================================= -/

/--
The lowered circuit for a signed phase product under a policy: the dispatcher's
plan, erased to a `LowGate`.
-/
def Policy.lowerSignedPhaseProd
    (P : ShorLoweringPolicy)
    (phi : Angle)
    (x z : ExtReg)
    (hstatic : Policy.WorkspaceOK P x z) :
    LowGate :=
  lowerGateRec (Policy.signedPlan P phi x z hstatic)

/--
The lowered controlled circuit for a signed phase product under a policy.
-/
def Policy.lowerCSignedPhaseProd
    (P : ShorLoweringPolicy)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (hstatic : Policy.CWorkspaceOK P ctrl x z) :
    LowGate :=
  lowerGateRec (Policy.cSignedPlan P ctrl phi x z hstatic)

/-- The fixed-table lowerer is the policy lowerer at the constant policy. -/
theorem lowerSignedPhaseProdWithWorkspace_eq_policy
    (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k)
    (hstatic : SignedRecursiveWorkspaceOK ops x z) :
    lowerSignedPhaseProdWithWorkspace k hk phi x z ops pts hpts hstatic =
      Policy.lowerSignedPhaseProd (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩)
        phi x z (Policy.workspaceOK_const_iff.mpr hstatic) :=
  rfl

/-- The controlled twin. -/
theorem lowerCSignedPhaseProdWithWorkspace_eq_policy
    (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k)
    (hstatic : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops pts hpts hstatic =
      Policy.lowerCSignedPhaseProd (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩)
        ctrl phi x z (Policy.cWorkspaceOK_const_iff.mpr hstatic) :=
  rfl

end Shor
