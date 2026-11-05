import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanBuilders

namespace Shor
open Operations

/-! =========================================================
    The policy-level lowerers

    The names the Shor layer calls when it lowers through a policy.
    The fixed-table lowerers are these at `constPolicy`.
========================================================= -/

/-- The fixed-table lowerer is the policy lowerer at the constant policy. -/
theorem lowerSignedPhaseProd_eq_policy
    (k : ℕ) (hk : 1 < k) (phi : Angle) (x z : ExtReg) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) :
    lowerSignedPhaseProd k hk phi x z ops pts hpts =
      Policy.lowerSignedPhaseProd (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩)
        phi x z :=
  rfl

/-- The controlled twin. -/
theorem lowerCSignedPhaseProd_eq_policy
    (k : ℕ) (hk : 1 < k) (ctrl : ℕ) (phi : Angle) (x z : ExtReg) (ops : Prog k)
    (pts : List Point) (hpts : pts.length = q k) :
    lowerCSignedPhaseProd k hk ctrl phi x z ops pts hpts =
      Policy.lowerCSignedPhaseProd (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩)
        ctrl phi x z :=
  rfl

end Shor
