import ForShor.ShorVerification.Implementation.ModularExponentiation.Spec.Assertions
import ForShor.ShorVerification.Implementation.ModularExponentiation.Proofs.ModExp

/-!
# Modular-Exponentiation Main Theorem

This module proves the public assertion for the modular-exponentiation
implementation.  All supporting lemmas are kept under
`ModularExponentiation.Proofs`.
-/

namespace Shor

/-- Main modular-exponentiation correctness theorem, packaged as the public
assertion.

The constant bound `K ≤ 1600` travels with the existential because a caller
that wants a *concrete* `K` needs it: `Reference`'s `referenceK = 1600` is
justified by exactly this, by monotonicity of `stepErr` in `K`. -/
theorem modExpApprox_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
 :
    ModExpApproxValidDistUniform qs := by
  obtain ⟨K, hK, hK_le, hbound⟩ := modExpApprox_valid_dist_uniform qs
  exact ⟨K, hK, hK_le, hbound⟩

/-- The uniform bound at the explicit constant, packaged as the public
assertion. This is the one a caller that must choose a precision needs. -/
theorem modExpApprox_correct_1600
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
 :
    ModExpApproxValidDist1600 qs :=
  modExpApprox_valid_dist_1600 qs

end Shor
