import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Assertions
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ModExp

/-!
# Modular-Exponentiation Main Theorem

This module proves the public assertion for the modular-exponentiation
implementation.  All supporting lemmas are kept under
`ModularExponentiation.Proofs`.
-/

namespace Shor

/-- Main modular-exponentiation correctness theorem, packaged as the public
assertion. -/
theorem modExpApprox_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs] :
    ModExpApproxValidDistUniform qs := by
  obtain ⟨K, hK, _hK_le, hbound⟩ := modExpApprox_valid_dist_uniform qs
  exact ⟨K, hK, hbound⟩

end Shor
