import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Assertions
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
    [Spec]
    [GateSemanticsFacts qs]
    [IdealCtrlModMulExactSemantics qs] :
    ModExpApproxValidDistUniform qs :=
  modExpApprox_valid_dist_uniform qs

end Shor
