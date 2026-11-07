import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.Basic
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.RefPp2048
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.K5Sixband2048
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.ThresholdDeclaredPp
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.ThresholdDegeneratePp
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.ThresholdNoshrinkPp
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.ThresholdScanonlyPp

/-!
# Qubit count: the 2048-bit peaks of the STO-table policies (width rule `scan`)

Root of the numerals for the six phase-product (PP) policies of `Submission/Policies/`
(`ref_pp_2048`, `k5_sixband_2048`, `threshold_declared_pp`, `threshold_degenerate_pp`,
`threshold_noshrink_pp`, `threshold_scanonly_pp`). For each policy, under the width rule `scan`
(the policies' own field) and each negation method (`oneQubit`, `scratch`), the reference 2048-bit
circuit lowered by the policy peaks at `xW + 8795 + N` qubits (`xW` the exponent width, 4095 or
4096) for the plain, the balanced and the every-site-split circuit. The statements are
`ReferencePeakIs`, `ReferenceBalancedPeakIs` and `ReferenceBalancedUPeakIs` of
`PolicyNumerals/Basic.lean`; the numerals `N` are closed by the kernel (`decide +kernel`) in the
per-policy files, one `numerals_scan` declaration each.

The `exact` width rule (the benchmark mode) needs 9 to 12 GB of memory per module, too much for a
CI runner, so its modules are not imported here: they are the roots of
`Proofs/PolicyNumeralsExact.lean`, built on demand. `threshold_degenerate_pp` has no `exact`
module at all (its kernel evaluation takes over five minutes).

The balanced statement carries no hypothesis on the allocator's spare capacities: the reference
layout holds every site's plan, so the balanced count is the width-only count
(`reference2048PeakBalanced_policyU`).

The two `faulty_*` policies are negative controls (no peak theorem) and the `*_ptp` policies have
no order-finding budget here (the phase-triple-product counts are the PTP files').
-/
