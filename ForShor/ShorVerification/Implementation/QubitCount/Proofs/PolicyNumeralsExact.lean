import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.RefPp2048Exact
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.K5Sixband2048Exact
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.ThresholdDeclaredPpExact
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.ThresholdNoshrinkPpExact
import ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumerals.ThresholdScanonlyPpExact

/-!
# Qubit count: the 2048-bit peaks of the STO-table policies (width rule `exact`)

The `exact` (benchmark) width rule counterpart of `PolicyNumerals.lean`, for five of the six
policies. It is **not** imported by `PolicyNumerals.lean` and not part of the `ForShor` umbrella:
each module's kernel evaluation peaks at 9 to 12 GB of memory (the scan modules need 4.5 to 5.4 GB,
of which 3.8 GB is just importing the library), too much for a CI runner. Build it on a machine
with the memory: `lake build ForShor.ShorVerification.Implementation.QubitCount.Proofs.PolicyNumeralsExact`.
`threshold_degenerate_pp` has no `exact` module: its kernel evaluation takes over five minutes.
-/
