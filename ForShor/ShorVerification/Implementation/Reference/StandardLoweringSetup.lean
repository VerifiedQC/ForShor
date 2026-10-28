import ForShor.ShorVerification.Implementation.Shor.Spec.Setup
import ForShor.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import ForShor.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Programs.WithProduct
import ForShor.ShorVerification.Implementation.GateCount.PhaseProduct.Lemmas

namespace Shor

/-!
# Standard P setup

A concrete `ShorLoweringSetup` built from the generated interpolation-point
table `genOpsWithProduct`. This is the program family the emitter uses: it
matches `ShorLoweringSetup.consumes`'s expected point stream
(`genInterpolationPoints k`) exactly, unlike the K2/K3 precomputed tables or
the `k ≥ 4` parity generator, which consume a different point stream.
-/

/-- The standard P setup at arity `k`. -/
def standardLoweringSetup (k : ℕ) (hk : 1 < k) : ShorLoweringSetup where
  k := k
  hk := hk
  pts := genInterpolationPoints k
  hpts := generatedInterpolationPoints_length k
  good := genInterpolationPoints_good k
  ops := genOpsWithProduct (k := k) (by omega) (genInterpolationPoints k)
  consumes := genOpsWithProduct_ProgConsumesPtsSafe (k := k) (by omega) (genInterpolationPoints k)
  returns := genOpsWithProduct_returns_to_original (k := k) (by omega) (genInterpolationPoints k)

/-- The standard P setup, as a one-band policy at threshold `0`. -/
def standardPolicy (k : ℕ) (hk : 1 < k) : ShorLoweringPolicy :=
  ShorLoweringPolicy.constPolicy (standardLoweringSetup k hk).table

/-- The standard policy is admissible. -/
theorem standardPolicy_admissible (k : ℕ) (hk : 1 < k) :
    (standardPolicy k hk).Admissible :=
  ShorLoweringPolicy.constPolicy_admissible (standardLoweringSetup k hk).table_admissible

end Shor
