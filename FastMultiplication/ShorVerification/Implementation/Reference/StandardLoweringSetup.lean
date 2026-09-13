import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Programs.WithProduct
import FastMultiplication.ShorVerification.Implementation.GateCount.PhaseProduct.Lemmas

namespace Shor

/-!
# Standard lowering setup

A concrete `ShorLoweringSetup` built from the generated interpolation-point
table `genOpsWithProduct`. This is the program family the emitter uses: it
matches `ShorLoweringSetup.consumes`'s expected point stream
(`genInterpolationPoints k`) exactly, unlike the K2/K3 precomputed tables or
the `k ≥ 4` parity generator, which consume a different point stream.
-/

/-- The standard lowering setup at arity `k`. -/
def standardLoweringSetup (k : ℕ) (hk : 1 < k) : ShorLoweringSetup where
  k := k
  hk := hk
  ops := genOpsWithProduct (k := k) (by omega) (genInterpolationPoints k)
  consumes := genOpsWithProduct_ProgConsumesPtsSafe (k := k) (by omega) (genInterpolationPoints k)
  returns := genOpsWithProduct_returns_to_original (k := k) (by omega) (genInterpolationPoints k)

end Shor
