import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.WellFormed
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

-- Failure-case PR for checking submission CI behavior.

/- The generated point list has the expected length and allowed point shapes. -/
theorem generatedPoints_valid (mode : ProductMode) (k : ℕ) (_ : k ≥ 2) :
    ValidPointList mode k (generatedPoints mode k) := by
  sorry

/- The generated program safely consumes the expected points in order. -/
theorem generate_ProgConsumesPtsSafe (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ProgConsumesPtsSafe (by omega) State.start_state
      (generate mode k hk) (generatePointsInOrder mode k hk) := by
  sorry

end Table_Generation
