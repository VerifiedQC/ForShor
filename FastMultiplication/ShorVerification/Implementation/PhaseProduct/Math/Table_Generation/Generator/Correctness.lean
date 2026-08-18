import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.WellFormed
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

theorem generatedPoints_valid (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ValidPointList mode k (generatedPoints mode k) := by
  sorry

theorem generate_ProgConsumesPtsSafe (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ProgConsumesPtsSafe (by omega) State.start_state
      (generate mode k hk) (generatePointsInOrder mode k hk) := by
  sorry

end Table_Generation
