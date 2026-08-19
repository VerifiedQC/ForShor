import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Generator.WellFormed
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

open Operations

namespace Table_Generation

/- The generated point list is the protected canonical point list. -/
theorem generatedPoints_valid (mode : ProductMode) (k : ℕ) (_ : k ≥ 2) :
    ValidPointList mode k (generatedPoints mode k) := by
  sorry

/- The generated program safely consumes a permutation of the canonical points. -/
theorem generate_ProgConsumesPtsSafe (mode : ProductMode) (k : ℕ) (hk : k ≥ 2) :
    ValidPointOrder mode k (generatePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (by omega) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  sorry

end Table_Generation
