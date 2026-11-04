import Source.BestKnown
import PhaseProduct.Baseline.BaselineContract
import PhaseProduct.Identity.CanonicalValidity

/-!
# Contract of the best-known generator

Shows the best-known generator produces valid points
(`bestKnownGeneratedPoints_valid`, `bestKnownOrderedPoints_valid`) and that its
generated program is safe (`bestKnownGenerate_safe`). `validPointList_of_order`
transfers validity along a point order.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace Paper.BestKnownContract

open TableGeneration TableGeneration.Operations
open TableGeneration.Policies.Accepted

theorem validPointList_of_order (mode : ProductMode) (k : Nat)
    (generated ordered : List Point)
    (hvalid : ValidPointList mode k generated)
    (horder : ValidPointOrder generated ordered) :
    ValidPointList mode k ordered := by
  rcases hvalid with ⟨hlen, hnodup, hall⟩
  refine ⟨?_, ?_, ?_⟩
  · exact horder.length_eq.trans hlen
  · exact (horder.symm.map normalizePoint).nodup_iff.mp hnodup
  · apply List.all_eq_true.mpr
    intro pt hpt
    exact (List.all_eq_true.mp hall) pt ((horder.mem_iff).mp hpt)

theorem bestKnownGeneratedPoints_valid (mode : ProductMode) (k : Nat)
    (hk : 2 ≤ k) :
    ValidPointList mode k (bestKnownGeneratedPoints mode k) := by
  by_cases hsmall : k ≤ 16
  · interval_cases k <;> cases mode <;>
      first
      | omega
      | simpa [bestKnownGeneratedPoints] using
          (P6f7d25984ff8.implementation.generatedPoints_valid .PhaseProduct 2
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (P52ec6fce9b57.implementation.generatedPoints_valid .PhaseTripleProduct 2
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 3
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (P6f7d25984ff8.implementation.generatedPoints_valid .PhaseTripleProduct 3
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 4
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 4
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 5
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 5
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 6
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 6
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 7
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 7
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 8
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 8
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 9
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 9
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 10
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 10
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 11
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 11
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 12
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 12
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 13
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 13
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 14
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 14
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 15
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 15
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseProduct 16
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints] using
          (Pf4aff955f16b.implementation.generatedPoints_valid .PhaseTripleProduct 16
            (by decide) (by decide))
  · have hlarge : 16 < k := by omega
    simpa [bestKnownGeneratedPoints,
      show k ≠ 2 by omega,
      show k ≠ 3 by omega,
      show k ≠ 4 by omega,
      show k ≠ 5 by omega,
      show k ≠ 6 by omega,
      show k ≠ 7 by omega,
      show k ≠ 8 by omega,
      show k ≠ 9 by omega,
      show k ≠ 10 by omega,
      show k ≠ 11 by omega,
      show k ≠ 12 by omega,
      show k ≠ 13 by omega,
      show k ≠ 14 by omega,
      show k ≠ 15 by omega,
      show k ≠ 16 by omega] using
      (CanonicalValidity.canonicalPoints_valid mode k)

theorem bestKnownGenerate_safe (mode : ProductMode) (k : Nat)
    (hk : 2 ≤ k) :
    ValidPointOrder (bestKnownGeneratedPoints mode k)
        (bestKnownGeneratePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (bestKnownGenerate mode k hk)
        (bestKnownGeneratePointsInOrder mode k hk) := by
  by_cases hsmall : k ≤ 16
  · interval_cases k <;> cases mode <;>
      first
      | omega
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (P6f7d25984ff8.implementation.generate_safe .PhaseProduct 2
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (P52ec6fce9b57.implementation.generate_safe .PhaseTripleProduct 2
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 3
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (P6f7d25984ff8.implementation.generate_safe .PhaseTripleProduct 3
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 4
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 4
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 5
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 5
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 6
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 6
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 7
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 7
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 8
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 8
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 9
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 9
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 10
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 10
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 11
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 11
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 12
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 12
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 13
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 13
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 14
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 14
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 15
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 15
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseProduct 16
            (by decide) (by decide))
      | simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
          bestKnownGenerate] using
          (Pf4aff955f16b.implementation.generate_safe .PhaseTripleProduct 16
            (by decide) (by decide))
  · have hlarge : 16 < k := by omega
    simpa [bestKnownGeneratedPoints, bestKnownGeneratePointsInOrder,
      bestKnownGenerate, show k ≠ 2 by omega,
      show k ≠ 3 by omega,
      show k ≠ 4 by omega,
      show k ≠ 5 by omega,
      show k ≠ 6 by omega,
      show k ≠ 7 by omega,
      show k ≠ 8 by omega,
      show k ≠ 9 by omega,
      show k ≠ 10 by omega,
      show k ≠ 11 by omega,
      show k ≠ 12 by omega,
      show k ≠ 13 by omega,
      show k ≠ 14 by omega,
      show k ≠ 15 by omega,
      show k ≠ 16 by omega] using
      (show ValidPointOrder (baselineGeneratedPoints mode k)
          (baselineGeneratePointsInOrder mode k hk) ∧
        ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
          (baselineGenerate mode k hk)
          (baselineGeneratePointsInOrder mode k hk) from
        ⟨List.Perm.refl _, BaselineContract.baselineGenerate_contract mode k hk⟩)

theorem bestKnownOrderedPoints_valid (mode : ProductMode) (k : Nat)
    (hk : 2 ≤ k) :
    ValidPointList mode k (bestKnownGeneratePointsInOrder mode k hk) :=
  validPointList_of_order mode k
    (bestKnownGeneratedPoints mode k)
    (bestKnownGeneratePointsInOrder mode k hk)
    (bestKnownGeneratedPoints_valid mode k hk)
    (bestKnownGenerate_safe mode k hk).1

end Paper.BestKnownContract
