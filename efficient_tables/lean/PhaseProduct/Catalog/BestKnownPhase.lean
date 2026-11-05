import PhaseProduct.Catalog.BestKnownContract
import PhaseProduct.Identity.ListPhase

/-!
# Phase identities for the best-known generator

Shows the best-known generated and ordered point lists contain the point at
infinity (`bestKnownGeneratedPoints_has_infinity`,
`bestKnownOrderedPoints_has_infinity`). It then gives the pair and triple phase
identities for the best-known generator at arity `k ≥ 2`
(`bestKnown_pair_phase`, `bestKnown_triple_phase`).
-/

namespace Paper.BestKnownPhase

open TableGeneration TableGeneration.Operations
open TableGeneration.Policies.Accepted

theorem canonicalPoints_has_infinity (mode : ProductMode) (k : Nat)
    (hk : 2 ≤ k) :
    Point.frac 0 ∈ canonicalPoints mode k :=
  PointNodes.canonicalPoints_has_infinity mode k hk

theorem bestKnownGeneratedPoints_has_infinity (mode : ProductMode) (k : Nat)
    (hk : 2 ≤ k) :
    Point.frac 0 ∈ bestKnownGeneratedPoints mode k := by
  by_cases hsmall : k ≤ 16
  · interval_cases k <;> cases mode <;> first | omega | decide
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
      (canonicalPoints_has_infinity mode k hk)

theorem bestKnownOrderedPoints_has_infinity (mode : ProductMode) (k : Nat)
    (hk : 2 ≤ k) :
    Point.frac 0 ∈ bestKnownGeneratePointsInOrder mode k hk := by
  have horder := (BestKnownContract.bestKnownGenerate_safe mode k hk).1
  exact horder.mem_iff.mpr (bestKnownGeneratedPoints_has_infinity mode k hk)

theorem bestKnown_pair_phase (k : Nat) (hk : 2 ≤ k) (b : ℚ) :
    ∃ (w : Fin (2*(k-1)+1) → ℚ), ∀ (x z : ValueSemantics.Values k),
    ∃ (xs zs : List Int),
      ValueSemantics.valueTrace (SourceBridge.mapToFull
        (bestKnownGenerate .PhaseProduct k hk)) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull
        (bestKnownGenerate .PhaseProduct k hk)) z = some (z,zs) ∧
      xs.length = 2*k-1 ∧ zs.length = 2*k-1 ∧
      (∑ l, w l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) *
        (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  exact ListPhase.pair_phase_of_valid_list k (positive_of_ge_two hk)
    (bestKnownGenerate .PhaseProduct k hk)
    (bestKnownGeneratePointsInOrder .PhaseProduct k hk)
    (BestKnownContract.bestKnownOrderedPoints_valid .PhaseProduct k hk)
    (bestKnownOrderedPoints_has_infinity .PhaseProduct k hk)
    (BestKnownContract.bestKnownGenerate_safe .PhaseProduct k hk).2 b

theorem bestKnown_triple_phase (k : Nat) (hk : 2 ≤ k) (b : ℚ) :
    ∃ (w : Fin (3*(k-1)+1) → ℚ), ∀ (x y z : ValueSemantics.Values k),
    ∃ (xs ys zs : List Int),
      ValueSemantics.valueTrace (SourceBridge.mapToFull
        (bestKnownGenerate .PhaseTripleProduct k hk)) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull
        (bestKnownGenerate .PhaseTripleProduct k hk)) y = some (y,ys) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull
        (bestKnownGenerate .PhaseTripleProduct k hk)) z = some (z,zs) ∧
      xs.length = 3*k-2 ∧ ys.length = 3*k-2 ∧ zs.length = 3*k-2 ∧
      (∑ l, w l * (xs.getD l.val 0 : ℚ) * (ys.getD l.val 0 : ℚ) *
        (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) *
        (∑ j : Fin k, b^j.val * (y j : ℚ)) *
        (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  exact ListPhase.triple_phase_of_valid_list k (positive_of_ge_two hk)
    (bestKnownGenerate .PhaseTripleProduct k hk)
    (bestKnownGeneratePointsInOrder .PhaseTripleProduct k hk)
    (BestKnownContract.bestKnownOrderedPoints_valid .PhaseTripleProduct k hk)
    (bestKnownOrderedPoints_has_infinity .PhaseTripleProduct k hk)
    (BestKnownContract.bestKnownGenerate_safe .PhaseTripleProduct k hk).2 b

end Paper.BestKnownPhase
