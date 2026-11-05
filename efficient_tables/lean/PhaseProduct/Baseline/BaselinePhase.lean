import PhaseProduct.Baseline.BaselineContract
import PhaseProduct.Identity.CanonicalValidity

/-!
# Phase identities for the baseline

The baseline generator's points are valid and ordered
(`baseline_validPoints`, `baseline_pointOrder`) at arity `k ≥ 2`, and it
satisfies the pair and triple phase identities (`baseline_pair_phase`,
`baseline_triple_phase`).
-/

namespace Paper.BaselinePhase
open TableGeneration TableGeneration.Operations

theorem baseline_validPoints (mode : ProductMode) (k : Nat) (hk : 2 ≤ k) :
    ValidPointList mode k (baselineGeneratePointsInOrder mode k hk) :=
  CanonicalValidity.canonicalPoints_valid mode k

theorem baseline_pointOrder (mode : ProductMode) (k : Nat) (hk : 2 ≤ k) :
    ValidPointOrder (baselineGeneratedPoints mode k) (baselineGeneratePointsInOrder mode k hk) :=
  List.Perm.refl _

theorem baseline_pair_phase (k : Nat) (hk : 2 ≤ k) (b : ℚ) :
    ∃ (w : Fin (2*(k-1)+1) → ℚ), ∀ (x z : ValueSemantics.Values k),
    ∃ (xs zs : List Int),
      ValueSemantics.valueTrace (SourceBridge.mapToFull (baselineGenerate .PhaseProduct k hk)) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull (baselineGenerate .PhaseProduct k hk)) z = some (z,zs) ∧
      xs.length = 2*k-1 ∧ zs.length = 2*k-1 ∧
      (∑ l, w l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) * (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  let pts : Fin (2*(k-1)+1) → Point := fun i => canonicalPoint i.val
  have hcount : 2*k-1 = 2*(k-1)+1 := by omega
  have hpts : baselineGeneratePointsInOrder .PhaseProduct k hk = List.ofFn pts := by
    change canonicalPoints .PhaseProduct k = List.ofFn pts
    rw [CanonicalNodes.canonicalPoints_eq_ofFn]
    simp only [ProductMode.pointCount, hcount, Fin.val_cast, pts]
  have hc : ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
      (baselineGenerate .PhaseProduct k hk) (List.ofFn pts) := by
    rw [← hpts]
    exact BaselineContract.baselineGenerate_contract .PhaseProduct k hk
  obtain ⟨v, order, hv, hf, hi⟩ := CanonicalNodes.canonical_enumeration
    (d := 2*(k-1)) (by omega)
  refine ⟨GeneralConstruction.phaseWeights k 2 pts v b order, ?_⟩
  intro x z
  exact GeneralConstruction.source_pair_constructed_phase
    (positive_of_ge_two hk) (baselineGenerate .PhaseProduct k hk) pts v order hv hf hi b hc x z

theorem baseline_triple_phase (k : Nat) (hk : 2 ≤ k) (b : ℚ) :
    ∃ (w : Fin (3*(k-1)+1) → ℚ), ∀ (x y z : ValueSemantics.Values k),
    ∃ (xs ys zs : List Int),
      ValueSemantics.valueTrace (SourceBridge.mapToFull (baselineGenerate .PhaseTripleProduct k hk)) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull (baselineGenerate .PhaseTripleProduct k hk)) y = some (y,ys) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull (baselineGenerate .PhaseTripleProduct k hk)) z = some (z,zs) ∧
      xs.length = 3*k-2 ∧ ys.length = 3*k-2 ∧ zs.length = 3*k-2 ∧
      (∑ l, w l * (xs.getD l.val 0 : ℚ) * (ys.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) * (∑ j : Fin k, b^j.val * (y j : ℚ)) *
        (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  let pts : Fin (3*(k-1)+1) → Point := fun i => canonicalPoint i.val
  have hcount : 3*k-2 = 3*(k-1)+1 := by omega
  have hpts : baselineGeneratePointsInOrder .PhaseTripleProduct k hk = List.ofFn pts := by
    change canonicalPoints .PhaseTripleProduct k = List.ofFn pts
    rw [CanonicalNodes.canonicalPoints_eq_ofFn]
    simp only [ProductMode.pointCount, hcount, Fin.val_cast, pts]
  have hc : ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
      (baselineGenerate .PhaseTripleProduct k hk) (List.ofFn pts) := by
    rw [← hpts]
    exact BaselineContract.baselineGenerate_contract .PhaseTripleProduct k hk
  obtain ⟨v, order, hv, hf, hi⟩ := CanonicalNodes.canonical_enumeration
    (d := 3*(k-1)) (by omega)
  refine ⟨GeneralConstruction.phaseWeights k 3 pts v b order, ?_⟩
  intro x y z
  exact GeneralConstruction.source_triple_constructed_phase
    (positive_of_ge_two hk) (baselineGenerate .PhaseTripleProduct k hk) pts v order hv hf hi b hc x y z

end Paper.BaselinePhase
