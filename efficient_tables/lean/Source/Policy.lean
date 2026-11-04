import Source.Baseline

/-!
# Generator policy interface

Defines `GeneratorPolicy`, a portable generator implementation bundled with its correctness proofs: the generated points are valid and the generated program safely consumes them in order. Also provides `GeneratorPolicy.empty`, the submission template that implements no targets.
-/

namespace TableGeneration

open Operations

/-- A portable generator implementation together with its correctness proofs. -/
structure GeneratorPolicy where
  generatedPoints : ProductMode → Nat → List Point
  handles : ProductMode → Nat → Bool
  generatePointsInOrder :
    (mode : ProductMode) → (k : Nat) → k >= 2 → List Point
  generate : (mode : ProductMode) → (k : Nat) → k >= 2 → Prog k
  generatedPoints_valid :
    ∀ (mode : ProductMode) (k : Nat), k >= 2 → handles mode k = true →
      ValidPointList mode k (generatedPoints mode k)
  generate_safe :
    ∀ (mode : ProductMode) (k : Nat) (hk : k >= 2), handles mode k = true →
      ValidPointOrder (generatedPoints mode k) (generatePointsInOrder mode k hk) /\
        ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
          (generate mode k hk) (generatePointsInOrder mode k hk)

namespace GeneratorPolicy

/-- The submission template implements no targets. -/
def empty : GeneratorPolicy where
  generatedPoints := canonicalPoints
  handles := fun _ _ => false
  generatePointsInOrder := baselineGeneratePointsInOrder
  generate := baselineGenerate
  generatedPoints_valid := by
    intros
    contradiction
  generate_safe := by
    intros
    contradiction

end GeneratorPolicy

end TableGeneration
