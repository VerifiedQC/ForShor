import Source.Policy

/-!
# Accepted policy P52

Defines the accepted generator policy P52. Provides `generatedPoints`, `handles`, `generatePointsInOrder` and `generate`, proves `generatedPoints_valid` and `generate_safe`, and packages them as `implementation : GeneratorPolicy`.
-/

namespace TableGeneration.Policies.Accepted.P52ec6fce9b57

open Operations

def generatedPoints (mode : ProductMode) (k : Nat) : List Point :=
  if decide (mode = .PhaseTripleProduct ∧ k = 2) then
    [.int 1, .int 0, .int (-1), .frac 0]
  else
    canonicalPoints mode k

def handles (mode : ProductMode) (k : Nat) : Bool :=
  decide (mode = .PhaseTripleProduct ∧ k = 2)

def generatePointsInOrder
    (mode : ProductMode) (k : Nat) (_hk : k >= 2) : List Point :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if htarget : mode = .PhaseTripleProduct ∧ k = 2 then
    let r0 : Fin 2 := ⟨0, by decide⟩
    let r1 : Fin 2 := ⟨1, by decide⟩
    let targetProgram : Prog 2 :=
      [.addScaled r1 r0 false 0,
        .phaseProduct r1,
        .phaseProduct r0,
        .addScaled r1 r0 true 0,
        .addScaled r0 r1 true 0,
        .phaseProduct r0,
        .phaseProduct r1,
        .addScaled r0 r1 false 0]
    htarget.2.symm ▸ targetProgram
  else
    baselineGenerate mode k hk

theorem generatedPoints_valid
    (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  have htarget : mode = .PhaseTripleProduct ∧ k = 2 :=
    of_decide_eq_true hhandles
  rcases htarget with ⟨rfl, rfl⟩
  unfold ValidPointList
  decide

theorem generate_safe
    (mode : ProductMode) (k : Nat) (hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointOrder (generatedPoints mode k) (generatePointsInOrder mode k hk) /\
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  have htarget : mode = .PhaseTripleProduct ∧ k = 2 :=
    of_decide_eq_true hhandles
  rcases htarget with ⟨rfl, rfl⟩
  have hhk : hk = (by decide : 2 >= 2) := Subsingleton.elim _ _
  subst hk
  constructor
  · exact List.Perm.refl _
  · apply progConsumesPtsSafe_of_checks <;> decide

def implementation : GeneratorPolicy where
  generatedPoints := generatedPoints
  handles := handles
  generatePointsInOrder := generatePointsInOrder
  generate := generate
  generatedPoints_valid := generatedPoints_valid
  generate_safe := generate_safe

end TableGeneration.Policies.Accepted.P52ec6fce9b57
