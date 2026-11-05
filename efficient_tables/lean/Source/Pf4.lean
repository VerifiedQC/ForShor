import Source.Pf4Fixed
import Source.Pf4Parity

/-!
# Accepted policy Pf4

Defines the accepted generator policy Pf4, combining the fixed (`Source.Pf4Fixed`) and parity (`Source.Pf4Parity`) constructions. Provides `generatedPoints`, `selectedTarget`, `handles` and `generate`, proves `generatedPoints_valid` and `generate_safe`, and packages them as `implementation : GeneratorPolicy`.
-/

namespace TableGeneration.Policies.Accepted.Pf4aff955f16b

open Operations

def generatedPoints (mode : ProductMode) (k : Nat) : List Point :=
  if decide (mode = .PhaseProduct ∧ k = 3) then
    Fixed.phaseProductK3Points
  else if decide (mode = .PhaseTripleProduct ∧ k = 4) then
    Fixed.phaseTripleProductK4Points
  else if decide (mode = .PhaseTripleProduct ∧ k = 5) then
    Fixed.phaseTripleProductK5Points
  else if decide (mode = .PhaseTripleProduct ∧ k = 6) then
    Fixed.phaseTripleProductK6Points
  else
    canonicalPoints mode k

def selectedTarget (mode : ProductMode) (k : Nat) : Bool :=
  match mode with
  | .PhaseProduct => decide (k = 3) || OptimizedParity.scoredK k
  | .PhaseTripleProduct =>
      decide (k = 4) || (decide (k = 5) || (decide (k = 6) ||
        (OptimizedParity.scoredK k && decide (k >= 7))))

def handles (mode : ProductMode) (k : Nat) : Bool :=
  selectedTarget mode k

def generatePointsInOrder
    (mode : ProductMode) (k : Nat) (_hk : k >= 2) : List Point :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if h3 : mode = .PhaseProduct ∧ k = 3 then
    h3.2.symm ▸ Fixed.phaseProductK3Program
  else if h4 : mode = .PhaseTripleProduct ∧ k = 4 then
    h4.2.symm ▸ Fixed.phaseTripleProductK4Program
  else if h5 : mode = .PhaseTripleProduct ∧ k = 5 then
    h5.2.symm ▸ Fixed.phaseTripleProductK5Program
  else if h6 : mode = .PhaseTripleProduct ∧ k = 6 then
    h6.2.symm ▸ Fixed.phaseTripleProductK6Program
  else
    OptimizedParity.generate mode k hk

theorem generatedPoints_valid
    (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  by_cases h3 : mode = .PhaseProduct ∧ k = 3
  · rcases h3 with ⟨rfl, rfl⟩
    unfold ValidPointList generatedPoints Fixed.phaseProductK3Points
    decide
  by_cases h4 : mode = .PhaseTripleProduct ∧ k = 4
  · rcases h4 with ⟨rfl, rfl⟩
    unfold ValidPointList generatedPoints Fixed.phaseTripleProductK4Points
    decide
  by_cases h5 : mode = .PhaseTripleProduct ∧ k = 5
  · rcases h5 with ⟨rfl, rfl⟩
    unfold ValidPointList generatedPoints Fixed.phaseTripleProductK5Points
    decide
  by_cases h6 : mode = .PhaseTripleProduct ∧ k = 6
  · rcases h6 with ⟨rfl, rfl⟩
    unfold ValidPointList generatedPoints Fixed.phaseTripleProductK6Points
    decide
  · have hscore : OptimizedParity.scoredK k = true := by
      cases mode with
      | PhaseProduct =>
          have hk3 : k ≠ 3 := fun hk => h3 ⟨rfl, hk⟩
          simpa [handles, selectedTarget, hk3] using hhandles
      | PhaseTripleProduct =>
          have hk4 : k ≠ 4 := fun hk => h4 ⟨rfl, hk⟩
          have hk5 : k ≠ 5 := fun hk => h5 ⟨rfl, hk⟩
          have hk6 : k ≠ 6 := fun hk => h6 ⟨rfl, hk⟩
          have hselected :
              OptimizedParity.scoredK k && decide (k >= 7) = true := by
            simpa [handles, selectedTarget, hk4, hk5, hk6] using hhandles
          exact (Bool.and_eq_true_iff.mp hselected).1
    simpa [generatedPoints, h3, h4, h5, h6] using
      OptimizedParity.generatedPoints_valid_scored mode k hscore

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem generate_safe
    (mode : ProductMode) (k : Nat) (hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointOrder (generatedPoints mode k) (generatePointsInOrder mode k hk) /\
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  by_cases h3 : mode = .PhaseProduct ∧ k = 3
  · rcases h3 with ⟨rfl, rfl⟩
    have hhk : hk = (by decide : 3 >= 2) := Subsingleton.elim _ _
    subst hk
    constructor
    · exact List.Perm.refl _
    · apply progConsumesPtsSafe_of_checks <;> decide
  by_cases h4 : mode = .PhaseTripleProduct ∧ k = 4
  · rcases h4 with ⟨rfl, rfl⟩
    have hhk : hk = (by decide : 4 >= 2) := Subsingleton.elim _ _
    subst hk
    constructor
    · exact List.Perm.refl _
    · apply progConsumesPtsSafe_of_checks <;> decide
  by_cases h5 : mode = .PhaseTripleProduct ∧ k = 5
  · rcases h5 with ⟨rfl, rfl⟩
    have hhk : hk = (by decide : 5 >= 2) := Subsingleton.elim _ _
    subst hk
    constructor
    · exact List.Perm.refl _
    · apply progConsumesPtsSafe_of_checks <;> decide
  by_cases h6 : mode = .PhaseTripleProduct ∧ k = 6
  · rcases h6 with ⟨rfl, rfl⟩
    have hhk : hk = (by decide : 6 >= 2) := Subsingleton.elim _ _
    subst hk
    constructor
    · exact List.Perm.refl _
    · apply progConsumesPtsSafe_of_checks <;> decide
  · have hscore : OptimizedParity.scoredK k = true := by
      cases mode with
      | PhaseProduct =>
          have hk3 : k ≠ 3 := fun hk => h3 ⟨rfl, hk⟩
          simpa [handles, selectedTarget, hk3] using hhandles
      | PhaseTripleProduct =>
          have hk4 : k ≠ 4 := fun hk => h4 ⟨rfl, hk⟩
          have hk5 : k ≠ 5 := fun hk => h5 ⟨rfl, hk⟩
          have hk6 : k ≠ 6 := fun hk => h6 ⟨rfl, hk⟩
          have hselected :
              OptimizedParity.scoredK k && decide (k >= 7) = true := by
            simpa [handles, selectedTarget, hk4, hk5, hk6] using hhandles
          exact (Bool.and_eq_true_iff.mp hselected).1
    simpa [generatedPoints, generatePointsInOrder, generate, h3, h4, h5, h6] using
      OptimizedParity.generate_safe_scored mode k hk hscore

def implementation : GeneratorPolicy where
  generatedPoints := generatedPoints
  handles := handles
  generatePointsInOrder := generatePointsInOrder
  generate := generate
  generatedPoints_valid := generatedPoints_valid
  generate_safe := generate_safe

end TableGeneration.Policies.Accepted.Pf4aff955f16b
