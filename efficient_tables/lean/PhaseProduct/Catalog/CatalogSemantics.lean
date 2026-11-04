import Source.Catalog
import PhaseProduct.Catalog.BestKnownPhase
import Model.Scanner.ArrayScanner

/-!
# Catalogue semantics

Reads off the properties of a catalogue `Candidate`: child width, recursive
call count and arithmetic operation count (`candidate_childWidth_eq_scan`,
`candidate_recursiveCallCount`). For a catalogue member it derives shape, bounds,
safety, consumption, restoration and the pair phase (`member_safe_contract`,
`member_integer_trace`, `member_pair_phase`).
-/

namespace Paper.CatalogSemantics

open TableGeneration TableGeneration.Operations
open TableGeneration.RecursiveCost

theorem candidate_childWidth_eq_scan (candidate : Candidate) (width : Nat) :
    (candidate.analyze width).childWidth =
      1 + (Scanner.scan
        (FullDSL.widthWord (SourceBridge.mapToFull candidate.program))
        (Scanner.fresh (ArrayBridge.literalSourceSplit width candidate.k))).peak := by
  change nextBalancedSignedWidth width candidate.program = _
  exact ArrayBridge.nextBalancedSignedWidth_eq_full_widthWord width candidate.program

theorem candidate_recursiveCallCount (candidate : Candidate) (width : Nat) :
    (candidate.analyze width).recursiveCallCount =
      phaseProductCount candidate.program := rfl

theorem candidate_arithmeticOperationCount (candidate : Candidate) (width : Nat) :
    (candidate.analyze width).arithmeticOperationCount =
      arithmeticOperationCount candidate.program := rfl

theorem member_shape (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) :
    ∃ (k : Nat) (hk : 2 ≤ k), k ≤ 16 ∧
      candidate = bestKnownCandidate k hk := by
  simp only [bestKnownCandidates, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst candidate
  all_goals exact ⟨_, _, by decide, rfl⟩

theorem member_k_bounds (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) :
    2 ≤ candidate.k ∧ candidate.k ≤ 16 := by
  obtain ⟨k, hk, hle, heq⟩ := member_shape candidate hmem
  subst candidate
  exact ⟨hk, hle⟩

theorem member_program (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) :
    candidate.program = bestKnownGenerate .PhaseProduct candidate.k candidate.hk := by
  obtain ⟨k, hk, _, heq⟩ := member_shape candidate hmem
  subst candidate
  rfl

theorem member_safe_contract (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) :
    ValidPointOrder
        (bestKnownGeneratedPoints .PhaseProduct candidate.k)
        (bestKnownGeneratePointsInOrder .PhaseProduct candidate.k candidate.hk) ∧
      ProgConsumesPtsSafe (positive_of_ge_two candidate.hk) State.start_state
        candidate.program
        (bestKnownGeneratePointsInOrder .PhaseProduct candidate.k candidate.hk) := by
  rw [member_program candidate hmem]
  exact BestKnownContract.bestKnownGenerate_safe .PhaseProduct candidate.k candidate.hk

theorem member_ordered_points_valid (candidate : Candidate)
    (_hmem : candidate ∈ bestKnownCandidates) :
    ValidPointList .PhaseProduct candidate.k
      (bestKnownGeneratePointsInOrder .PhaseProduct candidate.k candidate.hk) :=
  BestKnownContract.bestKnownOrderedPoints_valid .PhaseProduct candidate.k candidate.hk

theorem member_ordered_points_has_infinity (candidate : Candidate)
    (_hmem : candidate ∈ bestKnownCandidates) :
    Point.frac 0 ∈
      bestKnownGeneratePointsInOrder .PhaseProduct candidate.k candidate.hk :=
  BestKnownPhase.bestKnownOrderedPoints_has_infinity .PhaseProduct candidate.k candidate.hk

theorem member_safe (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) :
    safeProg? candidate.program = true :=
  (member_safe_contract candidate hmem).2.safe_add

theorem member_consumes (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) :
    progConsumesPts? (positive_of_ge_two candidate.hk) State.start_state
      candidate.program
      (bestKnownGeneratePointsInOrder .PhaseProduct candidate.k candidate.hk) = true :=
  (member_safe_contract candidate hmem).2.consumes

theorem member_restores (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) :
    returnsToStartCheck candidate.program State.start_state = true :=
  (member_safe_contract candidate hmem).2.returns_start

theorem member_integer_trace (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates)
    (x : ValueSemantics.Values candidate.k) :
    ValueSemantics.valueTrace (SourceBridge.mapToFull candidate.program) x =
      some (x,
        (bestKnownGeneratePointsInOrder .PhaseProduct candidate.k candidate.hk).map
          (fun p => ValueSemantics.evalRow (expectedRow p) x)) := by
  exact ValueSemantics.source_contract_valueTrace
    (positive_of_ge_two candidate.hk) candidate.program
    (bestKnownGeneratePointsInOrder .PhaseProduct candidate.k candidate.hk) x
    (member_safe_contract candidate hmem).2

theorem member_pair_phase (candidate : Candidate)
    (hmem : candidate ∈ bestKnownCandidates) (b : ℚ) :
    ∃ (w : Fin (2*(candidate.k-1)+1) → ℚ),
      ∀ (x z : ValueSemantics.Values candidate.k),
      ∃ (xs zs : List Int),
        ValueSemantics.valueTrace
          (SourceBridge.mapToFull candidate.program) x = some (x,xs) ∧
        ValueSemantics.valueTrace
          (SourceBridge.mapToFull candidate.program) z = some (z,zs) ∧
        xs.length = 2*candidate.k-1 ∧ zs.length = 2*candidate.k-1 ∧
        (∑ l, w l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
          (∑ j : Fin candidate.k, b^j.val * (x j : ℚ)) *
          (∑ j : Fin candidate.k, b^j.val * (z j : ℚ)) := by
  rw [member_program candidate hmem]
  exact BestKnownPhase.bestKnown_pair_phase candidate.k candidate.hk b

end Paper.CatalogSemantics
