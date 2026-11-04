-- Draft only until the exclusive trusted replay releases Lean execution.
import Planner.Optimality
import PhaseProduct.Catalog.CatalogSemantics

/-!
# Soundness of the planner's choice

Shows the dense fold retains its base or stores a step built from an actual
candidate (`chooseAtWidth_base_or_step`), so the root result is either the
direct base or a complete step (`bestPlan_base_or_step`). It reads backpointers:
`bestPlan_eq_base_of_choice_none` and `bestPlan_step_of_choice_some`, with
`bestKnownPlan_step_of_choice_some` for the promoted catalogue.
-/

namespace Paper.ChoiceSoundness

open TableGeneration.RecursiveCost

/-- A fold that either retains its state or produces a tagged item result
    returns its initial state or a result tagged by an item in the list. -/
theorem foldl_preserves_or_selects {α β : Type}
    (step : α → β → α) (selected : β → α → Prop)
    (items : List β) (initial : α)
    (hstep : ∀ state item, step state item = state ∨
      selected item (step state item)) :
    items.foldl step initial = initial ∨
      ∃ item ∈ items, selected item (items.foldl step initial) := by
  induction items generalizing initial with
  | nil =>
      left
      rfl
  | cons item rest ih =>
      rcases ih (step initial item) with hkeep | ⟨chosen, hmem, hselected⟩
      · rcases hstep initial item with hstay | hnew
        · left
          simp only [List.foldl_cons, hkeep]
          exact hstay
        · right
          refine ⟨item, by simp, ?_⟩
          simpa only [List.foldl_cons, hkeep] using hnew
      · right
        refine ⟨chosen, by simp [hmem], ?_⟩
        simpa only [List.foldl_cons] using hselected

/-- The source dense fold retains its base or stores a step built from an
    actual candidate and a successfully looked-up, strictly smaller child. -/
theorem chooseAtWidth_base_or_step (candidates : List Candidate)
    (plans : Array PlanResult) (width : Nat) :
    chooseAtWidth candidates plans width = PlanResult.base width ∨
      ∃ c : Candidate, c ∈ candidates ∧
        (c.analyze width).childWidth < width ∧
        ∃ child : PlanResult,
          plans[(c.analyze width).childWidth]? = some child ∧
          chooseAtWidth candidates plans width =
            PlanResult.step width c (c.analyze width) child := by
  let step : PlanResult → Candidate → PlanResult := fun current c =>
    let analysis := c.analyze width
    if analysis.childWidth < width then
      match plans[analysis.childWidth]? with
      | some child => lowerGateCount (PlanResult.step width c analysis child) current
      | none => current
    else current
  let selected : Candidate → PlanResult → Prop := fun c result =>
    (c.analyze width).childWidth < width ∧
    ∃ child : PlanResult,
      plans[(c.analyze width).childWidth]? = some child ∧
      result = PlanResult.step width c (c.analyze width) child
  have hstep : ∀ current c,
      step current c = current ∨ selected c (step current c) := by
    intro current c
    dsimp [step, selected]
    by_cases hcontract : (c.analyze width).childWidth < width
    · simp only [if_pos hcontract]
      cases hget : plans[(c.analyze width).childWidth]? with
      | none =>
          left
          simp [hget]
      | some child =>
          by_cases hbetter :
              (PlanResult.step width c (c.analyze width) child).gateCount <
                current.gateCount
          · right
            refine ⟨hcontract, child, rfl, ?_⟩
            have hbetter' :
                (c.analyze width).arithmeticGateCount +
                  (c.analyze width).recursiveCallCount * child.gateCount <
                    current.gateCount := by
              simpa only [PlanResult.step_gateCount] using hbetter
            simp [hget, lowerGateCount, hbetter']
          · left
            have hbetter' : ¬
                (c.analyze width).arithmeticGateCount +
                  (c.analyze width).recursiveCallCount * child.gateCount <
                    current.gateCount := by
              simpa only [PlanResult.step_gateCount] using hbetter
            simp [hget, lowerGateCount, hbetter']
    · left
      simp [hcontract]
  have hfold := foldl_preserves_or_selects step selected candidates
    (PlanResult.base width) hstep
  simpa only [chooseAtWidth, step, selected] using hfold

/-- The actual sparse root result is either the direct base or the complete
    source step record built from the actual optimal child plan. -/
theorem bestPlan_base_or_step (candidates : List Candidate) (width : Nat) :
    bestPlan candidates width = PlanResult.base width ∨
      ∃ c : Candidate, c ∈ candidates ∧
        (c.analyze width).childWidth < width ∧
        bestPlan candidates width =
          PlanResult.step width c (c.analyze width)
            (bestPlan candidates (c.analyze width).childWidth) := by
  rcases chooseAtWidth_base_or_step candidates
      (buildPlanTable candidates width) width with
    hbase | ⟨c, hmem, hcontract, child, hget, hresult⟩
  · left
    rw [PlannerDenseSparse.bestPlan_eq_dense_choice]
    exact hbase
  · right
    have hlookup :
        (buildPlanTable candidates width)[(c.analyze width).childWidth]? =
          some (bestPlan candidates (c.analyze width).childWidth) := by
      rw [PlannerDenseSparse.bestPlan_eq_dense_choice]
      exact PlannerOptimality.dense_child_lookup candidates width
        (c.analyze width).childWidth hcontract
    rw [hlookup] at hget
    have hchild : child =
        bestPlan candidates (c.analyze width).childWidth :=
      (Option.some.inj hget).symm
    subst child
    refine ⟨c, hmem, hcontract, ?_⟩
    rw [PlannerDenseSparse.bestPlan_eq_dense_choice]
    exact hresult

/-- Absence of a stored backpointer identifies the exact direct-base record. -/
theorem bestPlan_eq_base_of_choice_none (candidates : List Candidate)
    (width : Nat)
    (hchoice : (bestPlan candidates width).choice = none) :
    bestPlan candidates width = PlanResult.base width := by
  rcases bestPlan_base_or_step candidates width with hbase | ⟨c, _, _, hstep⟩
  · exact hbase
  · rw [hstep] at hchoice
    cases hchoice

/-- A stored backpointer has an actual candidate in the supplied catalog,
    a contracting child, and exact equality of the whole source PlanResult. -/
theorem bestPlan_step_of_choice_some (candidates : List Candidate)
    (width : Nat) (s : StepChoice)
    (hchoice : (bestPlan candidates width).choice = some s) :
    ∃ c : Candidate, c ∈ candidates ∧
      (c.analyze width).childWidth < width ∧
      bestPlan candidates width =
        PlanResult.step width c (c.analyze width)
          (bestPlan candidates (c.analyze width).childWidth) ∧
      (PlanResult.step width c (c.analyze width)
        (bestPlan candidates (c.analyze width).childWidth)).choice = some s := by
  rcases bestPlan_base_or_step candidates width with hbase | ⟨c, hmem, hcontract, hstep⟩
  · rw [hbase] at hchoice
    cases hchoice
  · refine ⟨c, hmem, hcontract, hstep, ?_⟩
    rw [hstep] at hchoice
    exact hchoice

/-- For the promoted catalog, the witnessed step uses an actual source
    BestKnown PhaseProduct program; no policy-key uniqueness is assumed. -/
theorem bestKnownPlan_step_of_choice_some (width : Nat) (s : StepChoice)
    (hchoice : (bestKnownPlan width).choice = some s) :
    ∃ c : Candidate, c ∈ bestKnownCandidates ∧
      c.program = TableGeneration.bestKnownGenerate
        .PhaseProduct c.k c.hk ∧
      (c.analyze width).childWidth < width ∧
      bestKnownPlan width =
        PlanResult.step width c (c.analyze width)
          (bestPlan bestKnownCandidates (c.analyze width).childWidth) ∧
      (PlanResult.step width c (c.analyze width)
        (bestPlan bestKnownCandidates (c.analyze width).childWidth)).choice = some s := by
  change (bestPlan bestKnownCandidates width).choice = some s at hchoice
  rcases bestPlan_step_of_choice_some bestKnownCandidates width s hchoice with
    ⟨c, hmem, hcontract, hstep, hstored⟩
  exact ⟨c, hmem, CatalogSemantics.member_program c hmem,
    hcontract, hstep, hstored⟩

end Paper.ChoiceSoundness
