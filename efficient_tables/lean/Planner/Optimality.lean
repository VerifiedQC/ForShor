import Model.Defs
import Planner.DenseSparse

/-!
# Optimality of the recursive planner

States that the planner's choice at each width is a legal plan whose gate count is at most that of every legal candidate. Key results are `chooseAtWidth_legal`, `bestPlan_legal` with `bestPlan_le_all_legal`, and the best-known-catalog versions `bestKnownPlan_legal` and `bestKnownPlan_le_all_legal`.
-/

namespace Paper.PlannerOptimality

open TableGeneration.RecursiveCost

theorem foldl_gate_le_initial {α : Type}
    (step : PlanResult → α → PlanResult) (items : List α)
    (initial : PlanResult)
    (hstep : ∀ p a, (step p a).gateCount ≤ p.gateCount) :
    (items.foldl step initial).gateCount ≤ initial.gateCount := by
  induction items generalizing initial with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (step initial a)) (hstep initial a)

theorem chooseAtWidth_step_le_current
    (plans : Array PlanResult) (width : Nat)
    (current : PlanResult) (c : Candidate) :
    (let analysis := c.analyze width
     if analysis.childWidth < width then
       match plans[analysis.childWidth]? with
       | some child => lowerGateCount (PlanResult.step width c analysis child) current
       | none => current
     else current).gateCount ≤ current.gateCount := by
  dsimp
  by_cases hcontract : (c.analyze width).childWidth < width
  · simp only [hcontract, ↓reduceIte]
    cases hget : plans[(c.analyze width).childWidth]? with
    | none => simp [hget]
    | some child =>
      simpa [hget] using
        lowerGateCount_gateCount_le_current
          (PlanResult.step width c (c.analyze width) child) current
  · simp [hcontract]

theorem chooseAtWidth_le_base (candidates : List Candidate)
    (plans : Array PlanResult) (width : Nat) :
    (chooseAtWidth candidates plans width).gateCount ≤ width * width := by
  unfold chooseAtWidth
  have h := foldl_gate_le_initial
    (fun current c =>
      let analysis := c.analyze width
      if analysis.childWidth < width then
        match plans[analysis.childWidth]? with
        | some child => lowerGateCount (PlanResult.step width c analysis child) current
        | none => current
      else current) candidates (PlanResult.base width)
    (chooseAtWidth_step_le_current plans width)
  simpa using h

theorem foldl_gate_le_member {α : Type}
    (step : PlanResult → α → PlanResult) (items : List α)
    (initial : PlanResult) (item : α) (bound : Nat)
    (hmem : item ∈ items)
    (hstep : ∀ p a, (step p a).gateCount ≤ p.gateCount)
    (hitem : ∀ p, (step p item).gateCount ≤ bound) :
    (items.foldl step initial).gateCount ≤ bound := by
  induction items generalizing initial with
  | nil => simp at hmem
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with heq | htail
    · subst a
      exact le_trans
        (foldl_gate_le_initial step rest (step initial item) hstep)
        (hitem initial)
    · exact ih (step initial a) htail

theorem chooseAtWidth_le_candidate (candidates : List Candidate)
    (plans : Array PlanResult) (width : Nat)
    (candidate : Candidate) (hmem : candidate ∈ candidates)
    (hcontract : (candidate.analyze width).childWidth < width)
    (child : PlanResult)
    (hget : plans[(candidate.analyze width).childWidth]? = some child) :
    (chooseAtWidth candidates plans width).gateCount ≤
      (PlanResult.step width candidate (candidate.analyze width) child).gateCount := by
  unfold chooseAtWidth
  apply foldl_gate_le_member
    (fun current c =>
      let analysis := c.analyze width
      if analysis.childWidth < width then
        match plans[analysis.childWidth]? with
        | some child => lowerGateCount (PlanResult.step width c analysis child) current
        | none => current
      else current) candidates (PlanResult.base width) candidate
    (PlanResult.step width candidate (candidate.analyze width) child).gateCount
    hmem (chooseAtWidth_step_le_current plans width)
  intro current
  simpa [hcontract, hget] using
    lowerGateCount_gateCount_le_candidate
      (PlanResult.step width candidate (candidate.analyze width) child) current

theorem chooseAtWidth_legal (candidates : List Candidate)
    (plans : Array PlanResult) (width : Nat)
    (hchild : ∀ c ∈ candidates,
      (c.analyze width).childWidth < width →
      ∀ child, plans[(c.analyze width).childWidth]? = some child →
        LegalCost candidates (c.analyze width).childWidth child.gateCount) :
    LegalCost candidates width (chooseAtWidth candidates plans width).gateCount := by
  let F : PlanResult → Candidate → PlanResult := fun current c =>
    let analysis := c.analyze width
    if analysis.childWidth < width then
      match plans[analysis.childWidth]? with
      | some child => lowerGateCount (PlanResult.step width c analysis child) current
      | none => current
    else current
  have hstep (current : PlanResult) (c : Candidate)
      (hc : c ∈ candidates)
      (hlegal : LegalCost candidates width current.gateCount) :
      LegalCost candidates width (F current c).gateCount := by
    dsimp [F]
    by_cases hcontract : (c.analyze width).childWidth < width
    · simp only [hcontract, ↓reduceIte]
      cases hget : plans[(c.analyze width).childWidth]? with
      | none => simpa [hget] using hlegal
      | some child =>
        have hcLegal : LegalCost candidates width
            (PlanResult.step width c (c.analyze width) child).gateCount := by
          simpa using
            (LegalCost.step width c hc hcontract child.gateCount
              (hchild c hc hcontract child hget))
        by_cases hbetter :
            (PlanResult.step width c (c.analyze width) child).gateCount <
              current.gateCount
        · have hbetter' :
              (c.analyze width).arithmeticGateCount +
                (c.analyze width).recursiveCallCount * child.gateCount <
                  current.gateCount := by
            simpa only [PlanResult.step_gateCount] using hbetter
          simpa [hget, lowerGateCount, hbetter'] using hcLegal
        · have hbetter' : ¬
              (c.analyze width).arithmeticGateCount +
                (c.analyze width).recursiveCallCount * child.gateCount <
                  current.gateCount := by
            simpa only [PlanResult.step_gateCount] using hbetter
          simpa [hget, lowerGateCount, hbetter'] using hlegal
    · simpa [hcontract] using hlegal
  have hfold (xs : List Candidate) (current : PlanResult)
      (hsub : ∀ c ∈ xs, c ∈ candidates)
      (hlegal : LegalCost candidates width current.gateCount) :
      LegalCost candidates width (xs.foldl F current).gateCount := by
    induction xs generalizing current with
    | nil => simpa using hlegal
    | cons c rest ih =>
      simp only [List.foldl_cons]
      apply ih (F current c)
      · intro d hd
        exact hsub d (by simp [hd])
      · exact hstep current c (hsub c (by simp)) hlegal
  change LegalCost candidates width
    (candidates.foldl F (PlanResult.base width)).gateCount
  apply hfold candidates (PlanResult.base width)
  · intro c hc; exact hc
  · simpa using (LegalCost.base (candidates := candidates) width)

theorem dense_child_lookup (candidates : List Candidate)
    (width childWidth : Nat) (hchild : childWidth < width) :
    (buildPlanTable candidates width)[childWidth]? =
      some (chooseAtWidth candidates
        (buildPlanTable candidates childWidth) childWidth) := by
  calc
    (buildPlanTable candidates width)[childWidth]? =
        (buildPlanTable candidates childWidth)[childWidth]? := by
          rw [PlannerDenseSparse.buildPlanTable_get candidates width childWidth
            (Nat.le_of_lt hchild)]
          rw [PlannerDenseSparse.buildPlanTable_get candidates childWidth childWidth
            (le_refl _)]
    _ = some (chooseAtWidth candidates
          (buildPlanTable candidates childWidth) childWidth) :=
      PlannerDenseSparse.buildPlanTable_fixed candidates childWidth childWidth (le_refl _)

theorem dense_choice_legal_and_le (candidates : List Candidate) (width : Nat) :
    LegalCost candidates width
      (chooseAtWidth candidates (buildPlanTable candidates width) width).gateCount ∧
    (∀ cost, LegalCost candidates width cost →
      (chooseAtWidth candidates (buildPlanTable candidates width) width).gateCount ≤ cost) := by
  induction width using Nat.strong_induction_on with
  | h width ih =>
    constructor
    · apply chooseAtWidth_legal
      intro c hc hcontract child hget
      have hlookup := dense_child_lookup candidates width
        (c.analyze width).childWidth hcontract
      rw [hlookup] at hget
      have hchild : child = chooseAtWidth candidates
          (buildPlanTable candidates (c.analyze width).childWidth)
          (c.analyze width).childWidth := by
        exact Option.some.inj hget.symm
      subst child
      exact (ih (c.analyze width).childWidth hcontract).1
    · intro cost hcost
      cases hcost with
      | base width =>
        exact chooseAtWidth_le_base candidates (buildPlanTable candidates width) width
      | step width c hc hcontract childCost hchild =>
        let child := chooseAtWidth candidates
          (buildPlanTable candidates (c.analyze width).childWidth)
          (c.analyze width).childWidth
        have hlookup :
            (buildPlanTable candidates width)[(c.analyze width).childWidth]? =
              some child :=
          dense_child_lookup candidates width (c.analyze width).childWidth hcontract
        have hchosen :
            (chooseAtWidth candidates (buildPlanTable candidates width) width).gateCount ≤
              (PlanResult.step width c (c.analyze width) child).gateCount :=
          chooseAtWidth_le_candidate candidates (buildPlanTable candidates width)
            width c hc hcontract child hlookup
        have hchildmin : child.gateCount ≤ childCost :=
          (ih (c.analyze width).childWidth hcontract).2 childCost hchild
        have hmul := Nat.mul_le_mul_left
          (c.analyze width).recursiveCallCount hchildmin
        have hcostbound :
            (PlanResult.step width c (c.analyze width) child).gateCount ≤
              (c.analyze width).arithmeticGateCount +
                (c.analyze width).recursiveCallCount * childCost := by
          simpa using Nat.add_le_add_left hmul
            (c.analyze width).arithmeticGateCount
        exact le_trans hchosen hcostbound

theorem bestPlan_legal (candidates : List Candidate) (width : Nat) :
    LegalCost candidates width (bestPlan candidates width).gateCount := by
  rw [PlannerDenseSparse.bestPlan_eq_dense_choice]
  exact (dense_choice_legal_and_le candidates width).1

theorem bestPlan_le_all_legal (candidates : List Candidate) (width cost : Nat)
    (hlegal : LegalCost candidates width cost) :
    (bestPlan candidates width).gateCount ≤ cost := by
  rw [PlannerDenseSparse.bestPlan_eq_dense_choice]
  exact (dense_choice_legal_and_le candidates width).2 cost hlegal

theorem bestKnownPlan_legal (width : Nat) :
    LegalCost bestKnownCandidates width (bestKnownPlan width).gateCount := by
  exact bestPlan_legal bestKnownCandidates width

theorem bestKnownPlan_le_all_legal (width cost : Nat)
    (hlegal : LegalCost bestKnownCandidates width cost) :
    (bestKnownPlan width).gateCount ≤ cost := by
  exact bestPlan_le_all_legal bestKnownCandidates width cost hlegal

end Paper.PlannerOptimality
