import Source.RecursiveCorrectness

/-!
# Local lemmas for the recursive planner

Local properties of the planner's per-width choice. Proves the width of the base and step results (`base_width`, `step_width`), that folding and choosing preserve the width (`chooseAtWidth_width`), and that the sparse choice equals the dense choice given a child lookup (`chooseAtWidthSparse_eq_chooseAtWidth_of_child_lookup`).
-/

namespace Paper.RecursivePlannerLocal

open TableGeneration.RecursiveCost

theorem base_width (width : Nat) : (PlanResult.base width).width = width := by
  rfl

theorem step_width (width : Nat) (candidate : Candidate)
    (analysis : ProgramAnalysis) (child : PlanResult) :
    (PlanResult.step width candidate analysis child).width = width := by
  rfl

theorem lowerGateCount_width (candidate current : PlanResult) (width : Nat)
    (hc : candidate.width = width) (hr : current.width = width) :
    (lowerGateCount candidate current).width = width := by
  by_cases h : candidate.gateCount < current.gateCount
  · simpa [lowerGateCount, h] using hc
  · simpa [lowerGateCount, h] using hr

theorem lowerGateCount_tie_full (candidate current : PlanResult)
    (h : candidate.gateCount = current.gateCount) :
    lowerGateCount candidate current = current :=
  TableGeneration.RecursiveCost.lowerGateCount_tie_keeps_current candidate current h

theorem foldl_width {α : Type} (f : PlanResult → α → PlanResult)
    (xs : List α) (initial : PlanResult) (width : Nat)
    (hinit : initial.width = width)
    (hstep : ∀ p a, p.width = width → (f p a).width = width) :
    (xs.foldl f initial).width = width := by
  suffices h : ∀ (ys : List α) (start : PlanResult), start.width = width →
      (ys.foldl f start).width = width from h xs initial hinit
  intro ys
  induction ys with
  | nil => intro start hs; simpa using hs
  | cons a ys ih =>
    intro start hs
    simp only [List.foldl_cons]
    exact ih (f start a) (hstep start a hs)

theorem chooseAtWidthSparse_width (candidates : List Candidate)
    (plans : List PlanResult) (width : Nat) :
    (chooseAtWidthSparse candidates plans width).width = width := by
  unfold chooseAtWidthSparse
  apply foldl_width
  · rfl
  · intro current candidate hcurrent
    dsimp
    by_cases h : (candidate.analyze width).childWidth < width
    · simp only [h, ↓reduceIte]
      cases hget : findPlan? plans (candidate.analyze width).childWidth with
      | none => simpa [hget] using hcurrent
      | some child =>
        exact lowerGateCount_width
          (PlanResult.step width candidate (candidate.analyze width) child)
          current width (by rfl) hcurrent
    · simpa [h] using hcurrent

theorem chooseAtWidth_width (candidates : List Candidate)
    (plans : Array PlanResult) (width : Nat) :
    (chooseAtWidth candidates plans width).width = width := by
  unfold chooseAtWidth
  apply foldl_width
  · rfl
  · intro current candidate hcurrent
    dsimp
    by_cases h : (candidate.analyze width).childWidth < width
    · simp only [h, ↓reduceIte]
      cases hget : plans[(candidate.analyze width).childWidth]? with
      | none => simpa [hget] using hcurrent
      | some child =>
        exact lowerGateCount_width
          (PlanResult.step width candidate (candidate.analyze width) child)
          current width (by rfl) hcurrent
    · simpa [h] using hcurrent

theorem chooseAtWidthSparse_eq_chooseAtWidth_of_child_lookup
    (candidates : List Candidate) (sparse : List PlanResult)
    (dense : Array PlanResult) (width : Nat)
    (hlookup : ∀ c ∈ candidates,
      (c.analyze width).childWidth < width →
      findPlan? sparse (c.analyze width).childWidth =
        dense[(c.analyze width).childWidth]?) :
    chooseAtWidthSparse candidates sparse width =
      chooseAtWidth candidates dense width := by
  let ss : PlanResult → Candidate → PlanResult := fun current c =>
    let analysis := c.analyze width
    if analysis.childWidth < width then
      match findPlan? sparse analysis.childWidth with
      | some child => lowerGateCount (PlanResult.step width c analysis child) current
      | none => current
    else current
  let ds : PlanResult → Candidate → PlanResult := fun current c =>
    let analysis := c.analyze width
    if analysis.childWidth < width then
      match dense[analysis.childWidth]? with
      | some child => lowerGateCount (PlanResult.step width c analysis child) current
      | none => current
    else current
  have hstep (current : PlanResult) (c : Candidate) (hc : c ∈ candidates) :
      ss current c = ds current c := by
    dsimp [ss, ds]
    by_cases h : (c.analyze width).childWidth < width
    · simp [h, hlookup c hc h]
    · simp [h]
  have hfold (cs : List Candidate) (hsub : ∀ c ∈ cs, c ∈ candidates) :
      ∀ current : PlanResult, cs.foldl ss current = cs.foldl ds current := by
    induction cs with
    | nil => intro current; rfl
    | cons c cs ih =>
      intro current
      have hc : c ∈ candidates := hsub c (by simp)
      have ht : ∀ x ∈ cs, x ∈ candidates := by
        intro x hx
        exact hsub x (by simp [hx])
      simp only [List.foldl_cons]
      rw [hstep current c hc]
      exact ih ht (ds current c)
  change candidates.foldl ss (PlanResult.base width) =
    candidates.foldl ds (PlanResult.base width)
  exact hfold candidates (by intro c hc; exact hc) (PlanResult.base width)

end Paper.RecursivePlannerLocal
