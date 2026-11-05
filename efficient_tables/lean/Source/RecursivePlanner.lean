import Source.Catalog

/-!
# Recursive planner definitions

Defines the recursive planner's data and operations: `StepChoice`, the per-width summary `PlanResult`, the direct schoolbook plan `PlanResult.base`, and `PlanResult.step` composing a table program with its optimized child. Also fixes `modelVersion` and `objective` (`logical_gate_count`) and keeps the existing plan on a gate-count tie.
-/

namespace TableGeneration.RecursiveCost

/-- Version attached to every result produced by this cost model. -/
def modelVersion : String := "forshor-phase-product-gates-v1"

/-- Stable machine-readable optimization objective. -/
def objective : String := "logical_gate_count"

/-- The local recursive choice retained as a compact plan backpointer. -/
structure StepChoice where
  policyId : String
  k : Nat
  childWidth : Nat
  localArithmeticGateCount : Nat
  localArithmeticOperationCount : Nat
  recursiveCallCount : Nat
deriving Repr, DecidableEq

/-- Minimum-gate summary for one balanced PhaseProduct input width. -/
structure PlanResult where
  width : Nat
  gateCount : Nat
  recursionHeight : Nat
  totalRecursiveCallCount : Nat
  totalArithmeticOperationCount : Nat
  choice : Option StepChoice
deriving Repr, DecidableEq

namespace PlanResult

/-- Direct schoolbook PhaseProduct at one width. -/
def base (width : Nat) : PlanResult where
  width
  gateCount := directSignedPhaseProductGateCount width width
  recursionHeight := 0
  totalRecursiveCallCount := 0
  totalArithmeticOperationCount := 0
  choice := none

/-- Compose one recursive table program with its already optimized child. -/
def step
    (width : Nat) (candidate : Candidate) (analysis : ProgramAnalysis)
    (child : PlanResult) : PlanResult :=
  let calls := analysis.recursiveCallCount
  { width
    gateCount := analysis.arithmeticGateCount + calls * child.gateCount
    recursionHeight := child.recursionHeight + 1
    totalRecursiveCallCount := calls * (child.totalRecursiveCallCount + 1)
    totalArithmeticOperationCount :=
      analysis.arithmeticOperationCount +
        calls * child.totalArithmeticOperationCount
    choice := some
      { policyId := candidate.policyId
        k := candidate.k
        childWidth := analysis.childWidth
        localArithmeticGateCount := analysis.arithmeticGateCount
        localArithmeticOperationCount := analysis.arithmeticOperationCount
        recursiveCallCount := calls } }

end PlanResult

/-- Keep the existing plan on a gate-count tie for deterministic selection. -/
def lowerGateCount (candidate current : PlanResult) : PlanResult :=
  if candidate.gateCount < current.gateCount then candidate else current

/--
Dense reference recurrence: choose the minimum-gate plan for `width` from
children already computed at every smaller width. Noncontracting recursive
candidates are rejected.
-/
def chooseAtWidth
    (candidates : List Candidate) (plans : Array PlanResult)
    (width : Nat) : PlanResult :=
  candidates.foldl (fun current candidate =>
    let analysis := candidate.analyze width
    if analysis.childWidth < width then
      match plans[analysis.childWidth]? with
      | some child =>
          lowerGateCount (PlanResult.step width candidate analysis child) current
      | none => current
    else
      current) (PlanResult.base width)

/--
Readable dense reference planner for every width through `maxWidth`. The
production entry point `bestPlan` uses the equivalent sparse planner below.
-/
def buildPlanTable
    (candidates : List Candidate) (maxWidth : Nat) : Array PlanResult :=
  (List.range (maxWidth + 1)).foldl
    (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]

/-- Minimum-gate plan at `width`, with a direct base-case fallback. -/
def findPlan? (plans : List PlanResult) (width : Nat) : Option PlanResult :=
  plans.find? (fun plan => plan.width == width)

/-- Add every unseen, strictly contracting child of `width` to the worklist. -/
def enqueueContractingChildren
    (candidates : List Candidate) (width : Nat)
    (seen pending : List Nat) : List Nat :=
  candidates.foldl (fun pending candidate =>
    let childWidth := (candidate.analyze width).childWidth
    if childWidth < width &&
        !seen.contains childWidth && !pending.contains childWidth then
      childWidth :: pending
    else
      pending) pending

/-- Worklist traversal bounded by the number of widths no greater than the root. -/
def reachableWidthsAux
    (candidates : List Candidate) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, width :: pending, seen =>
      let pending' := enqueueContractingChildren candidates width seen pending
      reachableWidthsAux candidates fuel pending' (width :: seen)

/-- Widths needed to answer all supplied root queries. -/
def reachableWidths (candidates : List Candidate) (roots : List Nat) : List Nat :=
  let maxWidth := roots.foldl max 0
  reachableWidthsAux candidates (maxWidth + 1) roots.eraseDups []

/-- Production recurrence using plans for reachable children only. -/
def chooseAtWidthSparse
    (candidates : List Candidate) (plans : List PlanResult)
    (width : Nat) : PlanResult :=
  candidates.foldl (fun current candidate =>
    let analysis := candidate.analyze width
    if analysis.childWidth < width then
      match findPlan? plans analysis.childWidth with
      | some child =>
          lowerGateCount (PlanResult.step width candidate analysis child) current
      | none => current
    else
      current) (PlanResult.base width)

/--
Production planner for widths reachable from `roots`. Sorting them first
preserves the dense reference recurrence without rescanning every intermediate
integer width.
-/
def buildSparsePlans
    (candidates : List Candidate) (roots : List Nat) : List PlanResult :=
  (reachableWidths candidates roots).mergeSort.foldl
    (fun plans width => chooseAtWidthSparse candidates plans width :: plans) []

/-- Minimum-gate plan at `width`, with a direct base-case fallback. -/
def bestPlan (candidates : List Candidate) (width : Nat) : PlanResult :=
  (findPlan? (buildSparsePlans candidates [width]) width).getD
    (PlanResult.base width)

/-- Minimum-gate plan using the current promoted PhaseProduct catalog. -/
def bestKnownPlan (width : Nat) : PlanResult :=
  bestPlan bestKnownCandidates width

end TableGeneration.RecursiveCost
