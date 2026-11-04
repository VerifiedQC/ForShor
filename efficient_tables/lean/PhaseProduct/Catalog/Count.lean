import PhaseProduct.Catalog.Schoolbook
import PhaseProduct.Catalog.TableSemantics
import Planner.PolicyOptimality

/-!
# Benchmark cost as a census

Expresses the benchmark cost of a policy through its census of adder ANDs and
leaf rotations (`benchmarkCost_eq_census`), and relates leaf rotations to
scheduled cells (`leafRotations_eq_scheduled_cells`). The lemmas
`policyFromTrace_of_cost` and `policyFromTrace_to_cost` relate policies built
from a trace to the cost.
-/

namespace Paper.PPEndToEnd

theorem benchmarkCost_eq_census {K W : Nat} (price : Nat → Nat)
    (policy : PPPolicy K W) (N : Nat) :
    policy.benchmarkCost price N =
      4 * (policy.adderAnds N + policy.leafRotations N) +
        policy.leafRotations N * price (policy.leafRotations N) := by
  induction policy generalizing N with
  | leaf W => simp [PPPolicy.benchmarkCost, PPPolicy.adderAnds,
      PPPolicy.leafRotations, leafPP]
  | @node W table h child ih =>
      simp only [PPPolicy.benchmarkCost, PPPolicy.adderAnds, PPPolicy.leafRotations]
      rw [ih]
      unfold ownPP
      ring

theorem leafRotations_eq_scheduled_cells {K W : Nat} (N : Nat) (a c : BitVec W) :
    (PPPolicy.leaf (K := K) W).leafRotations N =
      N * (schoolbookCells a c).length := by
  simp [PPPolicy.leafRotations, schoolbookCells_length]

theorem policyFromTrace_of_cost {K : Nat} {ι : Type}
    (price : Nat → Nat) (entry : ι → VerifiedPPCandidate K)
    {l : List ι} {W N v : Nat}
    (hc : Coupled.Formal.CostL (ppProblem price entry) l W N v) :
    ∃ policy, policyFromTrace entry l W = some policy ∧
      policy.benchmarkCost price N = v := by
  induction hc with
  | base W N => exact ⟨.leaf W, rfl, rfl⟩
  | step c l W N v h hc ih =>
      obtain ⟨child, hp, hv⟩ := ih
      dsimp only [ppProblem] at h hp hv
      refine ⟨.node (entry c) h child, ?_, ?_⟩
      · simp only [policyFromTrace, h, ↓reduceDIte, hp, Option.map_some]
      · simpa only [PPPolicy.benchmarkCost, ppProblem, hv]

theorem policyFromTrace_to_cost {K : Nat} {ι : Type}
    (price : Nat → Nat) (entry : ι → VerifiedPPCandidate K)
    (l : List ι) (W N : Nat) (policy : PPPolicy K W)
    (hp : policyFromTrace entry l W = some policy) :
    Coupled.Formal.CostL (ppProblem price entry) l W N
      (policy.benchmarkCost price N) := by
  induction l generalizing W N with
  | nil =>
      simp only [policyFromTrace, Option.some.injEq] at hp
      subst policy
      exact .base W N
  | cons c rest ih =>
      simp only [policyFromTrace] at hp
      split at hp
      next h =>
        cases he : policyFromTrace entry rest ((entry c).childWidth W) with
        | none => simp [he] at hp
        | some child =>
            simp only [he, Option.map_some, Option.some.injEq] at hp
            subst policy
            exact .step c rest W N _ h
              (ih _ _ child he)
      next h => simp at hp

end Paper.PPEndToEnd
