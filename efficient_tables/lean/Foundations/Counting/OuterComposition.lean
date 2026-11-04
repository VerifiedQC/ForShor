import Foundations.Counting.BranchCount
import Foundations.Counting.DimensionBound
import Foundations.Counting.TypedWords
import Foundations.Counting.RecursiveCalls

/-!
# Outer composition of counting bounds

Composes the branch-count, dimension and recursive-call bounds from the sibling `Counting` files. States that a branch-product budget bounds a power of the distinct dimension (`distinct_dimension_power_le_budget_power`), that generator invocations are controlled by the alphabet size and candidate count (`generator_calls_le_alphabet_plus_one_mul_candidates_plus_one`), and a conditional composition for a solver cost (`conditional_solver_cost_le_budget_power`).
-/

namespace Paper.CountStage.OuterComplexity

open Paper.CountStage.Bounds
open Paper.CountStage.TypedDecorationWords
open Paper.CountStage.TypedWordRuntime

/-- A branch-product budget on the full word also bounds the factorial of
the number of distinct arities, including words with repetitions. -/
theorem distinct_dimension_power_le_budget_power {ks : List Nat} {U c : Nat}
    (hvalid : ∀ k ∈ ks, 2 ≤ k)
    (hbudget : qProduct ks ≤ U) :
    (distinctArities ks).card ^ (c * (distinctArities ks).card) ≤ U ^ (2 * c) := by
  apply Paper.DimensionStage.factorial_power_dimension_bound
  exact (factorial_distinct_le_qProduct hvalid).trans hbudget

/-- The recursive generator's invocation count is controlled by its alphabet
size and the number of emitted words. This theorem concerns invocations only;
it does not assign costs to list operations, comparisons, or integer arithmetic. -/
theorem generator_calls_le_alphabet_plus_one_mul_candidates_plus_one
    {α : Type} (A : List α) (q : α → Nat) (hq : ∀ a, 3 ≤ q a) (U : Nat) :
    recursiveCalls A q hq U ≤
      (A.length + 1) * (typedBudgetWords A q hq U).length + 1 :=
  recursiveCalls_le_enumeratedSize_bound A q hq U

/-- Conditional arithmetic composition for a solver dimension factor. `hsolver`
is an external algorithmic cost contract; this theorem only substitutes the
proved dimension bound into that contract. -/
theorem conditional_solver_cost_le_budget_power {ks : List Nat} {U c cost : Nat}
    (hvalid : ∀ k ∈ ks, 2 ≤ k)
    (hbudget : qProduct ks ≤ U)
    (hsolver : cost ≤ (distinctArities ks).card ^ (c * (distinctArities ks).card)) :
    cost ≤ U ^ (2 * c) :=
  hsolver.trans (distinct_dimension_power_le_budget_power hvalid hbudget)

end Paper.CountStage.OuterComplexity
