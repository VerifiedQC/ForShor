import Provider.Ladders.CatalogTransfer
import Provider.Compression.Result

/-!
# Call-count bound for the actual policy

Relates the recursive call count of a raw F2 source table to its arity
(`rawCalls_eq_branchQ`, with `branchQ t = 2 * t.arity - 1`) and to the product
of branch counts along a list of tables (`rawCalls_product_eq_branchProduct`).
It then bounds the raw cost from below by four times that product
(`rawCost_ge_four_calls_product`) and compares the product with the competitive
budget (`branchProduct_le_competitive_budget`).
-/

namespace Paper.CountStage.ActualPolicyBounds

open Coupled.Formal
open Paper.F2CatalogTransfer
open Paper.PPEndToEnd
open Paper.PrefixPaddingStage

def branchQ {K : Nat} (t : F2Source K) : Nat := 2 * t.arity - 1

def branchProduct {K : Nat} (l : List (F2Source K)) : Nat :=
  (l.map branchQ).prod

theorem rawChildWidth_positive {K : Nat} (t : F2Source K) (w : Nat) :
    1 ≤ t.childWidth w := by
  rw [Paper.CompressionComplete.f2_childWidth_profile]
  unfold Paper.Planner.childWidth
  calc
    1 ≤ 1 + (w / t.source.k +
        max (Paper.PrefixPaddingStage.sourceProfileRaw t).peakA
          ((Paper.PrefixPaddingStage.sourceProfileRaw t).peakB + w % t.source.k)) :=
      Nat.le_add_right 1 _
    _ = w / t.source.k + 1 +
        max (Paper.PrefixPaddingStage.sourceProfileRaw t).peakA
          ((Paper.PrefixPaddingStage.sourceProfileRaw t).peakB + w % t.source.k) := by omega

theorem rawCalls_eq_branchQ {K : Nat} (t : F2Source K) :
    t.calls = branchQ t := by
  change 2 * (t.source.k - 1) + 1 = 2 * t.source.k - 1
  have hk := t.source.hk
  omega

theorem rawCalls_product_eq_branchProduct {K : Nat} (l : List (F2Source K)) :
    (l.map F2Source.calls).prod = branchProduct l := by
  unfold branchProduct
  congr 1
  apply List.map_congr_left
  intro t ht
  exact rawCalls_eq_branchQ t

theorem rawCost_ge_four_calls_product {K : Nat} (price : Nat → Nat)
    (l : List (F2Source K)) (w N v : Nat)
    (hcost : CostL (rawProblem price) l w N v) (hw : 1 ≤ w) :
    4 * N * (l.map F2Source.calls).prod ≤ v := by
  induction hcost with
  | base w N =>
      have hw2 : 1 ≤ w ^ 2 := Nat.one_le_pow 2 w hw
      have hN : N ≤ N * w ^ 2 := by
        simpa using Nat.mul_le_mul_left N hw2
      simp only [List.map_nil, List.prod_nil, Nat.mul_one]
      change 4 * N ≤ leafPP price N w
      unfold leafPP
      calc
        4 * N ≤ 4 * (N * w ^ 2) := Nat.mul_le_mul_left 4 hN
        _ ≤ 4 * (N * w ^ 2) + (N * w ^ 2) * price (N * w ^ 2) :=
          Nat.le_add_right _ _
  | @step c rest w N v hc htail ih =>
      have hcpos : 1 ≤ (rawProblem price).child c w := by
        simpa [rawProblem] using rawChildWidth_positive c w
      have htail' := ih hcpos
      change 4 * N * (c.calls * (rest.map F2Source.calls).prod) ≤
        N * ownPP c.charge (c.childWidth w) + v
      calc
        4 * N * (c.calls * (rest.map F2Source.calls).prod) =
            4 * (N * c.calls) * (rest.map F2Source.calls).prod := by ring
        _ ≤ v := htail'
        _ ≤ N * ownPP c.charge (c.childWidth w) + v := Nat.le_add_left _ _

theorem branchProduct_le_competitive_budget {K : Nat} (price : Nat → Nat)
    (l : List (F2Source K)) (w N v U : Nat)
    (hcost : CostL (rawProblem price) l w N v)
    (hw : 1 ≤ w) (hN : 1 ≤ N) (hbudget : v ≤ U) :
    branchProduct l ≤ U := by
  have hfour := rawCost_ge_four_calls_product price l w N v hcost hw
  rw [rawCalls_product_eq_branchProduct] at hfour
  have hqmul : branchProduct l ≤ N * branchProduct l :=
    by simpa using Nat.mul_le_mul_right (branchProduct l) hN
  have hNmul : 4 * branchProduct l ≤ 4 * N * branchProduct l := by
    calc
      4 * branchProduct l ≤ 4 * (N * branchProduct l) := Nat.mul_le_mul_left 4 hqmul
      _ = 4 * N * branchProduct l := by ring
  have hfour' : 4 * branchProduct l ≤ v := le_trans hNmul hfour
  omega

end Paper.CountStage.ActualPolicyBounds
