import Planner.TauPrice
import Model.Defs
import Foundations.Counting.TypedWords
import Foundations.Counting.RecursiveCalls
import Foundations.Counting.DimensionBound
import Foundations.Counting.BranchCount

/-! # Stop Budget Numeric Bounds
Defines `rootStopBudget` and proves explicit numeric bounds: `tauExact_le_thousand_mul_succ`, `rootStopBudget_le_2004_n4` (a quartic bound in the numeric parameter) and `candidates_le_explicit_numeric_bound`. These are parameter bounds only; the file makes no polynomial-in-bitlength claim.
-/

namespace Paper.CountStage.StopBudget

open Paper.PPEndToEnd
open Paper.CountStage.TypedDecorationWords
open Paper.CountStage.TypedWordRuntime
open Paper.CountStage.Bounds

/-- Raising a positive integer to the fixed power 615 multiplies its base-2
logarithm by at most 615, with one unit of rounding slack. -/
theorem log2_pow_615_le (x : Nat) :
    Nat.log2 (x ^ 615) ≤ 615 * (Nat.log2 x + 1) := by
  by_cases hx : x = 0
  · simp [hx]
  have hlt : x < 2 ^ (Nat.log2 x + 1) := by
    simpa [Nat.log2_eq_log_two] using
      (Nat.lt_pow_succ_log_self Nat.one_lt_two x)
  have hp : x ^ 615 < (2 ^ (Nat.log2 x + 1)) ^ 615 :=
    Nat.pow_lt_pow_left hlt (by norm_num)
  have hp' : x ^ 615 < 2 ^ (615 * (Nat.log2 x + 1)) := by
    simpa [Nat.pow_mul, Nat.mul_comm] using hp
  have hxpow : x ^ 615 ≠ 0 := pow_ne_zero 615 hx
  have hlog := Nat.log_lt_of_lt_pow hxpow hp'
  have hlog2 : Nat.log2 (x ^ 615) < 615 * (Nat.log2 x + 1) := by
    simpa [Nat.log2_eq_log_two] using hlog
  omega

/-- The executable tau cutoff is at most linear in its numeric argument. -/
theorem tauExact_le_thousand_mul_succ (R : Nat) :
    tauExact R ≤ 1000 * (R + 1) := by
  by_cases hR : R = 0
  · simp [tauExact, hR]
  have hRpos : 0 < R := Nat.pos_of_ne_zero hR
  have hxpos : 0 < 100 * R := by positivity
  have hlog := log2_pow_615_le (100 * R)
  have hlogself : Nat.log2 (100 * R) ≤ 100 * R := by
    simpa [Nat.log2_eq_log_two] using Nat.log_le_self 2 (100 * R)
  have hnum : Nat.log2 ((100 * R) ^ 615) + 272 ≤
      200 * (1000 * (R + 1)) := by
    omega
  rw [tauExact, if_neg hR]
  exact Nat.div_le_of_le_mul hnum

/-- The stop budget for a root leaf at multiplicity one is a quartic
polynomial in the numeric parameter. -/
def rootStopBudget (n : Nat) : Nat := Paper.PPEndToEnd.leafPP tauExact 1 n

theorem rootStopBudget_le_2004_n4 {n : Nat} (hn : 1 ≤ n) :
    rootStopBudget n ≤ 2004 * n ^ 4 := by
  have htau := tauExact_le_thousand_mul_succ (n ^ 2)
  have hprice : tauExact (n ^ 2) ≤ 2000 * n ^ 2 := by
    calc
      tauExact (n ^ 2) ≤ 1000 * (n ^ 2 + 1) := htau
      _ ≤ 2000 * n ^ 2 := by nlinarith
  have hn2pos : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n hn
  have hnle : n ≤ n ^ 2 := by nlinarith
  have hn24 : n ^ 2 ≤ n ^ 4 := by
    calc
      n ^ 2 ≤ (n ^ 2) ^ 2 := (Nat.pow_le_pow_left hnle) 2
      _ = n ^ 4 := by rw [← pow_mul]
  unfold rootStopBudget Paper.PPEndToEnd.leafPP
  simp only [Nat.one_mul]
  calc
    4 * n ^ 2 + n ^ 2 * tauExact (n ^ 2) ≤ 4 * n ^ 2 + n ^ 2 * (2000 * n ^ 2) := by
      gcongr
    _ = 4 * n ^ 2 + 2000 * n ^ 4 := by ring
    _ ≤ 2004 * n ^ 4 := by nlinarith

/-- Candidate count after substituting the root stop budget. This is a numeric
parameter bound; it makes no polynomial-in-bitlength claim. -/
theorem candidates_le_explicit_numeric_bound {K n : Nat} (hn : 1 ≤ n) :
    (typedBudgetWords (decorationLabels K) labelQ
      (fun x => by have hk := x.arity.property; unfold labelQ; omega)
      (rootStopBudget n)).length ≤
      3 * 2004 ^ 10 * n ^ 40 := by
  have hc := actualDecorationWords_count_lt_three_U10 K (rootStopBudget n)
    (by
      have hpos : 1 ≤ rootStopBudget n := by
        unfold rootStopBudget Paper.PPEndToEnd.leafPP
        simp only [Nat.one_mul]
        nlinarith [Nat.one_le_pow 2 n hn, Nat.zero_le (tauExact (n ^ 2))]
      exact hpos)
  have hc' : ((typedBudgetWords (decorationLabels K) labelQ
      (fun x => by have hk := x.arity.property; unfold labelQ; omega)
      (rootStopBudget n)).length : ℚ) <
        3 * ((rootStopBudget n : Nat) : ℚ) ^ 10 := hc
  have hnat : (typedBudgetWords (decorationLabels K) labelQ
      (fun x => by have hk := x.arity.property; unfold labelQ; omega)
      (rootStopBudget n)).length < 3 * (rootStopBudget n) ^ 10 := by
    exact_mod_cast hc'
  have hu := rootStopBudget_le_2004_n4 hn
  have hpow : (rootStopBudget n) ^ 10 ≤ (2004 * n ^ 4) ^ 10 :=
    (Nat.pow_le_pow_left hu) 10
  have hfinal : 3 * (rootStopBudget n) ^ 10 ≤ 3 * 2004 ^ 10 * n ^ 40 := by
    calc
      3 * (rootStopBudget n) ^ 10 ≤ 3 * (2004 * n ^ 4) ^ 10 :=
        Nat.mul_le_mul_left 3 hpow
      _ = 3 * 2004 ^ 10 * n ^ 40 := by ring
  exact (Nat.le_of_lt hnat).trans hfinal

/-- If the feasible branch product is charged against the root stop budget,
the dimension factor `t^(c*t)` is bounded by the explicit numeric polynomial. -/
theorem dimension_cost_le_explicit_numeric_bound {ks : List Nat} {n c : Nat}
    (hn : 1 ≤ n) (hvalid : ∀ k ∈ ks, 2 ≤ k)
    (hbudget : qProduct ks ≤ rootStopBudget n) :
    (distinctArities ks).card ^ (c * (distinctArities ks).card) ≤
      2004 ^ (2 * c) * n ^ (8 * c) := by
  have hfac := factorial_distinct_le_qProduct hvalid
  have hdim := Paper.DimensionStage.factorial_power_dimension_bound
    (t := (distinctArities ks).card) (c := c) (U := rootStopBudget n)
    (hfac.trans hbudget)
  have hu := rootStopBudget_le_2004_n4 hn
  calc
    (distinctArities ks).card ^ (c * (distinctArities ks).card) ≤
        rootStopBudget n ^ (2 * c) := hdim
    _ ≤ (2004 * n ^ 4) ^ (2 * c) := (Nat.pow_le_pow_left hu) (2 * c)
    _ = 2004 ^ (2 * c) * n ^ (8 * c) := by ring

/-- The recursive invocation count inherits the same explicit numeric bound,
with the finite typed alphabet size left as an explicit factor. -/
theorem recursive_calls_le_numeric_candidate_bound {K n : Nat} (hn : 1 ≤ n) :
    recursiveCalls (decorationLabels K) labelQ
      (fun x => by have hk := x.arity.property; unfold labelQ; omega)
      (rootStopBudget n) ≤
      (decorationLabels K).length *
        (3 * 2004 ^ 10 * n ^ 40) + 3 * 2004 ^ 10 * n ^ 40 + 1 := by
  have hcall := recursiveCalls_le_enumeratedSize_bound
    (decorationLabels K) labelQ
    (fun x => by have hk := x.arity.property; unfold labelQ; omega)
    (rootStopBudget n)
  have hc := candidates_le_explicit_numeric_bound (K := K) (n := n) hn
  calc
    recursiveCalls (decorationLabels K) labelQ
        (fun x => by have hk := x.arity.property; unfold labelQ; omega)
        (rootStopBudget n) ≤
        ((decorationLabels K).length + 1) *
          (typedBudgetWords (decorationLabels K) labelQ
            (fun x => by have hk := x.arity.property; unfold labelQ; omega)
            (rootStopBudget n)).length + 1 := hcall
    _ ≤ (decorationLabels K).length * (3 * 2004 ^ 10 * n ^ 40) +
          3 * 2004 ^ 10 * n ^ 40 + 1 := by
      have hmul := Nat.mul_le_mul_left ((decorationLabels K).length + 1) hc
      calc
        _ ≤ ((decorationLabels K).length + 1) *
              (3 * 2004 ^ 10 * n ^ 40) + 1 := Nat.add_le_add_right hmul 1
        _ = _ := by ring

end Paper.CountStage.StopBudget
