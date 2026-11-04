import ILPEncoding.Labels.Final

/-! # Positive Widths for Actual Words
Proves `actual_positiveWidths`, that an `ActualWord` has positive widths, and `actual_cost_exact_noHyp`, which gives the exact cost statement for an actual word without the positive-width hypothesis.
-/

namespace Paper.F6Positive

open Paper.AffineActual Paper.AffineConverse Paper.AffineNat
open Paper.AffineILP Paper.AffineChain Paper.F6Objective
open Paper.F2CatalogTransfer Paper.F6CostBridge
open Paper.PPEndToEnd Coupled.Formal

theorem actual_positiveWidths {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels) :
    PositiveWidths P x (labels.map (Paper.AffineNat.instantiate a)) := by
  obtain ⟨z, hz, hterminal, hcleared⟩ :=
    actual_to_constraints a d c labels P x hP hactual
  have hz' : (1 : ℤ) ≤ z := by exact_mod_cast hz
  exact (terminal_cleared_positive P x
    (labels.map (Paper.AffineNat.instantiate a)) z hP hz'
    hterminal hcleared).2

theorem actual_cost_exact_noHyp {K : Nat} (a d c : Nat → Nat)
    (labels : List Paper.AffineNat.Label) (P x : ℤ) (hP : 0 < P)
    (hactual : ActualWord (K := K) a d c P x labels)
    (price : Nat → Nat) (N : Nat) :
    ∃ (w : Nat) (ts : List (F2Source K)) (v : Nat),
      x = P * w ∧ ts.length = labels.length ∧
      CostL (F6CostBridge.rawProblem price) ts w N v ∧
      (v : ℤ) = affineSum a c N P x labels +
        (leafPP price (finalN N labels) (terminalNat P x a labels) : ℤ) := by
  exact actual_cost_exact a d c labels P x hP hactual
    (actual_positiveWidths a d c labels P x hP hactual) price N

end Paper.F6Positive
