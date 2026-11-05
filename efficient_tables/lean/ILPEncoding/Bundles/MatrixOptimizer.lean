import ILPEncoding.Bounds.CanonicalMatrix
import ILPEncoding.Bounds.SemanticRows
import ILPEncoding.Bundles.Profile

/-! # Optimizer Canonical Matrix
Proves `optimizer_canonical_matrix_bits`: the exact finite raw optimizer yields a feasible canonical-price ILP encoding at its own optimum threshold, with an explicit numeric bit bound. This theorem concerns the finite encoding and does not assert an ILP solver or uniform polynomial synthesis of the minimum-charge profiles.
-/

set_option autoImplicit false

namespace Paper.F7MatrixFinal

open Coupled.Formal Paper.F2CatalogTransfer Paper.PPEndToEnd
open Paper.A2Feasible Paper.A2ActualForward Paper.ComputableProfileProvider
open Paper.AffineNat Paper.F6ILP Paper.F6ILPSystem Paper.F6ILPFeasible
open Paper.F6TypedBridge Paper.F7System
open Paper.F7QControl Paper.F7WordSize Paper.F7Computable Paper.F7Encoding
open Paper.F7Semantics Paper.CountStage.TypedDecorationWords
open Paper.CountStage.StopBudget

/-- The exact finite raw optimizer yields a feasible canonical-price ILP
encoding at its own optimum threshold, with an explicit numeric bit bound.
This theorem concerns the finite encoding and does not assert an ILP solver
or uniform polynomial synthesis of the minimum-charge profiles. -/
theorem optimizer_canonical_matrix_bits {K W : Nat}
    (hK : 2 ≤ K) (hW : 1 ≤ W) :
    ∃ (reps : List (F2Source K)) (v' : Nat)
      (labels : List Label) (z : ℤ),
      v' = (optimize K W 1).benchmarkCost tauRS 1 ∧
      v' ≤ rootStopBudget W ∧
      ArityInj F2Source.arity reps ∧
      CostL (rawProblem tauRS) reps W 1 v' ∧
      qProduct labelQ (labels.map toTyped) ≤ rootStopBudget W ∧
      labels.map toTyped ∈ consistentBudgetWordsFixed K (rootStopBudget W) ∧
      1 ≤ z ∧ z ≤ v' ∧
      Feasible labels (1 * W) z (profileC reps)
        (fun k => levelLo K W k (profileD reps k) (profileC reps k))
        (fun k => levelHi K W k (profileD reps k) (profileC reps k))
        tauRS 1 v' (fun key => (profileA reps key.val : ℤ)) ∧
      (systemRowsC labels (W : ℤ) z (profileC reps)
        (fun k => levelLo K W k (profileD reps k) (profileC reps k))
        (fun k => levelHi K W k (profileD reps k) (profileC reps k))
        tauRS 1 v').Forall
          (fun row => 0 ≤ evalInt row
            (fun key => (profileA reps key.val : ℤ))) ∧
      matrixBits (systemRowsC labels (W : ℤ) z (profileC reps)
        (fun k => levelLo K W k (profileD reps k) (profileC reps k))
        (fun k => levelHi K W k (profileD reps k) (profileC reps k))
        tauRS 1 v') ≤
        (3 * rootStopBudget W + 3) * (rootStopBudget W + 1) *
          (numericMagnitudeUniform (rootStopBudget W) K W + 2) := by
  obtain ⟨reps,v',labels,z,hopt,hvroot,hinj,hcost,hlabel,hq,hfixed,
      _hcandidate,_hactual,_hcostEq,hz1,hzv,hfeas⟩ :=
    optimizer_candidate_feasible_root hK hW
  have hbudget : qWord labels ≤ rootStopBudget W := by
    rw [qWord_eq_typedProduct]
    exact hq
  have hKlabels : ∀ label ∈ labels, label.k ≤ K := by
    intro label hmem
    obtain ⟨_,_,_,hk,_⟩ := hlabel label hmem
    exact hk
  have hcap : ∀ label ∈ labels,
      label.c ≤ 27 * label.k ^ 3 := by
    intro label hmem
    obtain ⟨_,_,_,_,hcap⟩ := hlabel label hmem
    exact hcap
  have hshared : ∀ label ∈ labels,
      label.c = profileC reps label.k := by
    intro label hmem
    exact (hlabel label hmem).2.1
  have hx : -((W : Nat) : ℤ) ≤ (W : ℤ) ∧ (W : ℤ) ≤ W := by
    omega
  have hvrootZ : (v' : ℤ) ≤ rootStopBudget W := by
    exact_mod_cast hvroot
  have hzroot : 0 ≤ z ∧ z ≤ rootStopBudget W := by
    omega
  have hlohi : ∀ key ∈ usedKeys labels,
      levelLo K W key.val (profileD reps key.val)
          (profileC reps key.val) ≤ W ∧
      levelHi K W key.val (profileD reps key.val)
          (profileC reps key.val) ≤ W := by
    intro key _
    exact level_endpoints_le_root hW
  have hbitsExact := canonical_matrix_bits_uniform labels (W : ℤ) z
    (profileC reps)
    (fun k => levelLo K W k (profileD reps k) (profileC reps k))
    (fun k => levelHi K W k (profileD reps k) (profileC reps k))
    v' (rootStopBudget W) K W hbudget hKlabels hcap hshared
    hx hzroot hvroot hlohi
  have hbits : matrixBits (systemRowsC labels (W : ℤ) z (profileC reps)
      (fun k => levelLo K W k (profileD reps k) (profileC reps k))
      (fun k => levelHi K W k (profileD reps k) (profileC reps k))
      tauRS 1 v') ≤
      (3 * rootStopBudget W + 3) * (rootStopBudget W + 1) *
        (numericMagnitudeUniform (rootStopBudget W) K W + 2) := by
    simpa only [tauRS_eq_tauExact_fun] using hbitsExact
  have hrows := (systemRowsC_iff_feasible labels (W : ℤ) z
    (profileC reps)
    (fun k => levelLo K W k (profileD reps k) (profileC reps k))
    (fun k => levelHi K W k (profileD reps k) (profileC reps k))
    tauRS 1 v' (fun key => (profileA reps key.val : ℤ))).2
    (by simpa only [one_mul] using hfeas)
  exact ⟨reps,v',labels,z,hopt,hvroot,hinj,hcost,hq,hfixed,
    hz1,hzv,hfeas,hrows,hbits⟩

end Paper.F7MatrixFinal
