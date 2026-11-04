import Provider.Effective.ProfileExact

/-! # All-Arity-Cap Raw Optimum
Proves `no_raw_source` for caps `K < 2` and `optimal_raw_F2_allK`: all arity caps have an all-raw optimum. For `K` below two the raw source type is empty and the leaf is the only possible ladder; otherwise the computable minimum-profile catalog supplies the optimum.
-/

namespace Paper.ComputableProfileProvider

theorem no_raw_source {K : Nat} (hK : K < 2)
    (t : Paper.F2CatalogTransfer.F2Source K) : False := by
  have hk := t.source.hk
  have hc := t.cap
  omega

/-- All arity caps have an all-raw optimum. For K below two the raw source
type is empty and the leaf is the only possible ladder; otherwise the
computable minimum-profile catalog supplies the optimum. -/
theorem optimal_raw_F2_allK (K W N : Nat) :
    ∃ policy : Paper.PPEndToEnd.PPPolicy K W,
      policy.benchmarkCost Paper.PPEndToEnd.tauRS N =
        policy.benchmarkCost Paper.PPEndToEnd.tauExact N ∧
      (∀ (theta : ℝ) (a c : BitVec W),
        policy.eval Paper.PPEndToEnd.schoolbookLeaf theta a.toInt c.toInt =
          some (Paper.ValuePhase.phaseCharacter theta
            ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
      (∀ (l : List (Paper.F2CatalogTransfer.F2Source K)) (v : Nat),
        Coupled.Formal.ArityInj Paper.F2CatalogTransfer.F2Source.arity l →
        Coupled.Formal.CostL
          (Paper.F2CatalogTransfer.rawProblem Paper.PPEndToEnd.tauRS)
          l W N v →
        policy.benchmarkCost Paper.PPEndToEnd.tauRS N ≤ v) := by
  by_cases hK : 2 ≤ K
  · obtain ⟨policy, _, _, _, _, heq, hsem, hmin⟩ :=
      optimal_raw_F2_exact K W N hK
    exact ⟨policy, heq, hsem, hmin⟩
  · have hsmall : K < 2 := by omega
    refine ⟨.leaf W, ?_, ?_, ?_⟩
    · exact (Paper.PPEndToEnd.benchmarkCost_tauExact_eq_tauRS
        (Paper.PPEndToEnd.PPPolicy.leaf W : Paper.PPEndToEnd.PPPolicy K W) N).symm
    · intro theta a c
      exact Paper.PPEndToEnd.PPPolicy.eval_correct
        Paper.PPEndToEnd.schoolbookLeaf
        Paper.PPEndToEnd.schoolbookLeaf_correct
        (.leaf W) theta a.toInt c.toInt (by simp) (by simp)
    · intro l v _ hcost
      cases l with
      | nil =>
          cases hcost with
          | base => exact le_rfl
      | cons t rest => exact (no_raw_source hsmall t).elim

end Paper.ComputableProfileProvider
