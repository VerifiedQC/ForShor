import Provider.Effective.ProfileAllK

/-! # The Finite Optimizer
Defines `optimize K W N`, a finite executable optimizer whose profile lookup and outer selector are exhaustive; the definition carries no polynomial runtime claim. Proves `optimize_chosen_cost` and `optimize_all_raw`: the returned policy is optimal against every admissible shared raw literal-F2 ladder for every arity cap, including the leaf-only caps.
-/

namespace Paper.ComputableProfileProvider

/-- A finite, executable optimizer. Its profile lookup and outer selector
are exhaustive; this definition carries no polynomial runtime claim. -/
def optimize (K W N : Nat) : Paper.PPEndToEnd.PPPolicy K W :=
  if hK : 2 ≤ K then
    let e := entry (root := W) hK
    let c := catalog K W
    let P := Paper.PPEndToEnd.ppProblem Paper.PPEndToEnd.tauExact e
    let arity := fun i => (e i).arity
    let trace := Paper.PolicyOptimality.chosenTrace P c arity K W N
    (Paper.PPEndToEnd.policyFromTrace e trace W).getD (.leaf W)
  else .leaf W

theorem optimize_eq_selected {K W N : Nat} (hK : 2 ≤ K)
    (policy : Paper.PPEndToEnd.PPPolicy K W)
    (hp : Paper.PPEndToEnd.policyFromTrace (entry (root := W) hK)
      (Paper.PolicyOptimality.chosenTrace
        (Paper.PPEndToEnd.ppProblem Paper.PPEndToEnd.tauExact (entry hK))
        (catalog K W) (fun i => (entry hK i).arity) K W N) W = some policy) :
    optimize K W N = policy := by
  simp [optimize, dif_pos hK, hp]

theorem optimize_chosen_cost {K W N : Nat} (hK : 2 ≤ K) :
    (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauExact N =
      Paper.PolicyOptimality.chosenCost
        (Paper.PPEndToEnd.ppProblem Paper.PPEndToEnd.tauExact (entry hK))
        (catalog K W) (fun i => (entry hK i).arity) K W N := by
  obtain ⟨policy,hp,_,_,hc,_,_,_⟩ := optimal_raw_F2_exact K W N hK
  rw [optimize_eq_selected hK policy hp]
  exact hc

/-- The actual returned policy is optimal against every admissible shared
raw literal-F2 ladder for every arity cap, including the leaf-only caps. -/
theorem optimize_all_raw (K W N : Nat) :
    (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N =
      (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauExact N ∧
    (∀ (theta : ℝ) (a c : BitVec W),
      (optimize K W N).eval Paper.PPEndToEnd.schoolbookLeaf theta a.toInt c.toInt =
        some (Paper.ValuePhase.phaseCharacter theta
          ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
    (∀ (l : List (Paper.F2CatalogTransfer.F2Source K)) (v : Nat),
      Coupled.Formal.ArityInj Paper.F2CatalogTransfer.F2Source.arity l →
      Coupled.Formal.CostL
        (Paper.F2CatalogTransfer.rawProblem Paper.PPEndToEnd.tauRS)
        l W N v →
      (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N ≤ v) := by
  by_cases hK : 2 ≤ K
  · obtain ⟨policy,hp,_,_,_,heq,hsem,hmin⟩ :=
      optimal_raw_F2_exact K W N hK
    rw [optimize_eq_selected hK policy hp]
    exact ⟨heq,hsem,hmin⟩
  · have hsmall : K < 2 := by omega
    have hopt : optimize K W N = .leaf W := by simp [optimize, hK]
    rw [hopt]
    refine ⟨?_, ?_, ?_⟩
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
