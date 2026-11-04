import Provider.Effective.Complete
import Planner.TauPrice

/-! # Exact PP Optimality of the Effective Provider
Proves `entry_weights`: every enumerated candidate carries the executable projective interpolation weights at every input width. Combines the finite effective provider with the exact integer price to prove `effective_optimal_raw_F2_exact`, an attained optimum against every raw literal-F2 shared ladder. This is an exhaustive finite construction with no uniform polynomial runtime claim.
-/

namespace Paper.EffectiveProvider

/-- Every enumerated candidate carries the executable projective interpolation
weights supplied by A4, at every input width. -/
theorem entry_weights {K root : Nat} (hK : 2 ≤ K)
    (i : Index K root) (W : Nat) :
    (entry hK i).weights W =
      Paper.A4Exec.phaseWeightsExec (rawEntry hK i).source.k 2
        (rawEntry hK i).points
        (Paper.SignedLimbs.radix W (rawEntry hK i).source.k : ℚ) := by
  rfl

/-- The finite effective provider and the exact integer price together give
an attained optimum against every raw literal-F2 shared ladder. This remains
an exhaustive finite construction, with no uniform polynomial runtime claim. -/
theorem effective_optimal_raw_F2_exact (K W N : Nat) (hK : 2 ≤ K) :
    let e := entry (root := W) hK
    let c := catalog K W
    let P := Paper.PPEndToEnd.ppProblem Paper.PPEndToEnd.tauExact e
    let arity := fun i => (e i).arity
    let trace := Paper.PolicyOptimality.chosenTrace P c arity K W N
    ∃ policy : Paper.PPEndToEnd.PPPolicy K W,
      Paper.PPEndToEnd.policyFromTrace e trace W = some policy ∧
      Coupled.Formal.ArityInj arity trace ∧
      (∀ i ∈ trace, Paper.F2CatalogTransfer.VerifiedLiteralF2 (e i)) ∧
      policy.benchmarkCost Paper.PPEndToEnd.tauExact N =
        Paper.PolicyOptimality.chosenCost P c arity K W N ∧
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
  dsimp only
  obtain ⟨policy, hp, hs, hl, hc, _, heval, hmin⟩ :=
    effective_optimal_raw_F2_policy K W N hK Paper.PPEndToEnd.tauExact
  refine ⟨policy, hp, hs, hl, hc, ?_, heval, ?_⟩
  · exact (Paper.PPEndToEnd.benchmarkCost_tauExact_eq_tauRS policy N).symm
  · intro l v hshared hcost
    rw [Paper.PPEndToEnd.tauRS_eq_tauExact_fun] at hcost
    rw [← Paper.PPEndToEnd.benchmarkCost_tauExact_eq_tauRS]
    exact hmin l v hshared hcost

end Paper.EffectiveProvider
