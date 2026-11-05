import Provider.Effective.ProfileProvider
import Planner.TauPrice

/-! # Exact Optimality of the Profile Provider
Proves `entry_weights` for the profile-provider entries and `optimal_raw_F2_exact`. The finite minimum-profile provider feeds the accepted shared-ladder selector at the exact integer Tau price; the provider performs an exhaustive XP minimum search per key and the selector remains exhaustive in root width.
-/

namespace Paper.ComputableProfileProvider

theorem entry_weights {K root : Nat} (hK : 2 ≤ K)
    (key : Index K root) (W : Nat) :
    (entry hK key).weights W =
      Paper.A4Exec.phaseWeightsExec (rawEntry hK key).source.k 2
        (rawEntry hK key).points
        (Paper.SignedLimbs.radix W (rawEntry hK key).source.k : ℚ) := by
  rfl

/-- The finite minimum-profile provider feeds the accepted shared-ladder
selector at the exact integer Tau price. The provider performs an exhaustive
XP minimum search per key; the selector remains exhaustive in root width. -/
theorem optimal_raw_F2_exact (K W N : Nat) (hK : 2 ≤ K) :
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
    Paper.F2CatalogTransfer.optimized_pp_all_F2_conditional
      Paper.PPEndToEnd.tauExact (entry hK) (catalog K W) W N (provider hK)
  refine ⟨policy, hp, hs, hl, hc, ?_, heval, ?_⟩
  · exact (Paper.PPEndToEnd.benchmarkCost_tauExact_eq_tauRS policy N).symm
  · intro l v hshared hcost
    rw [Paper.PPEndToEnd.tauRS_eq_tauExact_fun] at hcost
    rw [← Paper.PPEndToEnd.benchmarkCost_tauExact_eq_tauRS]
    exact hmin l v hshared hcost

end Paper.ComputableProfileProvider
