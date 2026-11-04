import Provider.Effective.Optimize

/-! # Optimizer Attainment
Proves `optimize_raw_attained`: the named optimizer `optimize` is attained by a legal shared raw F2 ladder at its exact stipulated benchmark cost, including the leaf-only small-arity case. The supporting lemmas `mapped_trace_shared` and `mapped_trace_cost` handle the shared-ladder and cost statements for a mapped trace.
-/

namespace Paper.ComputableProfileProvider

open Coupled.Formal Paper.F2CatalogTransfer

theorem mapped_trace_shared {K root : Nat} (hK : 2 ≤ K)
    (trace : List (Index K root))
    (hshared : ArityInj (fun i => (entry hK i).arity) trace) :
    ArityInj F2Source.arity (trace.map (rawEntry hK)) := by
  intro t ht u hu heq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hu
  have hij : i = j := hshared i hi j hj (by simpa [entry] using heq)
  simp [hij]

theorem mapped_trace_cost {K root : Nat} (hK : 2 ≤ K)
    (price : Nat → Nat) (trace : List (Index K root))
    (w N v : Nat)
    (hcost : CostL (Paper.PPEndToEnd.ppProblem price (entry hK))
      trace w N v) :
    CostL (rawProblem price) (trace.map (rawEntry hK)) w N v := by
  induction hcost with
  | base w N =>
      exact CostL.base w N
  | step i rest w N v hcontract htail ih =>
      apply CostL.step (rawEntry hK i) (rest.map (rawEntry hK)) w N v
      · simpa [Paper.PPEndToEnd.ppProblem, entry, rawProblem]
          using hcontract
      · simpa [Paper.PPEndToEnd.ppProblem, entry, rawProblem]
          using ih

/-- The named optimizer is attained by a legal shared raw F2 ladder at its
exact stipulated benchmark cost, including the leaf-only small-arity case. -/
theorem optimize_raw_attained (K W N : Nat) :
    ∃ l : List (F2Source K),
      ArityInj F2Source.arity l ∧
      CostL (rawProblem Paper.PPEndToEnd.tauRS) l W N
        ((optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N) := by
  by_cases hK : 2 ≤ K
  · let e := entry (root := W) hK
    let c := catalog K W
    let P := Paper.PPEndToEnd.ppProblem Paper.PPEndToEnd.tauExact e
    let arity := fun i => (e i).arity
    let trace := Paper.PolicyOptimality.chosenTrace P c arity K W N
    obtain ⟨_, _, hshared, hcost⟩ :=
      Paper.PolicyOptimality.selected_valid P c arity K W N
    refine ⟨trace.map (rawEntry hK), mapped_trace_shared hK trace hshared, ?_⟩
    have hraw := mapped_trace_cost hK Paper.PPEndToEnd.tauExact
      trace W N (Paper.PolicyOptimality.chosenCost P c arity K W N) hcost
    rw [Paper.PPEndToEnd.tauExact_eq_tauRS_fun] at hraw
    have hv : Paper.PolicyOptimality.chosenCost P c arity K W N =
        (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N := by
      calc
        _ = (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauExact N := by
          exact (optimize_chosen_cost hK).symm
        _ = (optimize K W N).benchmarkCost Paper.PPEndToEnd.tauRS N :=
          Paper.PPEndToEnd.benchmarkCost_tauExact_eq_tauRS _ _
    simpa [hv] using hraw
  · have hleaf : optimize K W N = .leaf W := by simp [optimize, hK]
    refine ⟨[], by simp [ArityInj], ?_⟩
    simpa [hleaf, rawProblem, Paper.PPEndToEnd.PPPolicy.benchmarkCost]
      using (CostL.base W N : CostL (rawProblem Paper.PPEndToEnd.tauRS)
        ([] : List (F2Source K)) W N
        ((rawProblem Paper.PPEndToEnd.tauRS).leaf N W))

end Paper.ComputableProfileProvider
