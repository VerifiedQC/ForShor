import PhaseProduct.Catalog.Count
import PhaseProduct.Catalog.RecursiveSemantics

/-!
# End-to-end optimum over a verified catalogue

The optimum over a supplied verified catalogue: `optimized_pp_end_to_end`
constructs a shared-table policy with exactly the coupled benchmark cost, and
the lower bound compares all contracting shared-table traces in this
catalogue. `optimized_pp_tauRS` specializes it to the Ross--Selinger price
(noncomputable selector, no runtime bound asserted) and `pp_through_arity_K`
gives a finite witness through arity `K`. This is a finite-catalogue
statement; optimality is relative to the certified entries.
-/

namespace Paper.PPEndToEnd

/-- The candidate interface is inhabited at every allowed arity, including
arities beyond the optimized 2--16 dispatch. The source generator then uses
its verified baseline fallback. Certificate selection is classical. -/
theorem verified_catalog_through_arity_exists (K : Nat) :
    ∃ entry : Fin (K - 1) → VerifiedPPCandidate K,
      (∀ i, (entry i).arity = i.val + 2) ∧
      (∀ k, 2 ≤ k → k ≤ K → ∃ i, (entry i).arity = k) := by
  classical
  have h : ∀ i : Fin (K - 1),
      ∃ t : VerifiedPPCandidate K, t.arity = i.val + 2 := by
    intro i
    exact bestKnown_verified_candidate_exists K (i.val + 2) (by omega) (by omega)
  choose entry he using h
  refine ⟨entry, he, ?_⟩
  intro k hk hK
  refine ⟨⟨k - 2, by omega⟩, ?_⟩
  rw [he]
  change k - 2 + 2 = k
  omega

/-- End-to-end optimum over the supplied verified catalog. The concrete
selected trace constructs a shared-table policy, executes the ideal PP phase
on every signed W-bit input, and has exactly the coupled benchmark cost.
The lower bound compares all contracting shared-table traces in this catalog. -/
theorem optimized_pp_end_to_end {K : Nat} {ι : Type} [DecidableEq ι]
    (price : Nat → Nat) (entry : ι → VerifiedPPCandidate K)
    (catalog : List ι) (W N : Nat) :
    let P := ppProblem price entry
    let arity := fun c => (entry c).arity
    let trace := Paper.PolicyOptimality.chosenTrace P catalog arity K W N
    ∃ policy : PPPolicy K W,
      policyFromTrace entry trace W = some policy ∧
      (∀ c ∈ trace, c ∈ catalog) ∧
      Coupled.Formal.ArityInj arity trace ∧
      (∀ c ∈ trace,
        Paper.PolicyOptimality.chosenAtArity P catalog arity K W N (arity c) = some c ∧
        (arity c, c) ∈ Paper.PolicyOptimality.chosenTable P catalog arity K W N) ∧
      policy.benchmarkCost price N =
        Paper.PolicyOptimality.chosenCost P catalog arity K W N ∧
      policy.benchmarkCost price N =
        4 * (policy.adderAnds N + policy.leafRotations N) +
          policy.leafRotations N * price (policy.leafRotations N) ∧
      (∀ (theta : ℝ) (a c : BitVec W),
        policy.eval schoolbookLeaf theta a.toInt c.toInt =
          some (Paper.ValuePhase.phaseCharacter theta
            ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
      (∀ (l : List ι) (other : PPPolicy K W),
        (∀ c ∈ l, c ∈ catalog) → Coupled.Formal.ArityInj arity l →
        policyFromTrace entry l W = some other →
        policy.benchmarkCost price N ≤ other.benchmarkCost price N) := by
  dsimp only
  let P := ppProblem price entry
  let arity := fun c => (entry c).arity
  obtain ⟨hlen, hmem, hshared, hcost⟩ :=
    Paper.PolicyOptimality.selected_valid P catalog arity K W N
  obtain ⟨policy, hp, hv⟩ := policyFromTrace_of_cost price entry hcost
  refine ⟨policy, hp, fun c hc => (hmem c hc).1, hshared, ?_, hv,
    benchmarkCost_eq_census price policy N, ?_, ?_⟩
  · intro c hc
    exact ⟨Paper.PolicyOptimality.chosenAtArity_hit P catalog arity K W N c hc,
      Paper.PolicyOptimality.chosenTable_contains P catalog arity K W N c hc⟩
  · intro theta a c
    exact PPPolicy.eval_correct schoolbookLeaf schoolbookLeaf_correct policy theta
      a.toInt c.toInt (by simp) (by simp)
  · intro l other hm hs ho
    rw [hv]
    apply Paper.PolicyOptimality.selected_le_all_shared P catalog arity K W N
      l (other.benchmarkCost price N)
    · intro c hc
      exact ⟨hm c hc, (entry c).source.hk, (entry c).cap⟩
    · exact hs
    · exact policyFromTrace_to_cost price entry l W N other ho

/-- The stipulated Ross--Selinger price specializes the exact finite-catalog
theorem. This price uses real logarithms and rounding, so this canonical
mathematical selector is noncomputable; no runtime bound is asserted here. -/
theorem optimized_pp_tauRS {K : Nat} {ι : Type} [DecidableEq ι]
    (entry : ι → VerifiedPPCandidate K) (catalog : List ι) (W : Nat) :
    let P := ppProblem tauRS entry
    let arity := fun c => (entry c).arity
    let trace := Paper.PolicyOptimality.chosenTrace P catalog arity K W 1
    ∃ policy : PPPolicy K W,
      policyFromTrace entry trace W = some policy ∧
      (∀ c ∈ trace, c ∈ catalog) ∧
      Coupled.Formal.ArityInj arity trace ∧
      (∀ c ∈ trace,
        Paper.PolicyOptimality.chosenAtArity P catalog arity K W 1 (arity c) = some c ∧
        (arity c, c) ∈ Paper.PolicyOptimality.chosenTable P catalog arity K W 1) ∧
      policy.benchmarkCost tauRS 1 =
        Paper.PolicyOptimality.chosenCost P catalog arity K W 1 ∧
      policy.benchmarkCost tauRS 1 =
        4 * (policy.adderAnds 1 + policy.leafRotations 1) +
          policy.leafRotations 1 * tauRS (policy.leafRotations 1) ∧
      (∀ (theta : ℝ) (a c : BitVec W),
        policy.eval schoolbookLeaf theta a.toInt c.toInt =
          some (Paper.ValuePhase.phaseCharacter theta
            ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
      (∀ (l : List ι) (other : PPPolicy K W),
        (∀ c ∈ l, c ∈ catalog) → Coupled.Formal.ArityInj arity l →
        policyFromTrace entry l W = some other →
        policy.benchmarkCost tauRS 1 ≤ other.benchmarkCost tauRS 1) :=
  optimized_pp_end_to_end tauRS entry catalog W 1

/-- A complete finite witness through arity K, with its actual selected
policy. Optimality is relative to these certified source entries. -/
theorem pp_through_arity_K (K W : Nat) :
    ∃ (entry : Fin (K - 1) → VerifiedPPCandidate K) (policy : PPPolicy K W),
      (∀ k, 2 ≤ k → k ≤ K → ∃ i, (entry i).arity = k) ∧
      let catalog := List.finRange (K - 1)
      let P := ppProblem tauRS entry
      let arity := fun c => (entry c).arity
      let trace := Paper.PolicyOptimality.chosenTrace P catalog arity K W 1
      policyFromTrace entry trace W = some policy ∧
      Coupled.Formal.ArityInj arity trace ∧
      policy.benchmarkCost tauRS 1 =
        Paper.PolicyOptimality.chosenCost P catalog arity K W 1 ∧
      policy.benchmarkCost tauRS 1 =
        4 * (policy.adderAnds 1 + policy.leafRotations 1) +
          policy.leafRotations 1 * tauRS (policy.leafRotations 1) ∧
      (∀ (theta : ℝ) (a c : BitVec W),
        policy.eval schoolbookLeaf theta a.toInt c.toInt =
          some (Paper.ValuePhase.phaseCharacter theta
            ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
      (∀ (l : List (Fin (K - 1))) (other : PPPolicy K W),
        Coupled.Formal.ArityInj arity l →
        policyFromTrace entry l W = some other →
        policy.benchmarkCost tauRS 1 ≤ other.benchmarkCost tauRS 1) := by
  obtain ⟨entry, hentry, hcover⟩ := verified_catalog_through_arity_exists K
  obtain ⟨policy, hp, hm, hs, ht, hv, hc, hsem, hopt⟩ :=
    optimized_pp_tauRS entry (List.finRange (K - 1)) W
  refine ⟨entry, policy, hcover, hp, hs, hv, hc, hsem, ?_⟩
  intro l other hshared ho
  exact hopt l other (fun c _ => by simp) hshared ho

end Paper.PPEndToEnd
