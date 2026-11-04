import Provider.Effective.FiniteProvider

/-! # Classical Existence of the Optimum
Proves `completeProvider_exists`, classical finite existence of a complete provider at one root, which does not compute the entries. Derives `optimal_raw_F2_policy_exists`, an attained optimum among every contracting shared raw literal-F2 ladder. The catalog and selector are chosen classically; no effective construction or complexity bound is asserted.
-/

namespace Paper.F2CatalogTransfer

open Paper.PPEndToEnd Coupled.Formal

/-- Classical finite existence at one root. This does not compute the entries. -/
theorem completeProvider_exists (K root : Nat) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (entry : ι → VerifiedPPCandidate K) (catalog : List ι),
      Nonempty (CompleteProvider root entry catalog) := by
  classical
  by_cases h : Nonempty (F2Source K)
  . obtain ⟨fallback⟩ := h
    exact ⟨Option (ProfileKey K root), inferInstance, inferInstance,
      providerEntry fallback, providerCatalog K root,
      ⟨finiteCompleteProvider fallback⟩⟩
  . let entry : Empty → VerifiedPPCandidate K := Empty.elim
    let pick : F2Source K → Empty := fun t => False.elim (h ⟨t⟩)
    let provider : CompleteProvider root entry ([] : List Empty) := {
      pick := pick
      catalog_literal := by intro c hc; exact c.elim
      member := by intro t ht; exact (h ⟨t⟩).elim
      arity := by intro t ht; exact (h ⟨t⟩).elim
      width := by intro t ht w; exact (h ⟨t⟩).elim
      charge := by intro t ht; exact (h ⟨t⟩).elim
    }
    exact ⟨Empty, inferInstance, inferInstance, entry, [], ⟨provider⟩⟩

/-- An attained optimum among every contracting shared raw literal-F2 ladder.
The catalog and selector here are chosen classically; no effective construction
or complexity bound is asserted. -/
theorem optimal_raw_F2_policy_exists (K W N : Nat) (price : Nat → Nat) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (entry : ι → VerifiedPPCandidate K) (catalog : List ι)
      (policy : PPPolicy K W),
      (let trace := Paper.PolicyOptimality.chosenTrace
          (ppProblem price entry) catalog (fun c => (entry c).arity) K W N
       policyFromTrace entry trace W = some policy ∧
       ArityInj (fun c => (entry c).arity) trace ∧
       (∀ c ∈ trace, VerifiedLiteralF2 (entry c))) ∧
      policy.benchmarkCost price N =
        4 * (policy.adderAnds N + policy.leafRotations N) +
          policy.leafRotations N * price (policy.leafRotations N) ∧
      (∀ (theta : ℝ) (a c : BitVec W),
        policy.eval schoolbookLeaf theta a.toInt c.toInt =
          some (Paper.ValuePhase.phaseCharacter theta
            ((a.toInt : ℚ) * (c.toInt : ℚ)))) ∧
      (∀ (l : List (F2Source K)) (v : Nat),
        ArityInj F2Source.arity l →
        CostL (rawProblem price) l W N v →
        policy.benchmarkCost price N ≤ v) := by
  obtain ⟨ι, instFin, instDec, entry, catalog, ⟨provider⟩⟩ :=
    completeProvider_exists K W
  letI : Fintype ι := instFin
  letI : DecidableEq ι := instDec
  obtain ⟨policy, htrace, hshared, hliteral, _hchosen, hcensus, hphase, hmin⟩ :=
    optimized_pp_all_F2_conditional price entry catalog W N provider
  exact ⟨ι, instFin, instDec, entry, catalog, policy,
    ⟨htrace, hshared, hliteral⟩, hcensus, hphase, hmin⟩

end Paper.F2CatalogTransfer
