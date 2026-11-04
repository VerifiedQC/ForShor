import Model.Interpreter.ValueTrace
import PhaseProduct.Identity.PhaseIdentity
import Mathlib.Data.List.GetD

/-!
# Phase-product identity for source programs

Turns an accepted positive-arity source program with a supplied certificate
into the phase-product identity over its recorded observations:
`source_pair_trace_phase_product` for the pair case and
`source_triple_trace_phase_product` for the triple case, with
`indexed_observation_eq` as the indexing lemma.
-/

namespace Paper.GenericPhase

theorem evalRow_cast {k : Nat} (row : Fin k → Int)
    (x : ValueSemantics.Values k) :
    ((ValueSemantics.evalRow row x : Int) : ℚ) =
      PhaseIdentity.linearForm (fun j => (row j : ℚ)) (fun j => (x j : ℚ)) := by
  simp [ValueSemantics.evalRow, PhaseIdentity.linearForm]

theorem indexed_observations_length {k q : Nat}
    (pts : Fin q → TableGeneration.Operations.Point)
    (x : ValueSemantics.Values k) :
    (PhaseIdentity.observations (List.ofFn pts) x).length = q := by
  simp [PhaseIdentity.observations]

theorem indexed_observation_eq {k q : Nat}
    (pts : Fin q → TableGeneration.Operations.Point)
    (x : ValueSemantics.Values k) (l : Fin q) :
    ((PhaseIdentity.observations (List.ofFn pts) x).getD l.val 0 : ℚ) =
      PhaseIdentity.linearForm (indexedSourceRows pts l)
        (fun j => (x j : ℚ)) := by
  have hlt : l.val < (PhaseIdentity.observations (List.ofFn pts) x).length := by
    simp [indexed_observations_length]
  rw [List.getD_eq_getElem _ _ hlt]
  simpa [PhaseIdentity.observations, indexedSourceRows] using
    evalRow_cast (TableGeneration.expectedRow (k := k) (pts l)) x

/-- Any accepted positive-arity source program with a supplied pair
coefficient certificate yields the corresponding product identity on its
actual integer traces, for every pair of integer input vectors. -/
theorem source_pair_trace_phase_product {k q : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point)
    (weight : Fin q → ℚ) (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hcert : PhaseIdentity.PairCertificate weight (indexedSourceRows pts) base)
    (x z : ValueSemantics.Values k) :
    ∃ xs zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x, xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z, zs) ∧
      xs.length = q ∧ zs.length = q ∧
      (∑ l : Fin q, weight l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
        PhaseIdentity.linearForm base (fun j => (z j : ℚ)) := by
  refine ⟨PhaseIdentity.observations (List.ofFn pts) x,
    PhaseIdentity.observations (List.ofFn pts) z, ?_, ?_,
    indexed_observations_length pts x, indexed_observations_length pts z, ?_⟩
  · simpa [PhaseIdentity.observations] using
      ValueSemantics.source_contract_valueTrace hk ops (List.ofFn pts) x hcontract
  · simpa [PhaseIdentity.observations] using
      ValueSemantics.source_contract_valueTrace hk ops (List.ofFn pts) z hcontract
  · simp_rw [indexed_observation_eq]
    exact PhaseIdentity.pair_identity_of_certificate weight
      (indexedSourceRows pts) base hcert (fun j => (x j : ℚ))
      (fun j => (z j : ℚ))

/-- The corresponding three-input identity uses exactly the same ordered
source trace and a supplied triple coefficient certificate. -/
theorem source_triple_trace_phase_product {k q : Nat} (hk : k > 0)
    (ops : TableGeneration.Prog k)
    (pts : Fin q → TableGeneration.Operations.Point)
    (weight : Fin q → ℚ) (base : Fin k → ℚ)
    (hcontract : TableGeneration.ProgConsumesPtsSafe hk
      TableGeneration.State.start_state ops (List.ofFn pts))
    (hcert : PhaseIdentity.TripleCertificate weight (indexedSourceRows pts) base)
    (x y z : ValueSemantics.Values k) :
    ∃ xs ys zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x, xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) y = some (y, ys) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z, zs) ∧
      xs.length = q ∧ ys.length = q ∧ zs.length = q ∧
      (∑ l : Fin q, weight l * (xs.getD l.val 0 : ℚ) *
        (ys.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        PhaseIdentity.linearForm base (fun j => (x j : ℚ)) *
        PhaseIdentity.linearForm base (fun j => (y j : ℚ)) *
        PhaseIdentity.linearForm base (fun j => (z j : ℚ)) := by
  refine ⟨PhaseIdentity.observations (List.ofFn pts) x,
    PhaseIdentity.observations (List.ofFn pts) y,
    PhaseIdentity.observations (List.ofFn pts) z, ?_, ?_, ?_,
    indexed_observations_length pts x,
    indexed_observations_length pts y,
    indexed_observations_length pts z, ?_⟩
  · simpa [PhaseIdentity.observations] using
      ValueSemantics.source_contract_valueTrace hk ops (List.ofFn pts) x hcontract
  · simpa [PhaseIdentity.observations] using
      ValueSemantics.source_contract_valueTrace hk ops (List.ofFn pts) y hcontract
  · simpa [PhaseIdentity.observations] using
      ValueSemantics.source_contract_valueTrace hk ops (List.ofFn pts) z hcontract
  · simp_rw [indexed_observation_eq]
    exact PhaseIdentity.triple_identity_of_certificate weight
      (indexedSourceRows pts) base hcert (fun j => (x j : ℚ))
      (fun j => (y j : ℚ)) (fun j => (z j : ℚ))

end Paper.GenericPhase
