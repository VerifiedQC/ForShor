import PhaseProduct.Identity.GenericPhase
import PhaseProduct.Identity.Interpolation
import PhaseProduct.Identity.Normalization

/-!
# General construction of interpolation weights

Shows that interpolation weights built from projective nodes meet the moment
conditions (`projective_moments`, `ordered_projective_moments`) and so give
normalized pair and triple certificates (`pair_normalized_certificate`,
`triple_normalized_certificate`). Consequently constructed weights give the
phase identity for a source program (`source_pair_constructed_phase`,
`source_triple_constructed_phase`).
-/

namespace Paper.GeneralConstruction
open Normalization

theorem moment_reindex {q degree : Nat} (pt : Fin q → Option ℚ)
    (weight : Fin q → ℚ) (b : ℚ) (e : Fin q ≃ Fin q)
    (hm : MomentCertificate degree pt weight b) :
    MomentCertificate degree (fun l => pt (e l)) (fun l => weight (e l)) b := by
  intro m hmd
  rw [Equiv.sum_comp e (fun l => weight l * projectiveMonomial degree (pt l) m)]
  exact hm m hmd

theorem projective_moments {d : Nat}
    (pts : Fin (d+1) → TableGeneration.Operations.Point) (v : Fin d → ℚ)
    (hv : Function.Injective v)
    (hf : ∀ i, sourcePoint (pts i.castSucc) = some (v i))
    (hi : sourcePoint (pts (Fin.last d)) = none) (b : ℚ) :
    MomentCertificate d (fun l => sourcePoint (pts l)) (projectiveWeights v b) b := by
  intro m hm
  rw [Fin.sum_univ_castSucc]
  simpa [projectiveWeights, hf, hi, projectiveMonomial] using
    Interpolation.moment v hv b m hm

theorem ordered_projective_moments {d : Nat}
    (pts : Fin (d+1) → TableGeneration.Operations.Point) (v : Fin d → ℚ)
    (order : Fin (d+1) ≃ Fin (d+1)) (hv : Function.Injective v)
    (hf : ∀ i, sourcePoint (pts (order i.castSucc)) = some (v i))
    (hi : sourcePoint (pts (order (Fin.last d))) = none) (b : ℚ) :
    MomentCertificate d (fun l => sourcePoint (pts l))
      (fun l => projectiveWeights v b (order.symm l)) b := by
  have hm := projective_moments (fun l => pts (order l)) v hv hf hi b
  have hr := moment_reindex (fun l => sourcePoint (pts (order l)))
    (projectiveWeights v b) b order.symm hm
  simpa using hr

theorem pair_normalized_certificate {k : Nat} (hk : 0 < k)
    (pts : Fin (2*(k-1)+1) → TableGeneration.Operations.Point)
    (v : Fin (2*(k-1)) → ℚ) (order : Fin (2*(k-1)+1) ≃ Fin (2*(k-1)+1))
    (hv : Function.Injective v)
    (hf : ∀ i, sourcePoint (pts (order i.castSucc)) = some (v i))
    (hi : sourcePoint (pts (order (Fin.last (2*(k-1))))) = none) (b : ℚ) :
    PhaseIdentity.PairCertificate (phaseWeights k 2 pts v b order)
      (GenericPhase.indexedSourceRows (k := k) pts) (fun j => b^j.val) := by
  exact pair_certificate_of_moments hk pts _ b
    (ordered_projective_moments pts v order hv hf hi b)

theorem triple_normalized_certificate {k : Nat} (hk : 0 < k)
    (pts : Fin (3*(k-1)+1) → TableGeneration.Operations.Point)
    (v : Fin (3*(k-1)) → ℚ) (order : Fin (3*(k-1)+1) ≃ Fin (3*(k-1)+1))
    (hv : Function.Injective v)
    (hf : ∀ i, sourcePoint (pts (order i.castSucc)) = some (v i))
    (hi : sourcePoint (pts (order (Fin.last (3*(k-1))))) = none) (b : ℚ) :
    PhaseIdentity.TripleCertificate (phaseWeights k 3 pts v b order)
      (GenericPhase.indexedSourceRows (k := k) pts) (fun j => b^j.val) := by
  exact triple_certificate_of_moments hk pts _ b
    (ordered_projective_moments pts v order hv hf hi b)

/-- Constructed interpolation weights give the desired PP identity on the
actual ordered integer traces of any accepted source contract. -/
theorem source_pair_constructed_phase {k : Nat} (hk : 0 < k)
    (ops : TableGeneration.Prog k)
    (pts : Fin (2*(k-1)+1) → TableGeneration.Operations.Point)
    (v : Fin (2*(k-1)) → ℚ) (order : Fin (2*(k-1)+1) ≃ Fin (2*(k-1)+1))
    (hv : Function.Injective v)
    (hf : ∀ i, sourcePoint (pts (order i.castSucc)) = some (v i))
    (hi : sourcePoint (pts (order (Fin.last (2*(k-1))))) = none) (b : ℚ)
    (hc : TableGeneration.ProgConsumesPtsSafe hk TableGeneration.State.start_state ops (List.ofFn pts))
    (x z : ValueSemantics.Values k) :
    ∃ xs zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z,zs) ∧
      xs.length = 2*k-1 ∧ zs.length = 2*k-1 ∧
      (∑ l, phaseWeights k 2 pts v b order l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) * (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  have h := GenericPhase.source_pair_trace_phase_product hk ops pts
    (phaseWeights k 2 pts v b order) (fun j => b^j.val) hc
    (pair_normalized_certificate hk pts v order hv hf hi b) x z
  have hcount : 2*(k-1)+1 = 2*k-1 := by omega
  simpa only [hcount, PhaseIdentity.linearForm] using h

/-- The same construction supplies PTP weights with cubic row normalization. -/
theorem source_triple_constructed_phase {k : Nat} (hk : 0 < k)
    (ops : TableGeneration.Prog k)
    (pts : Fin (3*(k-1)+1) → TableGeneration.Operations.Point)
    (v : Fin (3*(k-1)) → ℚ) (order : Fin (3*(k-1)+1) ≃ Fin (3*(k-1)+1))
    (hv : Function.Injective v)
    (hf : ∀ i, sourcePoint (pts (order i.castSucc)) = some (v i))
    (hi : sourcePoint (pts (order (Fin.last (3*(k-1))))) = none) (b : ℚ)
    (hc : TableGeneration.ProgConsumesPtsSafe hk TableGeneration.State.start_state ops (List.ofFn pts))
    (x y z : ValueSemantics.Values k) :
    ∃ xs ys zs : List Int,
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) y = some (y,ys) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z,zs) ∧
      xs.length = 3*k-2 ∧ ys.length = 3*k-2 ∧ zs.length = 3*k-2 ∧
      (∑ l, phaseWeights k 3 pts v b order l * (xs.getD l.val 0 : ℚ) *
        (ys.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) * (∑ j : Fin k, b^j.val * (y j : ℚ)) *
        (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  have h := GenericPhase.source_triple_trace_phase_product hk ops pts
    (phaseWeights k 3 pts v b order) (fun j => b^j.val) hc
    (triple_normalized_certificate hk pts v order hv hf hi b) x y z
  have hcount : 3*(k-1)+1 = 3*k-2 := by omega
  simpa only [hcount, PhaseIdentity.linearForm] using h

end Paper.GeneralConstruction
