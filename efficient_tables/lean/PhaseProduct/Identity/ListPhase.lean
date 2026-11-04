import PhaseProduct.Identity.PointNodes

/-!
# Phase identities from valid point lists

States the pair and triple phase identities for a valid point list at positive
arity `k`: `pair_phase_of_valid_list` and `triple_phase_of_valid_list`. The
helper `ofFn_cast_get` handles list-to-function casts.
-/

namespace Paper.ListPhase

open TableGeneration TableGeneration.Operations

theorem ofFn_cast_get {α : Type} (xs : List α) {n : Nat}
    (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs.get (i.cast h.symm)) = xs := by
  subst n
  exact List.ofFn_get xs

theorem pair_phase_of_valid_list (k : Nat) (hk : 0 < k)
    (ops : Prog k) (pts : List Point)
    (hvalid : ValidPointList .PhaseProduct k pts)
    (hinfty : Point.frac 0 ∈ pts)
    (hcontract : ProgConsumesPtsSafe hk
      State.start_state ops pts) (b : ℚ) :
    ∃ (w : Fin (2*(k-1)+1) → ℚ), ∀ (x z : ValueSemantics.Values k),
    ∃ (xs zs : List Int),
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z,zs) ∧
      xs.length = 2*k-1 ∧ zs.length = 2*k-1 ∧
      (∑ l, w l * (xs.getD l.val 0 : ℚ) * (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) *
        (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  have hsize : pts.length = 2*(k-1)+1 := by
    have h := hvalid.1
    simp only [ProductMode.pointCount] at h
    omega
  let indexed : Fin (2*(k-1)+1) → Point :=
    fun i => pts.get (i.cast hsize.symm)
  have hindexed : List.ofFn indexed = pts := by
    exact ofFn_cast_get pts hsize
  have hv : ValidPointList .PhaseProduct k (List.ofFn indexed) := by
    rw [hindexed]
    exact hvalid
  have hi : Point.frac 0 ∈ List.ofFn indexed := by
    rw [hindexed]
    exact hinfty
  obtain ⟨v, order, hvnode, hf, hinode⟩ :=
    PointNodes.exists_enumeration_of_validPointList .PhaseProduct k indexed hv hi
  have hc : ProgConsumesPtsSafe hk
      State.start_state ops (List.ofFn indexed) := by
    rw [hindexed]
    exact hcontract
  refine ⟨GeneralConstruction.phaseWeights k 2 indexed v b order, ?_⟩
  intro x z
  exact GeneralConstruction.source_pair_constructed_phase
    hk ops indexed v order hvnode hf hinode b hc x z

theorem triple_phase_of_valid_list (k : Nat) (hk : 0 < k)
    (ops : Prog k) (pts : List Point)
    (hvalid : ValidPointList .PhaseTripleProduct k pts)
    (hinfty : Point.frac 0 ∈ pts)
    (hcontract : ProgConsumesPtsSafe hk
      State.start_state ops pts) (b : ℚ) :
    ∃ (w : Fin (3*(k-1)+1) → ℚ), ∀ (x y z : ValueSemantics.Values k),
    ∃ (xs ys zs : List Int),
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) x = some (x,xs) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) y = some (y,ys) ∧
      ValueSemantics.valueTrace (SourceBridge.mapToFull ops) z = some (z,zs) ∧
      xs.length = 3*k-2 ∧ ys.length = 3*k-2 ∧ zs.length = 3*k-2 ∧
      (∑ l, w l * (xs.getD l.val 0 : ℚ) * (ys.getD l.val 0 : ℚ) *
        (zs.getD l.val 0 : ℚ)) =
        (∑ j : Fin k, b^j.val * (x j : ℚ)) *
        (∑ j : Fin k, b^j.val * (y j : ℚ)) *
        (∑ j : Fin k, b^j.val * (z j : ℚ)) := by
  have hsize : pts.length = 3*(k-1)+1 := by
    have h := hvalid.1
    simp only [ProductMode.pointCount] at h
    omega
  let indexed : Fin (3*(k-1)+1) → Point :=
    fun i => pts.get (i.cast hsize.symm)
  have hindexed : List.ofFn indexed = pts := by
    exact ofFn_cast_get pts hsize
  have hv : ValidPointList .PhaseTripleProduct k (List.ofFn indexed) := by
    rw [hindexed]
    exact hvalid
  have hi : Point.frac 0 ∈ List.ofFn indexed := by
    rw [hindexed]
    exact hinfty
  obtain ⟨v, order, hvnode, hf, hinode⟩ :=
    PointNodes.exists_enumeration_of_validPointList .PhaseTripleProduct k indexed hv hi
  have hc : ProgConsumesPtsSafe hk
      State.start_state ops (List.ofFn indexed) := by
    rw [hindexed]
    exact hcontract
  refine ⟨GeneralConstruction.phaseWeights k 3 indexed v b order, ?_⟩
  intro x y z
  exact GeneralConstruction.source_triple_constructed_phase
    hk ops indexed v order hvnode hf hinode b hc x y z

end Paper.ListPhase
