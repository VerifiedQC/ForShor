import Provider.Ladders.Certificate

/-!
# Certificate existence for raw F2 sources

Shows that every raw F2 source table `t` admits the additional algebraic
evidence needed to run it as a verified candidate. The statements are
`f2Source_certificate_exists` (an `F2Certificate` exists) and
`f2Source_verified_exists` (a verified candidate exists). The proofs are
existence statements, not constructions.
-/

namespace Paper.F2CatalogTransfer

open TableGeneration TableGeneration.Operations Paper.Normalization

theorem f2Source_certificate_exists {K : Nat} (t : F2Source K) :
    Nonempty (F2Certificate t) := by
  classical
  have hfn : (f2Points t.source.k).Nodup := by
    unfold f2Points
    exact List.Nodup.map f2Point_injective List.nodup_range
  have hpn : (List.ofFn t.points).Nodup :=
    t.literalF2.nodup_iff.mpr hfn
  have hpi : Function.Injective t.points := by
    simpa only [List.nodup_ofFn] using hpn
  have hnorm (i : Fin (2 * (t.source.k - 1) + 1)) :
      normalizePoint (t.points i) = t.points i := by
    have hm : t.points i ∈ f2Points t.source.k := by
      apply t.literalF2.mem_iff.mp
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    obtain ⟨n, _, he⟩ := List.mem_map.mp hm
    rw [← he]
    exact normalize_f2Point n
  have hni : Function.Injective (fun i => normalizePoint (t.points i)) := by
    intro i j he
    apply hpi
    simpa only [hnorm] using he
  have hfm : Point.frac 0 ∈ f2Points t.source.k := by
    unfold f2Points
    apply List.mem_map.mpr
    refine ⟨1, ?_, rfl⟩
    simp only [List.mem_range]
    have hk := t.source.hk
    omega
  have hi : ∃ i, t.points i = Point.frac 0 := by
    apply List.mem_ofFn.mp
    exact t.literalF2.mem_iff.mpr hfm
  obtain ⟨v, order, hvnode, hf, hinode⟩ :=
    Paper.PointNodes.exists_projective_enumeration t.points hni hi
  let weights : (W : Nat) → Fin (2 * (t.source.k - 1) + 1) → ℚ :=
    fun W => Paper.GeneralConstruction.phaseWeights t.source.k 2 t.points v
      (Paper.SignedLimbs.radix W t.source.k : ℚ) order
  have hcert (W : Nat) :
      Paper.PhaseIdentity.PairCertificate (weights W)
        (Paper.GenericPhase.indexedSourceRows (k := t.source.k) t.points)
        (fun j : Fin t.source.k => (Paper.SignedLimbs.radix W t.source.k : ℚ) ^ j.val) := by
    exact Paper.GeneralConstruction.pair_normalized_certificate
      (by have hk := t.source.hk; omega) t.points v order hvnode hf hinode
      (Paper.SignedLimbs.radix W t.source.k : ℚ)
  exact ⟨{weights := weights, certificate := hcert}⟩

theorem f2Source_verified_exists {K : Nat} (t : F2Source K) :
    ∃ v : Paper.PPEndToEnd.VerifiedPPCandidate K,
      v.source = t.source ∧
      VerifiedLiteralF2 v := by
  obtain ⟨cert⟩ := f2Source_certificate_exists t
  exact ⟨t.toVerified cert, rfl, toVerified_literal t cert⟩

end Paper.F2CatalogTransfer
