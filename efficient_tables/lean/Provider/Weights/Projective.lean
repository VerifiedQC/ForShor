import Provider.Ladders.CertificateExists

/-!
# Executable projective interpolation weights

Defines executable weight functions for projective interpolation nodes:
`finiteWeightExec`, `infinityWeightExec`, `projectiveWeightsExec` and the
phase-scaled `phaseWeightsExec`. It proves they agree with the specified
weights (`projectiveWeightsExec_eq`, `phaseWeightsExec_eq`) and assembles
`sourceCertificate` and `verifiedSource` for an F2 source table.
-/

/- BEGIN Weights.lean sha256=b373490395a0a1082191ac788e2e6491cc81b0d257cb2d33fbd322560695d862 -/
namespace Paper.A4Exec

open TableGeneration TableGeneration.Operations Paper.Normalization

def infinityIndices {d : Nat} (pts : Fin (d+1) → Point) : Finset (Fin (d+1)) :=
  Finset.univ.filter (fun i => pts i = .frac 0)

def infinityPivot {d : Nat} (pts : Fin (d+1) → Point) : Fin (d+1) :=
  if h : (infinityIndices pts).Nonempty then
    (infinityIndices pts).min' h
  else Fin.last d

def order {d : Nat} (pts : Fin (d+1) → Point) :
    Fin (d+1) ≃ Fin (d+1) :=
  Equiv.swap (infinityPivot pts) (Fin.last d)

def finiteNodes {d : Nat} (pts : Fin (d+1) → Point) : Fin d → ℚ :=
  fun i => (sourcePoint (pts (order pts i.castSucc))).getD 0

def finiteWeightExec {d : Nat} (v : Fin d → ℚ) (b : ℚ) (i : Fin d) : ℚ :=
  ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, (b - v j) / (v i - v j)

def infinityWeightExec {d : Nat} (v : Fin d → ℚ) (b : ℚ) : ℚ :=
  b ^ d - ∑ i, finiteWeightExec v b i * v i ^ d

def projectiveWeightsExec {d : Nat} (v : Fin d → ℚ) (b : ℚ) :
    Fin (d+1) → ℚ :=
  Fin.lastCases (infinityWeightExec v b) (finiteWeightExec v b)

def phaseWeightsExec {d : Nat} (k power : Nat)
    (pts : Fin (d+1) → Point) (b : ℚ) : Fin (d+1) → ℚ :=
  normalizedWeights k power pts
    (fun i => projectiveWeightsExec (finiteNodes pts) b ((order pts).symm i))

end Paper.A4Exec
/- END Weights.lean -/

/- BEGIN Proof.lean sha256=eb4226a83b2d2a03730fbf682e885c282cd1efd8db353f824654a81c81e2737d -/
namespace Paper.A4Finite

open Paper.A4Exec TableGeneration TableGeneration.Operations
open Paper.Normalization

theorem infinityPivot_is_infinity {d : Nat}
    (pts : Fin (d+1) → Point) (hi : ∃ i, pts i = .frac 0) :
    pts (infinityPivot pts) = .frac 0 := by
  have hne : (infinityIndices pts).Nonempty := by
    obtain ⟨i, hpi⟩ := hi
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩⟩
  have hm := Finset.min'_mem (infinityIndices pts) hne
  have hp := (Finset.mem_filter.mp hm).2
  simpa [infinityPivot, hne] using hp

theorem finiteWeightExec_eq {d : Nat} (v : Fin d → ℚ) (b : ℚ) (i : Fin d) :
    finiteWeightExec v b i = Paper.Interpolation.finiteWeight v b i := by
  simp [finiteWeightExec, Paper.Interpolation.finiteWeight,
    Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro j hj
  ring

theorem infinityWeightExec_eq {d : Nat} (v : Fin d → ℚ) (b : ℚ) :
    infinityWeightExec v b = Paper.Interpolation.infinityWeight v b := by
  simp [infinityWeightExec, Paper.Interpolation.infinityWeight, finiteWeightExec_eq]

theorem projectiveWeightsExec_eq {d : Nat} (v : Fin d → ℚ) (b : ℚ) :
    projectiveWeightsExec v b = Paper.GeneralConstruction.projectiveWeights v b := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      simpa [projectiveWeightsExec, Paper.GeneralConstruction.projectiveWeights]
        using infinityWeightExec_eq v b
  | cast i =>
      simpa [projectiveWeightsExec, Paper.GeneralConstruction.projectiveWeights]
        using finiteWeightExec_eq v b i

end Paper.A4Finite
/- END Proof.lean -/

/- BEGIN Enumeration.lean sha256=4fd1ed4f7704ced52e4be16d28a10758fc4d741a81378589ed7e62a3dd795fc1 -/
namespace Paper.A4Nodes

open Paper.A4Exec Paper.A4Finite Paper.Normalization
open TableGeneration TableGeneration.Operations

theorem finiteNodes_properties {d : Nat} (pts : Fin (d+1) → Point)
    (hn : Function.Injective (fun i => normalizePoint (pts i)))
    (hi : ∃ i, pts i = .frac 0) :
    Function.Injective (finiteNodes pts) ∧
    (∀ i, sourcePoint (pts (order pts i.castSucc)) = some (finiteNodes pts i)) ∧
    sourcePoint (pts (order pts (Fin.last d))) = none := by
  have hinf : sourcePoint (pts (order pts (Fin.last d))) = none := by
    simp [order, infinityPivot_is_infinity pts hi, sourcePoint]
  have hnodes := Paper.PointNodes.sourcePoint_injective_of_normalized pts hn
  have hfinite (i : Fin d) : sourcePoint (pts (order pts i.castSucc)) ≠ none := by
    intro hz
    have he := hnodes (hz.trans hinf.symm)
    exact Fin.castSucc_ne_last i ((order pts).injective he)
  have hf (i : Fin d) :
      sourcePoint (pts (order pts i.castSucc)) = some (finiteNodes pts i) := by
    cases hq : sourcePoint (pts (order pts i.castSucc)) with
    | none => exact False.elim (hfinite i hq)
    | some z => simp [finiteNodes, hq]
  refine ⟨?_, hf, hinf⟩
  intro i j hij
  have he : sourcePoint (pts (order pts i.castSucc)) =
      sourcePoint (pts (order pts j.castSucc)) := by
    rw [hf, hf, hij]
  exact Fin.castSucc_inj.mp ((order pts).injective (hnodes he))

end Paper.A4Nodes
/- END Enumeration.lean -/

/- BEGIN Source.lean sha256=02c8733929ec38bbf8bf9111f9fb9774981499582f29853ba722eeb27d9de806 -/
namespace Paper.A4Certificate

open Paper.A4Exec Paper.A4Finite Paper.A4Nodes
open Paper.Normalization Paper.F2CatalogTransfer
open TableGeneration TableGeneration.Operations

theorem phaseWeightsExec_eq {d : Nat} (k power : Nat)
    (pts : Fin (d+1) → Point) (b : ℚ) :
    phaseWeightsExec k power pts b =
      Paper.GeneralConstruction.phaseWeights k power pts
        (finiteNodes pts) b (order pts) := by
  funext i
  simp [phaseWeightsExec, Paper.GeneralConstruction.phaseWeights,
    projectiveWeightsExec_eq]

theorem f2Source_nodes {K : Nat} (t : F2Source K) :
    Function.Injective (fun i => normalizePoint (t.points i)) ∧
    (∃ i, t.points i = Point.frac 0) := by
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
  exact ⟨hni, hi⟩

def sourceCertificate {K : Nat} (t : F2Source K) : F2Certificate t where
  weights := fun W => phaseWeightsExec t.source.k 2 t.points
    (Paper.SignedLimbs.radix W t.source.k : ℚ)
  certificate := by
    intro W
    obtain ⟨hni, hi⟩ := f2Source_nodes t
    obtain ⟨hv, hf, hinf⟩ := finiteNodes_properties t.points hni hi
    rw [phaseWeightsExec_eq]
    exact Paper.GeneralConstruction.pair_normalized_certificate
      (by have hk := t.source.hk; omega) t.points (finiteNodes t.points)
      (order t.points) hv hf hinf
      (Paper.SignedLimbs.radix W t.source.k : ℚ)

def verifiedSource {K : Nat} (t : F2Source K) :
    Paper.PPEndToEnd.VerifiedPPCandidate K :=
  t.toVerified (sourceCertificate t)

theorem verifiedSource_literal {K : Nat} (t : F2Source K) :
    (verifiedSource t).source = t.source ∧ VerifiedLiteralF2 (verifiedSource t) := by
  exact ⟨rfl, toVerified_literal t (sourceCertificate t)⟩

end Paper.A4Certificate
/- END Source.lean -/
