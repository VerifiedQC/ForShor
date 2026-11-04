import PhaseProduct.Identity.GeneralConstruction
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.List.FinRange

/-!
# Point nodes and projective enumeration

Facts about `sourcePoint` and point normalization: `sourcePoint_none_iff`
(only `frac 0` has no source point), `sourcePoint_eq_iff_normalize`, and
injectivity on normalized points (`sourcePoint_injective_of_normalized`). It
derives projective enumerations from point tuples and valid point lists
(`exists_projective_enumeration`, `exists_enumeration_of_validPointList`).
-/

namespace Paper.PointNodes
open TableGeneration TableGeneration.Operations Normalization

theorem sourcePoint_none_iff (pt : Point) : sourcePoint pt = none ↔ pt = .frac 0 := by
  cases pt with
  | int z => simp [sourcePoint]
  | frac m => by_cases hm : m = 0 <;> simp [sourcePoint, hm]

theorem normalize_preserves_sourcePoint (pt : Point) :
    sourcePoint (normalizePoint pt) = sourcePoint pt := by
  cases pt with
  | int z => rfl
  | frac m =>
    by_cases hp : m = 1
    · subst m; norm_num [normalizePoint, sourcePoint]
    · by_cases hn : m = -1
      · subst m; norm_num [normalizePoint, sourcePoint]
      · simp [normalizePoint, hp, hn]

theorem integer_reciprocal_collision (z m : Int) (hm : m ≠ 0)
    (h : (z : ℚ) = (m : ℚ)⁻¹) :
    (z = 1 ∧ m = 1) ∨ (z = -1 ∧ m = -1) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hprodQ : (z : ℚ) * (m : ℚ) = 1 := by rw [h]; exact inv_mul_cancel₀ hmQ
  have hprod : z * m = 1 := by exact_mod_cast hprodQ
  exact Int.eq_one_or_neg_one_of_mul_eq_one' hprod

theorem normalize_eq_of_int_frac (z m : Int)
    (h : sourcePoint (.int z) = sourcePoint (.frac m)) :
    normalizePoint (.int z) = normalizePoint (.frac m) := by
  by_cases hm : m = 0
  · simp [sourcePoint, hm] at h
  · have hq : (z : ℚ) = (m : ℚ)⁻¹ := by simpa [sourcePoint, hm] using h
    rcases integer_reciprocal_collision z m hm hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [normalizePoint]

theorem sourcePoint_eq_iff_normalize (p q : Point) :
    sourcePoint p = sourcePoint q ↔ normalizePoint p = normalizePoint q := by
  constructor
  · intro h
    cases p with
    | int z =>
      cases q with
      | int w =>
        have hzw : z = w := by simpa [sourcePoint] using h
        subst w; rfl
      | frac m => exact normalize_eq_of_int_frac z m h
    | frac m =>
      cases q with
      | int z => exact (normalize_eq_of_int_frac z m h.symm).symm
      | frac n =>
        by_cases hm : m = 0
        · have hn : n = 0 := by simpa [sourcePoint, hm] using h.symm
          subst m; subst n; rfl
        · by_cases hn : n = 0
          · simp [sourcePoint, hm, hn] at h
          · have hi : (m : ℚ)⁻¹ = (n : ℚ)⁻¹ := by simpa [sourcePoint, hm, hn] using h
            have he : (m : ℚ) = (n : ℚ) := inv_inj.mp hi
            have hmn : m = n := by exact_mod_cast he
            subst n; rfl
  · intro h
    have he := congrArg sourcePoint h
    simpa only [normalize_preserves_sourcePoint] using he

theorem sourcePoint_injective_of_normalized {ι : Type} (pts : ι → Point)
    (h : Function.Injective (fun i => normalizePoint (pts i))) :
    Function.Injective (fun i => sourcePoint (pts i)) := by
  intro i j hij
  exact h ((sourcePoint_eq_iff_normalize (pts i) (pts j)).mp hij)

theorem exists_projective_enumeration {d : Nat} (pts : Fin (d+1) → Point)
    (hn : Function.Injective (fun i => normalizePoint (pts i)))
    (hi : ∃ i, pts i = .frac 0) :
    ∃ (v : Fin d → ℚ) (order : Fin (d+1) ≃ Fin (d+1)),
      Function.Injective v ∧
      (∀ i, sourcePoint (pts (order i.castSucc)) = some (v i)) ∧
      sourcePoint (pts (order (Fin.last d))) = none := by
  classical
  obtain ⟨pivot, hpivot⟩ := hi
  let order : Fin (d+1) ≃ Fin (d+1) := Equiv.swap pivot (Fin.last d)
  have hinf : sourcePoint (pts (order (Fin.last d))) = none := by
    simp [order, hpivot, sourcePoint]
  have hnodes := sourcePoint_injective_of_normalized pts hn
  have hfinite (i : Fin d) : sourcePoint (pts (order i.castSucc)) ≠ none := by
    intro hz
    have he := hnodes (hz.trans hinf.symm)
    exact Fin.castSucc_ne_last i (order.injective he)
  let v : Fin d → ℚ := fun i => (sourcePoint (pts (order i.castSucc))).getD 0
  have hf (i : Fin d) : sourcePoint (pts (order i.castSucc)) = some (v i) := by
    cases hq : sourcePoint (pts (order i.castSucc)) with
    | none => exact False.elim (hfinite i hq)
    | some z => simp [v, hq]
  refine ⟨v, order, ?_, hf, hinf⟩
  intro i j hij
  have he : sourcePoint (pts (order i.castSucc)) = sourcePoint (pts (order j.castSucc)) := by
    rw [hf, hf, hij]
  exact Fin.castSucc_inj.mp (order.injective (hnodes he))

theorem validPointList_nodes_injective {q : Nat} (mode : ProductMode) (k : Nat)
    (pts : Fin q → Point) (hvalid : ValidPointList mode k (List.ofFn pts)) :
    Function.Injective (fun i => sourcePoint (pts i)) := by
  apply sourcePoint_injective_of_normalized pts
  have h := hvalid.2.1
  simpa only [List.map_ofFn, List.nodup_ofFn, Function.comp_def] using h

theorem exists_enumeration_of_validPointList {d : Nat} (mode : ProductMode) (k : Nat)
    (pts : Fin (d+1) → Point) (hvalid : ValidPointList mode k (List.ofFn pts))
    (hi : Point.frac 0 ∈ List.ofFn pts) :
    ∃ (v : Fin d → ℚ) (order : Fin (d+1) ≃ Fin (d+1)),
      Function.Injective v ∧
      (∀ i, sourcePoint (pts (order i.castSucc)) = some (v i)) ∧
      sourcePoint (pts (order (Fin.last d))) = none := by
  apply exists_projective_enumeration pts
  · simpa only [List.map_ofFn, List.nodup_ofFn, Function.comp_def] using hvalid.2.1
  · exact List.mem_ofFn.mp hi

theorem canonicalPoints_has_infinity (mode : ProductMode) (k : Nat) (hk : 2 ≤ k) :
    Point.frac 0 ∈ canonicalPoints mode k := by
  unfold canonicalPoints
  apply List.mem_map.mpr
  refine ⟨1, List.mem_range.mpr ?_, rfl⟩
  cases mode <;> simp only [ProductMode.pointCount] <;> omega

end Paper.PointNodes
