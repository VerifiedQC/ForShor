import PhaseProduct.Identity.PointNodes
import Mathlib.Tactic.IntervalCases

/-!
# Canonical nodes

Properties of the canonical point enumeration `canonicalPoint`: it is
injective (`canonicalPoint_injective`), already normalized
(`normalize_canonicalPoint`), and injective projectively
(`canonical_projective_injective`). `canonical_enumeration` provides the
resulting enumeration for positive `d`.
-/

namespace Paper.CanonicalNodes
open TableGeneration TableGeneration.Operations Paper.Normalization

theorem two_pow_tail_gt_one (n : Nat) : (1 : Int) < 2 ^ (1 + n / 4) := by
  have h := (pow_right_strictMono₀ (show (1 : Int) < 2 by decide)) (show 0 < 1+n/4 by omega)
  simpa using h

theorem canonical_initial_ne_tail (a n : Nat) (ha : a < 4) :
    canonicalPoint a ≠ canonicalPoint (n+4) := by
  have hp := two_pow_tail_gt_one n
  have hn : n % 4 < 4 := Nat.mod_lt n (by decide)
  intro he
  interval_cases a <;> interval_cases hm : n % 4 <;>
    simp [canonicalPoint, hm] at he <;> omega

theorem canonical_tail_injective (n m : Nat)
    (he : canonicalPoint (n+4) = canonicalPoint (m+4)) : n = m := by
  have hp := two_pow_tail_gt_one n
  have hq := two_pow_tail_gt_one m
  have hn : n % 4 < 4 := Nat.mod_lt n (by decide)
  have hm : m % 4 < 4 := Nat.mod_lt m (by decide)
  interval_cases hnq : n % 4 <;> interval_cases hmq : m % 4 <;>
    simp [canonicalPoint, hnq, hmq] at he <;> omega

theorem canonicalPoint_injective : Function.Injective canonicalPoint := by
  intro a b he
  by_cases ha : a < 4
  · by_cases hb : b < 4
    · interval_cases a <;> interval_cases b <;> norm_num [canonicalPoint] at * <;> cases he
    · have hb' : b = (b-4)+4 := by omega
      rw [hb'] at he
      exact False.elim (canonical_initial_ne_tail a (b-4) ha he)
  · have ha' : a = (a-4)+4 := by omega
    rw [ha'] at he
    by_cases hb : b < 4
    · exact False.elim (canonical_initial_ne_tail b (a-4) hb he.symm)
    · have hb' : b = (b-4)+4 := by omega
      rw [hb'] at he
      have hn := canonical_tail_injective (a-4) (b-4) he
      omega

theorem normalize_canonicalPoint (n : Nat) : normalizePoint (canonicalPoint n) = canonicalPoint n := by
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [canonicalPoint, normalizePoint]
  · have he : n = (n-4)+4 := by omega
    rw [he]
    have hp := two_pow_tail_gt_one (n-4)
    have hb : (n-4) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hp1 : (2 : Int)^(1+(n-4)/4) ≠ 1 := by omega
    have hpn1 : (2 : Int)^(1+(n-4)/4) ≠ -1 := by omega
    have hnp1 : -((2 : Int)^(1+(n-4)/4)) ≠ 1 := by omega
    have hnpn1 : -((2 : Int)^(1+(n-4)/4)) ≠ -1 := by omega
    interval_cases hm : (n-4) % 4 <;>
      simp [canonicalPoint, hm, normalizePoint, hp1, hpn1, hnp1, hnpn1]

theorem canonical_projective_injective :
    Function.Injective (fun n => sourcePoint (canonicalPoint n)) := by
  apply PointNodes.sourcePoint_injective_of_normalized
  simpa only [normalize_canonicalPoint] using canonicalPoint_injective

theorem canonicalPoints_eq_ofFn (mode : ProductMode) (k : Nat) :
    canonicalPoints mode k =
      List.ofFn (fun i : Fin (mode.pointCount k) => canonicalPoint i.val) := by
  rw [List.ofFn_eq_map]
  unfold canonicalPoints
  change (List.range (mode.pointCount k)).map canonicalPoint =
    (List.finRange (mode.pointCount k)).map (canonicalPoint ∘ Fin.val)
  rw [← List.map_map, List.map_coe_finRange_eq_range]

theorem canonical_enumeration {d : Nat} (hd : 0 < d) :
    ∃ (v : Fin d → ℚ) (order : Fin (d+1) ≃ Fin (d+1)),
      Function.Injective v ∧
      (∀ i, sourcePoint (canonicalPoint (order i.castSucc).val) = some (v i)) ∧
      sourcePoint (canonicalPoint (order (Fin.last d)).val) = none := by
  apply PointNodes.exists_projective_enumeration (fun i => canonicalPoint i.val)
  · intro i j he
    apply Fin.ext
    apply canonicalPoint_injective
    simpa only [normalize_canonicalPoint] using he
  · exact ⟨⟨1, by omega⟩, rfl⟩

end Paper.CanonicalNodes
