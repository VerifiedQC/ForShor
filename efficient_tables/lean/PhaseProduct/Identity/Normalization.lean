import PhaseProduct.Identity.PhaseIdentity
import Mathlib.Tactic.FieldSimp

/-!
# Projective normalization of source rows

Relates source rows to projective monomials: `sourceScale_ne_zero` shows the
source scale is nonzero and `sourceRow_eq_projective` identifies a source row
with its projective form. It then derives pair and triple certificates from
moment conditions (`pair_certificate_of_moments`,
`triple_certificate_of_moments`).
-/

namespace Paper.Normalization

theorem sourceScale_ne_zero (k : Nat) (pt : TableGeneration.Operations.Point) :
    sourceScale k pt ≠ 0 := by
  cases pt with
  | int z => simp [sourceScale]
  | frac m =>
    by_cases hm : m = 0
    · simp [sourceScale, hm]
    · simp [sourceScale, hm, pow_ne_zero, Int.cast_ne_zero]

theorem sourceRow_eq_projective {k : Nat} (hk : 0 < k)
    (pt : TableGeneration.Operations.Point) (j : Fin k) :
    (TableGeneration.expectedRow pt j : ℚ) =
      sourceScale k pt * projectiveMonomial (k-1) (sourcePoint pt) j.val := by
  have hj : j.val ≤ k - 1 := by omega
  cases pt with
  | int z => simp [TableGeneration.expectedRow, sourceScale, sourcePoint, projectiveMonomial]
  | frac m =>
    by_cases hm : m = 0
    · subst m
      by_cases he : j.val = k - 1
      · simp [TableGeneration.expectedRow, sourceScale, sourcePoint, projectiveMonomial, he]
      · have hn : k - 1 - j.val ≠ 0 := by omega
        simp [TableGeneration.expectedRow, sourceScale, sourcePoint, projectiveMonomial, he, hn]
    · have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
      simp only [TableGeneration.expectedRow, Int.cast_pow, sourceScale, sourcePoint,
        if_neg hm, projectiveMonomial]
      rw [pow_sub₀ (m : ℚ) hmQ hj, inv_pow]

theorem projectiveMonomial_mul (a b i j : Nat) (hi : i ≤ a) (hj : j ≤ b)
    (pt : Option ℚ) :
    projectiveMonomial a pt i * projectiveMonomial b pt j =
      projectiveMonomial (a+b) pt (i+j) := by
  cases pt with
  | some z => simp [projectiveMonomial, pow_add]
  | none =>
    by_cases hia : i = a <;> by_cases hjb : j = b
    · simp [projectiveMonomial, hia, hjb]
    · have hne : i+j ≠ a+b := by omega
      simp [projectiveMonomial, hia, hjb, hne]
    · have hne : i+j ≠ a+b := by omega
      simp [projectiveMonomial, hia, hjb, hne]
    · have hne : i+j ≠ a+b := by omega
      simp [projectiveMonomial, hia, hjb, hne]

theorem projectiveMonomial_triple (a b c i j t : Nat)
    (hi : i ≤ a) (hj : j ≤ b) (ht : t ≤ c) (pt : Option ℚ) :
    projectiveMonomial a pt i * projectiveMonomial b pt j * projectiveMonomial c pt t =
      projectiveMonomial (a+b+c) pt (i+j+t) := by
  rw [projectiveMonomial_mul a b i j hi hj]
  exact projectiveMonomial_mul (a+b) c (i+j) t (by omega) ht pt

theorem pair_certificate_of_moments {k q : Nat} (hk : 0 < k)
    (pts : Fin q → TableGeneration.Operations.Point) (weight : Fin q → ℚ) (b : ℚ)
    (hm : MomentCertificate (2*(k-1)) (fun l => sourcePoint (pts l)) weight b) :
    PhaseIdentity.PairCertificate (k := k) (normalizedWeights k 2 pts weight)
      (fun l j => (TableGeneration.expectedRow (pts l) j : ℚ)) (fun j => b ^ j.val) := by
  intro i j
  have hi : i.val ≤ k-1 := by omega
  have hj : j.val ≤ k-1 := by omega
  have hmon := hm (i.val+j.val) (by omega)
  rw [pow_add] at hmon
  rw [← hmon]
  apply Finset.sum_congr rfl
  intro l _
  dsimp only
  rw [sourceRow_eq_projective hk, sourceRow_eq_projective hk]
  have hp := projectiveMonomial_mul (k-1) (k-1) i.val j.val hi hj (sourcePoint (pts l))
  have hd : k-1+(k-1) = 2*(k-1) := by omega
  rw [hd] at hp
  rw [← hp]
  dsimp only [normalizedWeights]
  field_simp [sourceScale_ne_zero k (pts l)] <;> ring

theorem triple_certificate_of_moments {k q : Nat} (hk : 0 < k)
    (pts : Fin q → TableGeneration.Operations.Point) (weight : Fin q → ℚ) (b : ℚ)
    (hm : MomentCertificate (3*(k-1)) (fun l => sourcePoint (pts l)) weight b) :
    PhaseIdentity.TripleCertificate (k := k) (normalizedWeights k 3 pts weight)
      (fun l j => (TableGeneration.expectedRow (pts l) j : ℚ)) (fun j => b ^ j.val) := by
  intro i j t
  have hi : i.val ≤ k-1 := by omega
  have hj : j.val ≤ k-1 := by omega
  have ht : t.val ≤ k-1 := by omega
  have hmon := hm (i.val+j.val+t.val) (by omega)
  simp only [pow_add] at hmon
  rw [← hmon]
  apply Finset.sum_congr rfl
  intro l _
  dsimp only
  rw [sourceRow_eq_projective hk, sourceRow_eq_projective hk, sourceRow_eq_projective hk]
  have hp := projectiveMonomial_triple (k-1) (k-1) (k-1) i.val j.val t.val hi hj ht (sourcePoint (pts l))
  have hd : k-1+(k-1)+(k-1) = 3*(k-1) := by omega
  rw [hd] at hp
  rw [← hp]
  dsimp only [normalizedWeights]
  field_simp [sourceScale_ne_zero k (pts l)] <;> ring

end Paper.Normalization
