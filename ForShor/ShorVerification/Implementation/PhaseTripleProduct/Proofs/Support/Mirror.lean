import ForShor.ShorVerification.Implementation.PhaseTripleProduct.Statement
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.ToomCook
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The Toom–Cook identity at an arbitrary number of points

Pure algebra for the PTP node. Nothing here mentions widths, bands or the recursion; the node
identity (`Values/Semantics.lean`) uses `toomCook_exact`.

`r` is the arity of the product: `3` for the phase triple product. A table with `k` limb
registers evaluates each of the `r` operands' limb polynomials (degree `≤ k - 1`) at
`r (k - 1) + 1` points; the product polynomial has degree `≤ r (k - 1)`, so that many distinct
projective points determine it, and the interpolation weights at the radix recover the product
of the operands.

The interpolation weights are ForShor's `ToomCookMath.interpCoeff`
(`PhaseProduct/Proofs/Math/ToomCook.lean`), which is generic in the matrix size, and its
correctness theorem `ToomCookMath.interpCoeff_correct` is used as is. ForShor states C2
(invertibility) only at size `q k = 2k - 1`; `pointRowQ_good` below is the same
projective-Vandermonde argument at an arbitrary size, which the phase triple product (`3k - 2`)
needs.

Point conventions are the Framework's (`Operations.Point`): `int z` is the affine point `z`,
i.e. projective `(z : 1)`; `frac c` is the point `1 / c`, projective `(1 : c)`; `frac 0` is the
point at infinity. These are the conventions of `expectedRow` and of ForShor's `interpEntry`.
-/

noncomputable section

namespace Shor
namespace PTP

open Polynomial Finset
open Operations

/-! ## Projective coordinates and interpolation rows -/

/-- First projective coordinate of a point. -/
def projV : Point → ℚ
  | .int z => (z : ℚ)
  | .frac _ => 1

/-- Second projective coordinate of a point. -/
def projW : Point → ℚ
  | .int _ => 1
  | .frac c => (c : ℚ)

theorem pointRowQ_eq (N : ℕ) (p : Point) (j : Fin N) :
    pointRowQ N p j = projV p ^ (j : ℕ) * projW p ^ (N - 1 - (j : ℕ)) := by
  cases p <;> simp [pointRowQ, projV, projW]

/-- Two points are different projective points. The same inequality as
ForShor's `Shor.DistinctPair`, over `ℚ`. -/
def DistinctPair (p p' : Point) : Prop :=
  projV p' * projW p - projV p * projW p' ≠ 0

/-- Normalized-distinct points (the `Nodup` clause of the table contract) are
projectively distinct. -/
theorem distinctPair_of_normalize_ne {p p' : Point}
    (h : normalizePoint p ≠ normalizePoint p') : DistinctPair p p' := by
  unfold DistinctPair
  cases p with
  | int z =>
    cases p' with
    | int z' =>
      simp only [projV, projW, mul_one, sub_ne_zero]
      intro hq
      apply h
      simp only [normalizePoint]
      exact congrArg Point.int (by exact_mod_cast hq.symm)
    | frac c =>
      simp only [projV, projW, mul_one]
      intro hq
      have hzc : z * c = 1 := by
        have : ((z * c : ℤ) : ℚ) = 1 := by push_cast; linarith
        exact_mod_cast this
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hzc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h (by simp [normalizePoint])
      · exact h (by simp [normalizePoint])
  | frac c =>
    cases p' with
    | int z =>
      simp only [projV, projW, mul_one]
      intro hq
      have hzc : z * c = 1 := by
        have : ((z * c : ℤ) : ℚ) = 1 := by push_cast; linarith
        exact_mod_cast this
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hzc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h (by simp [normalizePoint])
      · exact h (by simp [normalizePoint])
    | frac c' =>
      simp only [projV, projW, one_mul, sub_ne_zero]
      intro hq
      have : c = c' := by exact_mod_cast hq
      subst this
      exact h rfl

theorem pairwise_distinct_of_nodup {pts : List Point}
    (h : (pts.map normalizePoint).Nodup) : pts.Pairwise DistinctPair := by
  have h' : List.Pairwise (fun a b => normalizePoint a ≠ normalizePoint b) pts :=
    List.pairwise_map.mp h
  exact h'.imp distinctPair_of_normalize_ne

/-- C2 at an arbitrary size: pairwise projectively distinct points make the
interpolation matrix invertible. -/
theorem pointRowQ_good (pts : List Point) (h : pts.Pairwise DistinctPair) :
    ToomCookMath.GoodInterpolationPoints (row := pointRowQ pts.length)
      (pts := fun i : Fin pts.length => pts.get i) := by
  unfold ToomCookMath.GoodInterpolationPoints
  have hM : ToomCookMath.interpMatrix (pointRowQ pts.length) (fun i : Fin pts.length => pts.get i)
      = Matrix.projVandermonde (fun i => projV (pts.get i)) (fun i => projW (pts.get i)) := by
    ext i j
    simp only [ToomCookMath.interpMatrix, Matrix.projVandermonde_apply, pointRowQ_eq, Fin.val_rev]
    congr 2
    omega
  rw [hM, Matrix.det_projVandermonde]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
  have hij : i < j := Finset.mem_Ioi.mp hj
  exact List.pairwise_iff_get.mp h i j hij

/-! ## Homogeneous evaluation -/

/-- Degree-`d` homogeneous evaluation of `p` at the projective point `(v : w)`:
`∑_{i ≤ d} pᵢ vⁱ w^(d-i)`. -/
def hom (d : ℕ) (p : ℚ[X]) (v w : ℚ) : ℚ :=
  ∑ i ∈ range (d + 1), p.coeff i * v ^ i * w ^ (d - i)

theorem hom_of_ne_zero {d : ℕ} {p : ℚ[X]} {v w : ℚ} (hp : p.natDegree ≤ d) (hw : w ≠ 0) :
    hom d p v w = w ^ d * p.eval (v / w) := by
  rw [hom, eval_eq_sum_range' (n := d + 1) (by omega), mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi : i ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hsplit : w ^ d = w ^ i * w ^ (d - i) := by rw [← pow_add]; congr 1; omega
  rw [div_pow, hsplit]
  have hwi : w ^ i ≠ 0 := pow_ne_zero _ hw
  field_simp

theorem hom_zero_right (d : ℕ) (p : ℚ[X]) (v : ℚ) : hom d p v 0 = p.coeff d * v ^ d := by
  rw [hom, sum_eq_single_of_mem d (mem_range.mpr (Nat.lt_succ_self d))]
  · simp
  · intro i hi hne
    have : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hi)) hne
    rw [zero_pow (by omega), mul_zero]

theorem hom_mul {d e : ℕ} {p q : ℚ[X]} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ e) (v w : ℚ) :
    hom (d + e) (p * q) v w = hom d p v w * hom e q v w := by
  by_cases hw : w = 0
  · subst hw
    rw [hom_zero_right, hom_zero_right, hom_zero_right, coeff_mul_add_eq_of_natDegree_le hp hq,
      pow_add]
    ring
  · rw [hom_of_ne_zero (natDegree_mul_le_of_le hp hq) hw, hom_of_ne_zero hp hw,
      hom_of_ne_zero hq hw, eval_mul, pow_add]
    ring

theorem hom_prod : ∀ (r : ℕ) (f : Fin r → ℚ[X]) (d : ℕ), (∀ s, (f s).natDegree ≤ d) →
    (∏ s, f s).natDegree ≤ r * d ∧ ∀ v w, hom (r * d) (∏ s, f s) v w = ∏ s, hom d (f s) v w
  | 0, f, d, _ => by
      refine ⟨by simp, fun v w => ?_⟩
      simp [hom]
  | r + 1, f, d, hf => by
      obtain ⟨hdeg, hval⟩ := hom_prod r (fun s => f s.succ) d (fun s => hf _)
      have hrd : (r + 1) * d = d + r * d := by ring
      refine ⟨?_, fun v w => ?_⟩
      · rw [Fin.prod_univ_succ, hrd]
        exact natDegree_mul_le_of_le (hf 0) hdeg
      · rw [Fin.prod_univ_succ, Fin.prod_univ_succ, hrd, hom_mul (hf 0) hdeg, hval]

/-- A sum over `Fin N` of coefficients against homogeneous monomials is the
homogeneous evaluation of degree `N - 1`. -/
theorem sum_fin_eq_hom (N : ℕ) (hN : 0 < N) (p : ℚ[X]) (v w : ℚ) :
    ∑ l : Fin N, p.coeff l * (v ^ (l : ℕ) * w ^ (N - 1 - (l : ℕ))) = hom (N - 1) p v w := by
  rw [hom, show N - 1 + 1 = N by omega]
  rw [Fin.sum_univ_eq_sum_range (fun l => p.coeff l * (v ^ l * w ^ (N - 1 - l))) N]
  refine sum_congr rfl fun i _ => by ring

/-! ## Limb polynomials -/

/-- The polynomial `∑ⱼ Lⱼ Xʲ` of a limb vector. -/
def limbPoly {k : ℕ} (L : Fin k → ℤ) : ℚ[X] :=
  ∑ j : Fin k, C (L j : ℚ) * X ^ (j : ℕ)

theorem limbPoly_coeff {k : ℕ} (L : Fin k → ℤ) (i : ℕ) (hi : i < k) :
    (limbPoly L).coeff i = (L ⟨i, hi⟩ : ℚ) := by
  simp only [limbPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro j _ hj
    have : i ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
    simp [this]
  · simp

theorem limbPoly_natDegree {k : ℕ} (L : Fin k → ℤ) : (limbPoly L).natDegree ≤ k - 1 := by
  unfold limbPoly
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- Homogeneous evaluation of a limb polynomial is the sum against
homogeneous monomials of degree `k - 1`. -/
theorem hom_limbPoly {k : ℕ} (hk : 0 < k) (L : Fin k → ℤ) (v w : ℚ) :
    hom (k - 1) (limbPoly L) v w = ∑ j : Fin k, (L j : ℚ) * (v ^ (j : ℕ) * w ^ (k - 1 - (j : ℕ))) := by
  rw [← sum_fin_eq_hom k hk]
  refine sum_congr rfl fun j _ => ?_
  rw [limbPoly_coeff L j j.isLt]

/-! ## The identity -/

/-- **Arity-`r` Toom–Cook exactness.** If `pts` has `r (k - 1) + 1` pairwise
projectively distinct points, then for every `r`-tuple of limb vectors, the
interpolation weights at radix `B` applied to the products of the operands'
homogeneous point values recover the product of the operands' radix-`B`
values. -/
theorem toomCook_exact (r k : ℕ) (hk : 0 < k) (pts : List Point)
    (hlen : pts.length = r * (k - 1) + 1) (hd : pts.Pairwise DistinctPair)
    (B : ℚ) (L : Fin r → Fin k → ℤ) :
    ∑ t : Fin pts.length,
        ToomCookMath.interpCoeff (pointRowQ pts.length) (fun i : Fin pts.length => pts.get i) B t *
          ∏ s, ∑ j : Fin k, (L s j : ℚ) *
            (projV (pts.get t) ^ (j : ℕ) * projW (pts.get t) ^ (k - 1 - (j : ℕ)))
      = ∏ s, ∑ j : Fin k, (L s j : ℚ) * B ^ (j : ℕ) := by
  set N := pts.length with hN
  have hN0 : 0 < N := by omega
  have hN1 : N - 1 = r * (k - 1) := by omega
  set Pp : ℚ[X] := ∏ s, limbPoly (L s) with hPp
  obtain ⟨_, hval⟩ := hom_prod r (fun s => limbPoly (L s)) (k - 1) (fun s => limbPoly_natDegree _)
  -- each point value is the product polynomial's row evaluation
  have hpt : ∀ t : Fin N,
      (∏ s, ∑ j : Fin k, (L s j : ℚ) *
          (projV (pts.get t) ^ (j : ℕ) * projW (pts.get t) ^ (k - 1 - (j : ℕ))))
        = ToomCookMath.evalAtPoint N (pointRowQ N) (fun l => Pp.coeff l) (pts.get t) := by
    intro t
    unfold ToomCookMath.evalAtPoint
    simp only [pointRowQ_eq]
    rw [sum_fin_eq_hom N hN0, hN1, hPp, hval]
    exact Finset.prod_congr rfl fun s _ => (hom_limbPoly hk (L s) _ _).symm
  have hrad : ToomCookMath.evalAtRadix N (fun l => Pp.coeff l) B
      = ∏ s, ∑ j : Fin k, (L s j : ℚ) * B ^ (j : ℕ) := by
    unfold ToomCookMath.evalAtRadix
    have h1 : ∑ j : Fin N, Pp.coeff j * B ^ (j : ℕ)
        = ∑ j : Fin N, Pp.coeff j * (B ^ (j : ℕ) * (1 : ℚ) ^ (N - 1 - (j : ℕ))) := by
      simp
    rw [h1, sum_fin_eq_hom N hN0, hN1, hPp, hval]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hom_limbPoly hk]
    simp
  simp_rw [hpt]
  rw [ToomCookMath.interpCoeff_correct (pointRowQ N) (fun i : Fin N => pts.get i) B
    (fun l => Pp.coeff l) (pointRowQ_good pts hd), hrad]

/-! ## Limb split -/

/-- Top-heavy split at radix `B`: lower limbs are `B`-digits, the top limb
takes the (signed) remainder. ForShor's layout (`phaseSplitLogicalWidth`):
the lower `k - 1` chunks have width `W`, the top chunk the rest. -/
def limbs (k : ℕ) (B : ℤ) (x : ℤ) (j : Fin k) : ℤ :=
  if (j : ℕ) + 1 = k then x / B ^ (j : ℕ) else (x / B ^ (j : ℕ)) % B

theorem lower_add_top (B : ℤ) (hB : 0 ≤ B) (x : ℤ) : ∀ m : ℕ,
    (∑ j ∈ range m, (x / B ^ j % B) * B ^ j) + x / B ^ m * B ^ m = x
  | 0 => by simp
  | m + 1 => by
      have ih := lower_add_top B hB x m
      have hdiv : x / B ^ (m + 1) = x / B ^ m / B := by
        rw [pow_succ, Int.ediv_ediv_of_nonneg (pow_nonneg hB m)]
      rw [sum_range_succ, hdiv, pow_succ]
      have := Int.emod_add_mul_ediv (x / B ^ m) B
      linear_combination ih + (B ^ m) * this

theorem sum_limbs (k : ℕ) (hk : 0 < k) (B : ℤ) (hB : 0 ≤ B) (x : ℤ) :
    ∑ j : Fin k, limbs k B x j * B ^ (j : ℕ) = x := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  have hlow : ∑ j : Fin m, limbs (m + 1) B x (Fin.castSucc j) * B ^ ((Fin.castSucc j : Fin (m + 1)) : ℕ)
      = ∑ j ∈ range m, (x / B ^ j % B) * B ^ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (x / B ^ j % B) * B ^ j) m]
    refine sum_congr rfl fun j _ => ?_
    have : (j : ℕ) + 1 ≠ m + 1 := by omega
    simp only [limbs, Fin.val_castSucc, this, ↓reduceIte]
  rw [hlow]
  simp only [limbs, Fin.val_last, ite_true]
  exact lower_add_top B hB x m

theorem expectedRow_cast {k : Nat} (pt : Point) (j : Fin k) :
    ((expectedRow (k := k) pt j : ℤ) : ℚ) = projV pt ^ (j : ℕ) * projW pt ^ (k - 1 - (j : ℕ)) := by
  cases pt <;> simp [expectedRow, projV, projW]

end PTP
end Shor
