import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Framework.ToomCookTable
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.Layout
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.ToomCook

/-!
# Phase-Product Compiler: Coefficients

The inverse-based phase coefficients (`phaseCoeffFromPts`) and their agreement
with Cramer's rule (`cramerCoeffFromPts`, in `PhaseProduct/Coefficients.lean`
with its Gauss-Jordan `@[csimp]` lemma), the canonical interpolation
points (`alternatingPoint`, `genInterpolationPoints`) together with the proof
that they interpolate (`genInterpolationPoints_good`), and the bridge to the
pure Toom-Cook algebra (`toMathPoint`).

`Shor.interpMatrix` here is the compiler's own, indexed by `Fin (q k)`; the
generic `ToomCookMath.interpMatrix` that `GoodToomCookPoints` is defined
through is a different function. `q`, `interpEntry` and `GoodToomCookPoints`
are defined in `Framework/ToomCookTable.lean`.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators
open scoped Matrix

/-! =========================================================
    Interpolation and phase coefficients
========================================================= -/

/-- Coefficients obtained by multiplying the radix row by the inverse interpolation matrix. -/
noncomputable def phaseCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) : Fin (q k) → ℚ :=
  let B : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let v : Matrix (Fin 1) (Fin (q k)) ℚ := ToomCookMath.radixRow (q k) b * B⁻¹
  fun i => v 0 i

/-- Phase coefficients for a fixed chunk width. -/
noncomputable def phaseCoeffFromPtsWidth (k W : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  phaseCoeffFromPts k (ptsToFin k pts hpts) ((2 : ℚ) ^ W)

/--
`Matrix.cramer`-based coefficients agree with the `Matrix.inv`-based ones
whenever the interpolation matrix is invertible.

The argument is pure linear algebra and does not need the points to be
distinct integers (unlike a closed-form Lagrange-weight product, which would
only be valid for plain monomial rows): from `M *ᵥ cramer M v = M.det • v`
(`Matrix.mulVec_cramer`), left-multiplying by `M⁻¹` gives
`cramer M v = M.det • (M⁻¹ *ᵥ v)`, and dividing by the (nonzero) determinant
recovers `M⁻¹ *ᵥ v` from `cramer M v`.
-/
lemma cramerCoeffFromPts_eq_phaseCoeffFromPts
    {k : ℕ}
    (pts : Fin (q k) → Point)
    (b : ℚ)
    (hgood : (interpMatrix k pts).det ≠ 0) :
    cramerCoeffFromPts k pts b = phaseCoeffFromPts k pts b := by
  funext i
  set M : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts with hM
  set radixVec : Fin (q k) → ℚ := fun j => b ^ (j : ℕ) with hradixVec
  have hUnitT : IsUnit M.transpose.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hgood
  have hleft :
      M.transpose⁻¹ *ᵥ (M.transpose *ᵥ Matrix.cramer M.transpose radixVec)
        = Matrix.cramer M.transpose radixVec := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M.transpose hUnitT, Matrix.one_mulVec]
  have hkey :
      Matrix.cramer M.transpose radixVec
        = M.transpose.det • (M.transpose⁻¹ *ᵥ radixVec) := by
    calc Matrix.cramer M.transpose radixVec
        = M.transpose⁻¹ *ᵥ (M.transpose *ᵥ Matrix.cramer M.transpose radixVec) := hleft.symm
      _ = M.transpose⁻¹ *ᵥ (M.transpose.det • radixVec) := by rw [Matrix.mulVec_cramer]
      _ = M.transpose.det • (M.transpose⁻¹ *ᵥ radixVec) := Matrix.mulVec_smul _ _ _
  have hcomp :
      Matrix.cramer M.transpose radixVec i
        = M.transpose.det * (M.transpose⁻¹ *ᵥ radixVec) i := by
    have h := congrFun hkey i
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have hdet_ne : M.transpose.det ≠ 0 := by rw [Matrix.det_transpose]; exact hgood
  have hinv_component :
      (M.transpose⁻¹ *ᵥ radixVec) i
        = Matrix.cramer M.transpose radixVec i / M.transpose.det := by
    rw [eq_div_iff hdet_ne, mul_comm]
    exact hcomp.symm
  have hphase :
      phaseCoeffFromPts k pts b i = (M.transpose⁻¹ *ᵥ radixVec) i := by
    have hstep1 :
        phaseCoeffFromPts k pts b i = (radixVec ᵥ* M⁻¹) i := by
      show (ToomCookMath.radixRow (q k) b * M⁻¹) 0 i = (radixVec ᵥ* M⁻¹) i
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, ToomCookMath.radixRow, radixVec]
    rw [hstep1, ← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv]
  rw [hphase, hinv_component, cramerCoeffFromPts, hM, hradixVec]
  simp [Matrix.det_transpose]

/-- Phase coefficients selected from the common limb width of two operands. -/
noncomputable def phaseCoeffFromPtsForRegs (k : ℕ) (x z : ExtReg) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts

/-! =========================================================
    Canonical interpolation points
    The compiler uses its own `Point` type, while the algebraic Toom-Cook proof
    lives in `Proofs/Math/ToomCook.lean`. This section bridges the two representations.
========================================================= -/

/-- Alternating integer interpolation points around zero. -/
def alternatingPoint (i : ℕ) : Point :=
  if i % 2 == 0 then Point.int (i / 2 : ℤ) else Point.int (-((i + 1) / 2 : ℤ))

/-- Generate the canonical `2k - 1` interpolation points. -/
def genInterpolationPoints (k : ℕ) : List Point := (List.range (2 * k - 1)).map alternatingPoint

/-! =========================================================
    Toom-Cook Points And Interpolation Inputs

    These declarations connect compiler interpolation points with the pure math
    Toom-Cook matrix used by the final interpolation proof.
========================================================= -/

/--
Convert a compiler interpolation point to the pure-math point representation.
-/
def toMathPoint : Point → ToomCookMath.Point
  | Point.int z  => ToomCookMath.Point.int z
  | Point.frac c => ToomCookMath.Point.frac c

/--
The compiler's interpolation row is definitionally the pure-math adjusted row.
-/
lemma toMathPoint_interpEntry {k : ℕ} (p : Point) (j : Fin (q k)) :
    ToomCookMath.pointRow (q k) (toMathPoint p) j = interpEntry k p j := by
  cases p <;> rfl

lemma toMathPoint_alternatingPoint (i : ℕ) :
    toMathPoint (alternatingPoint i) = ToomCookMath.alternatingPoint i := by
  unfold alternatingPoint ToomCookMath.alternatingPoint
  unfold ToomCookMath.alternatingInt
  by_cases h : i % 2 == 0
  · simp [h, toMathPoint]
  · simp [h, toMathPoint]

lemma listToFin_genInterpolationPoints_toMathPoint
    (k : ℕ)
    (hpts : (genInterpolationPoints k).length = q k)
    (hmath : (ToomCookMath.genFiniteInterpolationPoints (q k)).length = q k)
    (i : Fin (q k)) :
    ToomCookMath.listToFin (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath i
      = toMathPoint (ToomCookMath.listToFin (genInterpolationPoints k) hpts i) := by
  simp [ToomCookMath.listToFin, genInterpolationPoints, ToomCookMath.genFiniteInterpolationPoints, toMathPoint_alternatingPoint]

lemma genInterpolationPoints_good (k : ℕ) :
    GoodToomCookPoints k (genInterpolationPoints k) (by simp [genInterpolationPoints, q]) := by
  let hpts : (genInterpolationPoints k).length = q k := by simp [genInterpolationPoints, q]
  let hmath : (ToomCookMath.genFiniteInterpolationPoints (q k)).length = q k := by
    simp [ToomCookMath.genFiniteInterpolationPoints]
  unfold GoodToomCookPoints
  have hgoodMath :
      ToomCookMath.GoodInterpolationPoints (row := ToomCookMath.pointRow (q k))
        (pts := ToomCookMath.listToFin (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath) :=
    ToomCookMath.genFiniteInterpolationPoints_good (q k) hmath
  apply ToomCookMath.GoodInterpolationPoints.congr_matrix
    (rowA := ToomCookMath.pointRow (q k))
    (rowB := interpEntry k)
    (ptsA := ToomCookMath.listToFin (ToomCookMath.genFiniteInterpolationPoints (q k)) hmath)
    (ptsB := ToomCookMath.listToFin (genInterpolationPoints k) hpts)
  · intro i j
    rw [listToFin_genInterpolationPoints_toMathPoint (k := k) (hpts := hpts) (hmath := hmath) (i := i)]
    exact toMathPoint_interpEntry (k := k) ((ToomCookMath.listToFin (genInterpolationPoints k) hpts) i) j
  · exact hgoodMath

end Shor
