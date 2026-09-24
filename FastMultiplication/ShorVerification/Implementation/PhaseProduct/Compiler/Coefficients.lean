import FastMultiplication.ShorVerification.Framework.ToomCookTable
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Layout
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.ToomCook

/-!
# Phase-Product Compiler: Coefficients

Interpolation and phase-coefficient definitions (`interpMatrix`,
`phaseCoeffFromPts`, `cramerCoeffFromPts`, ...), the canonical interpolation
points (`alternatingPoint`, `genInterpolationPoints`), and the bridge to the
pure Toom-Cook math file (`toMathPoint`).

`SUBMISSION_PLAN.md` S2.0 moved `q`, `interpEntry` and `GoodToomCookPoints`
(C1's count and C2's statement) into `Framework/ToomCookTable.lean`. They keep
their fully-qualified names; `Shor.interpMatrix` — the compiler's own, not to
be confused with the generic `ToomCookMath.interpMatrix` that moved — the
Cramer coefficients, the canonical point ladder and `genInterpolationPoints_good`
all stayed here.
-/

namespace Shor
open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Interpolation and phase coefficients
========================================================= -/

/-- Interpolation matrix built from the chosen point set. -/
def interpMatrix (k : ℕ) (pts : Fin (q k) → Point) : Matrix (Fin (q k)) (Fin (q k)) ℚ :=
  fun i j => interpEntry k (pts i) j

/-- Row vector `[1, b, b^2, ...]` used for interpolation evaluation. -/
def radixRow (k : ℕ) (b : ℚ) : Matrix (Fin 1) (Fin (q k)) ℚ := fun _ j => b ^ (j : ℕ)

/-- Coefficients obtained by multiplying the radix row by the inverse interpolation matrix. -/
noncomputable def phaseCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) : Fin (q k) → ℚ :=
  let B : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let v : Matrix (Fin 1) (Fin (q k)) ℚ := radixRow k b * B⁻¹
  fun i => v 0 i

/-- Convert a point list of the right length into a `Fin`-indexed family. -/
def ptsToFin (k : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → Point :=
  fun i => pts.get ⟨i.val, by have hi : i.val < q k := i.is_lt; simp [hpts]⟩

/-- Radix used for chunked phase decomposition. -/
def phaseRadix (x : Reg) (k : ℕ) : ℚ := (2 : ℚ) ^ (regSize x / k)

/-- Radix determined directly by an operand width. -/
def phaseRadixWidth (w k : ℕ) : ℚ := (2 : ℚ) ^ (w / k)

/-- Radix for an already chosen chunk width. -/
def chunkRadix (W : ℕ) : ℚ := (2 : ℚ) ^ W

/-- Phase coefficients for a fixed chunk width. -/
noncomputable def phaseCoeffFromPtsWidth (k W : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  phaseCoeffFromPts k (ptsToFin k pts hpts) ((2 : ℚ) ^ W)

/--
Cramer's-rule reformulation of `phaseCoeffFromPts`.

`phaseCoeffFromPts` goes through `Matrix.inv`, which is noncomputable in
general (it case-splits on invertibility via `Ring.inverse`). `Matrix.cramer`
and `Matrix.det` need no such split — both reduce to a finite sum over
`Equiv.Perm (Fin (q k))` — so this definition is executable.
-/
def cramerCoeffFromPts (k : ℕ) (pts : Fin (q k) → Point) (b : ℚ) : Fin (q k) → ℚ :=
  let M : Matrix (Fin (q k)) (Fin (q k)) ℚ := interpMatrix k pts
  let radixVec : Fin (q k) → ℚ := fun j => b ^ (j : ℕ)
  fun i => Matrix.cramer M.transpose radixVec i / M.det

/-- `cramerCoeffFromPts` specialised to a fixed chunk width. -/
def cramerCoeffFromPtsWidth (k W : ℕ) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  cramerCoeffFromPts k (ptsToFin k pts hpts) ((2 : ℚ) ^ W)

/-- Phase coefficients selected from the common limb width of two operands. -/
noncomputable def phaseCoeffFromPtsForRegs (k : ℕ) (x z : ExtReg) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  phaseCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts

/-! =========================================================
    Canonical interpolation points
    The compiler uses its own `Point` type, while the algebraic Toom-Cook proof
    lives in `Toom_Cook_formula`. This section bridges the two representations.
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
