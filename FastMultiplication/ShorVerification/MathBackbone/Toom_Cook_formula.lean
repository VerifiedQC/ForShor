import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic


noncomputable section

open scoped BigOperators
open Matrix

namespace ToomCookMath

universe u

/-!
# Toom-Cook interpolation formula

This file develops the pure interpolation algebra used by the phase-product
compiler: interpolation points, Vandermonde-style invertibility, reconstruction
at a radix, and the exponential phase scalars obtained from weighted point
sums.
-/

/-! =========================================================
    Section 1: Points, rows, and interpolation matrices
========================================================= -/

inductive Point where
  | int : ℤ → Point
  | inf : Point
deriving DecidableEq, Repr

def pointRow (m : ℕ) (p : Point) (j : Fin m) : ℚ :=
  match p with
  | Point.int z => (z : ℚ) ^ (j : ℕ)
  | Point.inf   => if (j : ℕ) = m - 1 then 1 else 0

def pointCoordQ : Point → ℚ
  | Point.int z => (z : ℚ)
  | Point.inf   => 0

/-- Convert a list of length `m` into a `Fin m`-indexed function. -/
def listToFin {α : Type u} {m : ℕ}
    (pts : List α)
    (hpts : pts.length = m) :
    Fin m → α :=
  fun i =>
    pts.get ⟨i.1, by
      simp [hpts]
    ⟩

def interpMatrix {Point : Type u} {m : ℕ}
    (row : Point → Fin m → ℚ)
    (pts : Fin m → Point) :
    Matrix (Fin m) (Fin m) ℚ :=
  fun i j => row (pts i) j

/-- Row `[1, B, B^2, ...]`, used for evaluation at radix `B`. -/
def radixRow (m : ℕ) (B : ℚ) :
    Matrix (Fin 1) (Fin m) ℚ :=
  fun _ j => B ^ (j : ℕ)

def GoodInterpolationPoints {Point : Type u} {m : ℕ}
    (row : Point → Fin m → ℚ)
    (pts : Fin m → Point) : Prop :=
  Matrix.det (interpMatrix row pts) ≠ 0

/-! =========================================================
    Section 2: Invertibility and interpolation correctness
========================================================= -/

/--
Pure mathematical Vandermonde fact.

If the coordinates of the selected points are pairwise distinct, then the
monomial interpolation matrix is invertible.
-/
lemma GoodInterpolationPoints.of_vandermonde_distinct
    {α : Type u}
    {n : ℕ}
    (coord : α → ℚ)
    (pts : Fin n → α)
    (hinj : Function.Injective (fun i : Fin n => coord (pts i))) :
    GoodInterpolationPoints
      (row := fun p j => coord p ^ (j : ℕ))
      (pts := pts) := by
  classical
  unfold GoodInterpolationPoints interpMatrix
  let v : Fin n → ℚ := fun i => coord (pts i)
  change (Matrix.vandermonde v).det ≠ 0
  exact (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hinj

lemma GoodInterpolationPoints.congr_matrix
    {α β : Type u}
    {m : ℕ}
    {rowA : α → Fin m → ℚ}
    {rowB : β → Fin m → ℚ}
    {ptsA : Fin m → α}
    {ptsB : Fin m → β}
    (hentry : ∀ i j, rowA (ptsA i) j = rowB (ptsB i) j)
    (hgood : GoodInterpolationPoints rowA ptsA) :
    GoodInterpolationPoints rowB ptsB := by
  unfold GoodInterpolationPoints interpMatrix at *
  have hM :
      (fun i j => rowA (ptsA i) j)
        =
      (fun i j => rowB (ptsB i) j) := by
    funext i j
    exact hentry i j
  simpa [hM] using hgood

noncomputable def interpCoeff {Point : Type u} {m : ℕ}
    (row : Point → Fin m → ℚ)
    (pts : Fin m → Point)
    (B : ℚ) :
    Fin m → ℚ :=
  let M : Matrix (Fin m) (Fin m) ℚ := interpMatrix row pts
  let v : Matrix (Fin 1) (Fin m) ℚ := radixRow m B * M⁻¹
  fun i => v 0 i

/-- Evaluate a coefficient vector using the abstract point-row function. -/
def evalAtPoint {Point : Type u} (m : ℕ)
    (row : Point → Fin m → ℚ)
    (polyCoeff : Fin m → ℚ)
    (pt : Point) : ℚ :=
  ∑ j : Fin m, polyCoeff j * row pt j

/-- Evaluate a coefficient vector at radix `B`. -/
def evalAtRadix (m : ℕ)
    (polyCoeff : Fin m → ℚ)
    (B : ℚ) : ℚ :=
  ∑ j : Fin m, polyCoeff j * B ^ (j : ℕ)

theorem interpCoeff_correct {Point : Type u} {m : ℕ}
    (row : Point → Fin m → ℚ)
    (pts : Fin m → Point)
    (B : ℚ)
    (polyCoeff : Fin m → ℚ)
    (hGood : GoodInterpolationPoints row pts) :
    (∑ i : Fin m,
        interpCoeff row pts B i *
          evalAtPoint m row polyCoeff (pts i))
      =
    evalAtRadix m polyCoeff B := by
  classical

  let M : Matrix (Fin m) (Fin m) ℚ :=
    interpMatrix row pts

  let c : Matrix (Fin m) (Fin 1) ℚ :=
    fun j _ => polyCoeff j

  have hUnit : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    simpa [M, GoodInterpolationPoints] using hGood

  have hInv : M⁻¹ * M = 1 := by
    simpa using Matrix.nonsing_inv_mul M hUnit

  have hLeft :
      (∑ i : Fin m,
          interpCoeff row pts B i *
            evalAtPoint m row polyCoeff (pts i))
        =
      (((radixRow m B * M⁻¹) * (M * c)) 0 0) := by
    simp [interpCoeff, evalAtPoint, M, c, Matrix.mul_apply,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    refine Finset.sum_congr rfl ?_
    intro x hx
    refine Finset.sum_congr rfl ?_
    intro x_1 hx_1
    refine Finset.sum_congr rfl ?_
    intro x_2 hx_2
    simp [interpMatrix]
    ring

  have hRight :
      evalAtRadix m polyCoeff B
        =
      (radixRow m B * c) 0 0 := by
    simp [evalAtRadix, radixRow, c, Matrix.mul_apply, mul_comm]

  have hMat :
      radixRow m B * M⁻¹ * (M * c)
        =
      radixRow m B * c := by
    calc
      radixRow m B * M⁻¹ * (M * c)
          =
        radixRow m B * (M⁻¹ * (M * c)) := by
          rw [Matrix.mul_assoc]
      _ =
        radixRow m B * ((M⁻¹ * M) * c) := by
          rw [← Matrix.mul_assoc]
          rw [Matrix.mul_assoc]
          congr 1
          rw [← Matrix.mul_assoc]

      _ =
        radixRow m B * (((1 : Matrix (Fin m) (Fin m) ℚ) * c)) := by
          rw [hInv]
      _ =
        radixRow m B * c := by
          simp

  calc
    (∑ i : Fin m,
        interpCoeff row pts B i *
          evalAtPoint m row polyCoeff (pts i))
        =
      (((radixRow m B * M⁻¹) * (M * c)) 0 0) := hLeft
    _ =
      (radixRow m B * c) 0 0 := by
        rw [hMat]
    _ =
      evalAtRadix m polyCoeff B := hRight.symm

/-! =========================================================
    Section 3: Phase scalar products
========================================================= -/

/-- Weighted sum appearing in the exponent. -/
def weightedPointSum {m : ℕ}
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ) : ℂ :=
  ∑ i : Fin m,
    ((coeff i : ℚ) : ℂ) * ((pointTerm i : ℚ) : ℂ)

/-- One exponential phase factor. -/
def phaseFactor
    (phi : ℝ)
    (coeff : ℚ)
    (term : ℚ) : ℂ :=
  Complex.exp
    ((((phi * (coeff : ℝ)) : ℝ) : ℂ) *
      Complex.I *
      ((term : ℚ) : ℂ))


noncomputable def phaseScalarFromList {Point : Type u} {m : ℕ}
    (phi : ℝ)
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ) :
    (pts : List Point) → (n : ℕ) → n + pts.length = m → ℂ
  | [], _n, _hn => 1
  | _pt :: rest, n, hn =>
      let i : Fin m := ⟨n, by simp at hn;omega⟩
      let hn' : n + 1 + rest.length = m := by simp at hn;omega
      phaseFactor phi (coeff i) (pointTerm i) *
        phaseScalarFromList phi coeff pointTerm rest (n + 1) hn'

/-! =========================================================
    Section 4: Canonical finite interpolation points
========================================================= -/

/-- Integer coordinate used by the canonical alternating point sequence. -/
def alternatingInt (i : ℕ) : ℤ :=
  if i % 2 == 0 then
    (i / 2 : ℤ)
  else
    -((i + 1) / 2 : ℤ)

/-- Pure canonical point sequence: `0, -1, 1, -2, 2, ...`. -/
def alternatingPoint (i : ℕ) : Point :=
  Point.int (alternatingInt i)

/-- First `m` canonical finite interpolation points. -/
def genFiniteInterpolationPoints (m : ℕ) : List Point :=
  (List.range m).map alternatingPoint

lemma pointCoordQ_alternatingPoint (i : ℕ) :
    pointCoordQ (alternatingPoint i) = (alternatingInt i : ℚ) := by
  simp [alternatingPoint, pointCoordQ]

lemma nat_mod_two_eq_one_of_ne_zero {n : ℕ} (h : n % 2 ≠ 0) :
    n % 2 = 1 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < 2)
  omega

lemma alternatingInt_injective :
    Function.Injective alternatingInt := by
  intro i j h

  by_cases hi : i % 2 = 0
  · by_cases hj : j % 2 = 0
    · -- even/even
      simp [alternatingInt, hi, hj] at h

      have hdiv : i / 2 = j / 2 := by
        exact_mod_cast h

      have hi_rec := Nat.mod_add_div i 2
      have hj_rec := Nat.mod_add_div j 2
      omega

    · -- even/odd: nonnegative equals negative, contradiction
      simp [alternatingInt, hi, hj] at h

      have hj1 : j % 2 = 1 :=
        nat_mod_two_eq_one_of_ne_zero hj

      have hj_ge : 2 ≤ j + 1 := by
        omega

      have hjpos_nat : 0 < (j + 1) / 2 :=
        Nat.div_pos hj_ge (by decide : 0 < 2)

      have hnonneg : (0 : ℤ) ≤ ((i / 2 : ℕ) : ℤ) := by
        exact_mod_cast Nat.zero_le (i / 2)

      have hneg : -(((j + 1) / 2 : ℕ) : ℤ) < 0 := by
        have hpos : (0 : ℤ) < (((j + 1) / 2 : ℕ) : ℤ) := by
          exact_mod_cast hjpos_nat
        linarith

      exfalso
      simp_all
      omega

  · by_cases hj : j % 2 = 0
    · -- odd/even: negative equals nonnegative, contradiction
      simp [alternatingInt, hi, hj] at h

      have hi1 : i % 2 = 1 :=
        nat_mod_two_eq_one_of_ne_zero hi

      have hi_ge : 2 ≤ i + 1 := by
        omega

      have hipos_nat : 0 < (i + 1) / 2 :=
        Nat.div_pos hi_ge (by decide : 0 < 2)

      have hneg : -(((i + 1) / 2 : ℕ) : ℤ) < 0 := by
        have hpos : (0 : ℤ) < (((i + 1) / 2 : ℕ) : ℤ) := by
          exact_mod_cast hipos_nat
        linarith

      have hnonneg : (0 : ℤ) ≤ ((j / 2 : ℕ) : ℤ) := by
        exact_mod_cast Nat.zero_le (j / 2)

      exfalso
      simp_all
      omega

    · -- odd/odd
      simp [alternatingInt, hi, hj] at h

      have hcast :
          (((i + 1) / 2 : ℕ) : ℤ)
            =
          (((j + 1) / 2 : ℕ) : ℤ) := by
        simp_all

      have hdiv : (i + 1) / 2 = (j + 1) / 2 := by
        exact_mod_cast hcast

      have hi1 : i % 2 = 1 :=
        nat_mod_two_eq_one_of_ne_zero hi

      have hj1 : j % 2 = 1 :=
        nat_mod_two_eq_one_of_ne_zero hj

      have hisucc_mod : (i + 1) % 2 = 0 := by
        omega

      have hjsucc_mod : (j + 1) % 2 = 0 := by
        omega

      have hi_rec := Nat.mod_add_div (i + 1) 2
      have hj_rec := Nat.mod_add_div (j + 1) 2
      omega

lemma genFiniteInterpolationPoints_coord_injective
    (m : ℕ)
    (hpts : (genFiniteInterpolationPoints m).length = m) :
    Function.Injective
      (fun i : Fin m =>
        pointCoordQ ((listToFin (genFiniteInterpolationPoints m) hpts) i)) := by
  classical
  intro i j hij
  apply Fin.ext
  apply alternatingInt_injective

  have hij' :
      (alternatingInt i.1 : ℚ) = (alternatingInt j.1 : ℚ) := by
    simpa [listToFin, genFiniteInterpolationPoints,
      pointCoordQ_alternatingPoint] using hij

  exact_mod_cast hij'

/--
The generated pure finite points are good interpolation points.
-/
lemma genFiniteInterpolationPoints_good
    (m : ℕ)
    (hpts : (genFiniteInterpolationPoints m).length = m) :
    GoodInterpolationPoints
      (row := pointRow m)
      (pts := listToFin (genFiniteInterpolationPoints m) hpts) := by
  classical

  let ptsFin : Fin m → Point :=
    listToFin (genFiniteInterpolationPoints m) hpts

  have hCoordGood :
      GoodInterpolationPoints
        (row := fun p j => pointCoordQ p ^ (j : ℕ))
        (pts := ptsFin) := by
    exact
      GoodInterpolationPoints.of_vandermonde_distinct
        pointCoordQ
        ptsFin
        (genFiniteInterpolationPoints_coord_injective m hpts)

  apply GoodInterpolationPoints.congr_matrix
    (rowA := fun p j => pointCoordQ p ^ (j : ℕ))
    (rowB := pointRow m)
    (ptsA := ptsFin)
    (ptsB := ptsFin)
  · intro i j
    dsimp [ptsFin]
    simp [listToFin, genFiniteInterpolationPoints,
      pointRow, pointCoordQ, alternatingPoint]
  · exact hCoordGood

/-! =========================================================
    Section 5: Tail-weighted sums and phase scalar identities
========================================================= -/

def tailWeightedPointSum {m : ℕ}
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ)
    (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ i.1),
    ((coeff i : ℚ) : ℂ) * ((pointTerm i : ℚ) : ℂ)

lemma tailWeightedPointSum_eq_zero_of_le
    {m n : ℕ}
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ)
    (hmn : m ≤ n) :
    tailWeightedPointSum coeff pointTerm n = 0 := by
  classical
  unfold tailWeightedPointSum
  apply Finset.sum_eq_zero
  intro i hi
  have hnle : n ≤ i.1 := by
    exact (Finset.mem_filter.mp hi).2
  have him : i.1 < m := i.2
  exfalso
  omega

lemma tailWeightedPointSum_eq_cons
    {m n : ℕ}
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ)
    (hn : n < m) :
    tailWeightedPointSum coeff pointTerm n
      =
    ((coeff ⟨n, hn⟩ : ℚ) : ℂ) *
      ((pointTerm ⟨n, hn⟩ : ℚ) : ℂ)
      +
    tailWeightedPointSum coeff pointTerm (n + 1) := by

  let i0 : Fin m := ⟨n, hn⟩

  have hset :
      Finset.univ.filter (fun i : Fin m => n ≤ i.1)
        =
      insert i0 (Finset.univ.filter (fun i : Fin m => n + 1 ≤ i.1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hni
      by_cases hi : i = i0
      · exact Or.inl hi
      · right
        have hne : i.1 ≠ n := by
          intro hv
          apply hi
          exact Fin.ext hv
        omega
    · intro h
      rcases h with h | h
      · rw [h]
      · omega

  unfold tailWeightedPointSum
  rw [hset]
  rw [Finset.sum_insert]
  simp_all
  rfl

theorem phaseScalarFromList_eq_exp_tailWeightedPointSum
    {α : Type u} {m : ℕ}
    (phi : ℝ)
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ) :
    ∀ (pts : List α) (n : ℕ) (hn : n + pts.length = m),
      phaseScalarFromList phi coeff pointTerm pts n hn
        =
      Complex.exp
        ((phi : ℂ) * Complex.I *
          tailWeightedPointSum coeff pointTerm n) := by
  classical
  intro pts
  induction pts with
  | nil =>
      intro n hn
      have hmn : m ≤ n := by
        simp at hn
        omega
      have htail :
          tailWeightedPointSum coeff pointTerm n = 0 :=
        tailWeightedPointSum_eq_zero_of_le coeff pointTerm hmn
      simp [phaseScalarFromList, htail]

  | cons pt rest ih =>
      intro n hn

      have hnlt : n < m := by
        simp at hn
        omega

      have hnrest : n + 1 + rest.length = m := by
        simp at hn ⊢
        omega

      simp [phaseScalarFromList]

      rw [ih (n + 1) hnrest]
      rw [tailWeightedPointSum_eq_cons coeff pointTerm hnlt]
      rw [phaseFactor]
      rw [← Complex.exp_add]
      congr 1
      simp

      have hidx :
          (⟨n, by
            simp at hn
            omega
          ⟩ : Fin m) = ⟨n, hnlt⟩ := by
        ext
        rfl

      rw [hidx]
      ring_nf


theorem phaseScalarFromList_eq_exp_weightedPointSum
    {α : Type u} {m : ℕ}
    (phi : ℝ)
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ)
    (pts : List α)
    (hpts : pts.length = m) :
    phaseScalarFromList phi coeff pointTerm pts 0 (by simpa using hpts)
      =
    Complex.exp
      ((phi : ℂ) * Complex.I * weightedPointSum coeff pointTerm) := by
  classical
  have h :=
    phaseScalarFromList_eq_exp_tailWeightedPointSum
      (α := α)
      (m := m)
      phi coeff pointTerm pts 0
      (by simpa using hpts)

  simpa [tailWeightedPointSum, weightedPointSum] using h

lemma phaseScalarFromList_eq_exp_sum
  {Point : Type u}
  {k : ℕ}
  (phi : ℝ)
  (coeff terms : Fin (2*k-1) → ℚ)
  (pts : List Point)
  (hpts : pts.length = (2*k-1)) :
  ToomCookMath.phaseScalarFromList phi coeff terms pts 0 (by simpa using hpts)
    =
  Complex.exp
    (phi * Complex.I *
      (((∑ i : Fin (2*k-1), coeff i * terms i : ℚ) : ℂ))) := by
  simpa [ToomCookMath.weightedPointSum, mul_assoc, mul_left_comm, mul_comm] using
    (ToomCookMath.phaseScalarFromList_eq_exp_weightedPointSum
      (α := Point)
      (m := 2*k-1)
      (phi := phi)
      (coeff := coeff)
      (pointTerm := terms)
      (pts := pts)
      (hpts := hpts))

end ToomCookMath
