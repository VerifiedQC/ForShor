import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic


noncomputable section

open scoped BigOperators
open Matrix

namespace ToomCookMath

universe u

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
  sorry

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

lemma phaseScalarFromList_eq_exp_sum
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
  sorry

theorem phaseScalarFromList_eq_exp_weightedPointSum
    {Point : Type u} {m : ℕ}
    (phi : ℝ)
    (coeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ)
    (pts : List Point)
    (hpts : pts.length = m) :
    phaseScalarFromList phi coeff pointTerm pts 0 (by simpa using hpts)
      =
    Complex.exp
      ((phi : ℂ) * Complex.I * weightedPointSum coeff pointTerm) := by
  classical
  sorry

theorem toomCook_phase_interpolation
    {Point : Type u} {m : ℕ}
    (row : Point → Fin m → ℚ)
    (pts : List Point)
    (hpts : pts.length = m)
    (B : ℚ)
    (phi : ℝ)
    (polyCoeff : Fin m → ℚ)
    (pointTerm : Fin m → ℚ)
    (target : ℚ)
    (hGood :
      GoodInterpolationPoints row (listToFin pts hpts))
    (hPointTerm :
      ∀ i : Fin m,
        pointTerm i =
          evalAtPoint m row polyCoeff ((listToFin pts hpts) i))
    (hTarget :
      target = evalAtRadix m polyCoeff B) :
    let coeff : Fin m → ℚ :=
      interpCoeff row (listToFin pts hpts) B
    phaseScalarFromList phi coeff pointTerm pts 0 (by simpa using hpts)
      =
    Complex.exp
      ((phi : ℂ) * Complex.I * ((target : ℚ) : ℂ)) := by
  classical
  intro coeff

  have hInterp :
      (∑ i : Fin m,
          coeff i *
            evalAtPoint m row polyCoeff ((listToFin pts hpts) i))
        =
      evalAtRadix m polyCoeff B := by
    simpa [coeff] using
      interpCoeff_correct
        (row := row)
        (pts := listToFin pts hpts)
        (B := B)
        (polyCoeff := polyCoeff)
        hGood

  have hWeighted :
    weightedPointSum coeff pointTerm =
      ((target : ℚ) : ℂ) := by
    have hRat :
        (∑ i : Fin m, coeff i * pointTerm i) = target := by
      calc
        (∑ i : Fin m, coeff i * pointTerm i)
            =
          (∑ i : Fin m,
              coeff i *
                evalAtPoint m row polyCoeff ((listToFin pts hpts) i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hPointTerm i]
        _ = evalAtRadix m polyCoeff B := hInterp
        _ = target := hTarget.symm
    simpa [weightedPointSum] using congrArg (fun q : ℚ => ((q : ℚ) : ℂ)) hRat

  calc
    phaseScalarFromList phi coeff pointTerm pts 0 (by simpa using hpts)
        =
      Complex.exp
        ((phi : ℂ) * Complex.I * weightedPointSum coeff pointTerm) := by
          exact phaseScalarFromList_eq_exp_weightedPointSum
            (phi := phi)
            (coeff := coeff)
            (pointTerm := pointTerm)
            (pts := pts)
            (hpts := hpts)
    _ =
      Complex.exp
        ((phi : ℂ) * Complex.I * ((target : ℚ) : ℂ)) := by
          rw [hWeighted]

end ToomCookMath
