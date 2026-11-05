import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic

namespace SmallPoint

open Matrix

/-- Cone K = {x : G x ≤ 0}. -/
def coneK {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ) : Set (Fin n → ℝ) :=
  {x | ∀ i, (G.map (Int.cast : ℤ → ℝ) *ᵥ x) i ≤ 0}

/-- Rows tight at w. -/
def tightRows {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ) (w : Fin n → ℝ) : Set (Fin m) :=
  {i | (G.map (Int.cast : ℤ → ℝ) *ᵥ w) i = 0}

/-- Rank of the submatrix of G on tight rows at w. -/
noncomputable def tightRank {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ) (w : Fin n → ℝ) : ℕ :=
  Matrix.rank ((G.map (Int.cast : ℤ → ℝ)).submatrix ((↑) : tightRows G w → Fin m) id)

/-- Generator of an extreme ray of a cone K. -/
def IsExtremeRayOfCone {n : ℕ} (K : Set (Fin n → ℝ)) (v : Fin n → ℝ) : Prop :=
  v ∈ K ∧ v ≠ 0 ∧ ∀ x ∈ K, ∀ y ∈ K, x + y = v →
    (∃ a : ℝ, 0 ≤ a ∧ x = a • v) ∧ (∃ b : ℝ, 0 ≤ b ∧ y = b • v)

/-- Extreme vector: w ∈ K, w ≠ 0, tight rank n-1. -/
def IsExtremeVector {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℤ) (w : Fin n → ℝ) : Prop :=
  w ∈ coneK G ∧ w ≠ 0 ∧ tightRank G w = n - 1

/-- P = {x ≥ 0, A x ≤ b}. -/
def polyhedronInt {s t : ℕ} (A : Matrix (Fin s) (Fin t) ℤ) (b : Fin s → ℤ) : Set (Fin t → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∀ i, (A.map (Int.cast : ℤ → ℝ) *ᵥ x) i ≤ (b i : ℝ)}

/-- P has an integer point. -/
def HasIntegerPoint {s t : ℕ} (A : Matrix (Fin s) (Fin t) ℤ) (b : Fin s → ℤ) : Prop :=
  ∃ y : Fin t → ℤ, (fun j => (y j : ℝ)) ∈ polyhedronInt A b

end SmallPoint
