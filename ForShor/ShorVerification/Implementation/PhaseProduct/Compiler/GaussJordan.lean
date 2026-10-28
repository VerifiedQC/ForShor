import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Phase-Product Compiler: exact Gauss-Jordan elimination, with a verified inverse

The compiler's interpolation weights are specified through `Matrix.cramer`
and `Matrix.det` (`Coefficients.lean`, `cramerCoeffFromPts`). Those are sums
over all permutations, so they serve as a specification, not as code. This
file is the computational counterpart, arranged so that nothing about the
algorithm has to be proved:

- `gaussJordanInverseRows` is an ordinary eliminator over `ℚ`. Nothing is
  proved about it; it may return anything.
- `isRightInverseRows M inv` re-multiplies and decides `M · inv = I`
  entrywise. That is the only computation that is trusted, and
  `mul_rowsToMatrix_eq_one_of_isRightInverseRows` turns a `true` into the
  proposition `M * rowsToMatrix inv = 1`.
- `Coefficients.lean` defines `gjCoeffFromPts` as "eliminate, verify, and
  fall back to Cramer if the verification fails", proves it equal to
  `cramerCoeffFromPts` (the verified branch through `Matrix.inv_eq_right_inv`,
  the fallbacks by `rfl`), and tags the equality `@[csimp]`.

`csimp` changes compiled code only: the kernel keeps seeing
`cramerCoeffFromPts`, so proofs are unaffected, while compiled code runs the
eliminator. It is the sound counterpart of `@[implemented_by]`, because it
demands the equality proof.

The file imports Mathlib and nothing from the project, so it sits at the
bottom of `Compiler/`: the `@[csimp]` lemma must be in the environment before
the definitions that call `cramerCoeffFromPts` are compiled.
-/

namespace Shor

open scoped BigOperators

/-- Row-major dense form of an `n × n` `Matrix`, for the eliminator below. -/
def matrixToRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Array (Array ℚ) :=
  ((List.finRange n).map fun i => ((List.finRange n).map fun j => M i j).toArray).toArray

/-- Row-major dense rows read back as a `Matrix`; a missing entry is `0`. The
inverse of `matrixToRows` on well-formed input, and the bridge that lets the
verified check below be stated as a `Matrix` equation. -/
def rowsToMatrix {n : ℕ} (rows : Array (Array ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (rows.getD i.val #[]).getD j.val 0

/-- Exact Gauss-Jordan elimination over `ℚ`: given the `n` rows of `M`,
returns the `n` rows of `M⁻¹`, or `none` if no pivot is found. Unverified;
its output is only used after `isRightInverseRows` has re-multiplied it. -/
def gaussJordanInverseRows (n : ℕ) (rows : Array (Array ℚ)) : Option (Array (Array ℚ)) :=
  Id.run do
    let mut aug : Array (Array ℚ) :=
      (Array.range n).map fun i =>
        (rows.getD i #[]) ++ (Array.range n).map (fun j => if i = j then (1 : ℚ) else 0)
    for col in [0:n] do
      let mut pivot : Option ℕ := none
      for r in [col:n] do
        if pivot.isNone then
          if (aug.getD r #[]).getD col 0 ≠ 0 then
            pivot := some r
      match pivot with
      | none => return none
      | some p =>
          if p ≠ col then
            let rowCol := aug.getD col #[]
            let rowP := aug.getD p #[]
            aug := aug.set! col rowP
            aug := aug.set! p rowCol
          let pv := (aug.getD col #[]).getD col 0
          aug := aug.set! col ((aug.getD col #[]).map (· / pv))
          for r in [0:n] do
            if r ≠ col then
              let factor := (aug.getD r #[]).getD col 0
              if factor ≠ 0 then
                let rowR := aug.getD r #[]
                let rowColNow := aug.getD col #[]
                aug := aug.set! r
                  ((Array.range (2 * n)).map fun c => rowR.getD c 0 - factor * rowColNow.getD c 0)
    return some ((Array.range n).map fun i => (aug.getD i #[]).extract n (2 * n))

/-- `M · rowsToMatrix inv = I`, decided entrywise over `ℚ`. This is the
trusted computation. -/
def isRightInverseRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (inv : Array (Array ℚ)) : Bool :=
  decide (∀ i j : Fin n,
    (∑ r : Fin n, M i r * rowsToMatrix (n := n) inv r j) = if i = j then (1 : ℚ) else 0)

/-- A `true` from `isRightInverseRows` is a right inverse, as a `Matrix`
equation. -/
theorem mul_rowsToMatrix_eq_one_of_isRightInverseRows
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {inv : Array (Array ℚ)}
    (h : isRightInverseRows M inv = true) :
    M * rowsToMatrix (n := n) inv = 1 := by
  have h' := of_decide_eq_true h
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  exact h' i j

end Shor
