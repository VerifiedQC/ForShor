import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients

/-!
# E2: interpolation-weight polynomials

The leaf weights solve `M · c = (1, b, b², …)ᵀ` with `M_{j,l} = interpEntry k
pts[l] j` and `b = 2^m`, so `c_l(b) = Σ_j (M⁻¹)_{j,l} b^j` is a polynomial in
`b` determined by `k` and the point list alone.

`M⁻¹` is computed by exact Gauss-Jordan elimination over `ℚ`
(`gaussJordanInverseRows`, from `Compiler/GaussJordan.lean`), **not** via Mathlib's `Matrix.adjugate`/
`Matrix.det`: those are the Leibniz-formula/`Equiv.Perm`-sum definitions used
for *proofs*, not computation, and evaluating them is `O(n!)` **per entry**
(`Matrix.adjugate M i j` itself unfolds to one more `n!`-cost `Matrix.det`
call) — `O(n² · n!)` for a whole inverse this way, which is intractable
already at `k = 5` (`q 5 = 9`, `9! = 362880`, times `81` entries). Gauss-Jordan
is `O(n³)` and stays fast for any `k` this repository's tables reach.

Blocking checks (design principle 3): `check1_inverse` re-verifies
`M · M⁻¹ = I` exactly (also `O(n³)`, plain arithmetic, no `Matrix.det`).
`check2_agreesWithCramer` re-verifies that evaluating these polynomials at
`b = 2^m` agrees with the compiler's own `cramerCoeffFromPtsWidth`: that the
polynomial read off `M⁻¹` and the compiler's pointwise weights are the same
numbers.
-/

namespace Shor

open Operations

/-- The `q k × q k` interpolation matrix for a concrete point list. -/
def coeffMatrix (k : ℕ) (pts : List Point) (hpts : pts.length = q k) :
    Matrix (Fin (q k)) (Fin (q k)) ℚ :=
  interpMatrix k (ptsToFin k pts hpts)

/-- `M⁻¹`, computed once via Gauss-Jordan. `none` if singular. -/
def coeffInverse (k : ℕ) (pts : List Point) (hpts : pts.length = q k) :
    Option (Array (Array ℚ)) :=
  gaussJordanInverseRows (q k) (matrixToRows (coeffMatrix k pts hpts))

/-- Row `l`'s coefficient-of-`bʲ` vector, reading off a precomputed `M⁻¹`
(from `coeffInverse`): `c_l(b) = Σ_j coeffPolyRowOf inv l j * b ^ j`, where
`coeffPolyRowOf inv l j = (M⁻¹) j l`. -/
def coeffPolyRowOf {n : ℕ} (inv : Array (Array ℚ)) (l : Fin n) : Fin n → ℚ :=
  fun j => (inv.getD j.val #[]).getD l.val 0

/-- Evaluate a coefficient-of-`bʲ` vector at a concrete `b`. -/
def polyEval {n : ℕ} (c : Fin n → ℚ) (b : ℚ) : ℚ :=
  ∑ j, c j * b ^ (j : ℕ)

/-- Blocking check 1: `M · M⁻¹ = I` exactly, entrywise — the compiler's
`isRightInverseRows`. -/
abbrev check1_inverseOf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (inv : Array (Array ℚ)) : Bool :=
  isRightInverseRows M inv

/-- Blocking check 2: for `m = 1..mMax`, evaluating the polynomial at `2^m`
agrees with the compiler's own `cramerCoeffFromPtsWidth` at chunk width `m`,
for every row `l`. It checks `coeffPolyRowOf`/`polyEval`, the polynomial
form, against the compiler's pointwise weights. -/
def check2_agreesWithCramer
    (inv : Array (Array ℚ)) (k : ℕ) (pts : List Point) (hpts : pts.length = q k) (mMax : ℕ) :
    Bool :=
  (List.range mMax).all fun m' =>
    let m := m' + 1
    (List.finRange (q k)).all fun l =>
      decide (polyEval (coeffPolyRowOf inv l) ((2 : ℚ) ^ m) = cramerCoeffFromPtsWidth k m pts hpts l)

/-- Points pairwise distinct, by their coordinate in `ToomCookMath`'s sense
(`int z ↦ z`, `frac c ↦ 1/c`). -/
def pointsDistinct (pts : List Point) : Bool :=
  decide (pts.map (fun p => ToomCookMath.pointCoordQ (toMathPoint p))).Nodup

/-- Every `m ≤ mMax` at which `2^m` coincides with one of the (integer)
points — there the weight vector is a selector and any downstream
differential is vacuous. Advisory only. -/
def degenerateMs (pts : List Point) (mMax : ℕ) : List ℕ :=
  (List.range (mMax + 1)).filter fun m =>
    pts.any fun p =>
      match p with
      | .int z => decide (z = (2 : ℤ) ^ m)
      | .frac _ => false

end Shor
