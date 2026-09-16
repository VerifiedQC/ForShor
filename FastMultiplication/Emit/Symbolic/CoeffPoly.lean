import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients

/-!
# E2: interpolation-weight polynomials

The leaf weights solve `M · c = (1, b, b², …)ᵀ` with `M_{j,l} = interpEntry k
pts[l] j` and `b = 2^m`, so `c_l(b) = Σ_j (M⁻¹)_{j,l} b^j` is a polynomial in
`b` determined by `k` and the point list alone.

`M⁻¹` is computed by exact Gauss-Jordan elimination over `ℚ`
(`gaussJordanInverseRows`), **not** via Mathlib's `Matrix.adjugate`/
`Matrix.det`: those are the Leibniz-formula/`Equiv.Perm`-sum definitions used
for *proofs*, not computation, and evaluating them is `O(n!)` **per entry**
(`Matrix.adjugate M i j` itself unfolds to one more `n!`-cost `Matrix.det`
call) — `O(n² · n!)` for a whole inverse this way, which is intractable
already at `k = 5` (`q 5 = 9`, `9! = 362880`, times `81` entries). Gauss-Jordan
is `O(n³)` and stays fast for any `k` this repository's tables reach.

Blocking checks (design principle 3): `check1_inverse` re-verifies
`M · M⁻¹ = I` exactly (also `O(n³)`, plain arithmetic, no `Matrix.det`).
`check2_agreesWithCramer` re-verifies that evaluating these polynomials at
`b = 2^m` agrees with the compiler's own `cramerCoeffFromPtsWidth` — that
function *is* one of the expensive `Matrix.det`/`Matrix.cramer` calls (it's
the pre-existing, unmodifiable ground truth this check is cross-verifying
against), so unlike the rest of this file it cannot be sped up, and the
caller (`Symbolic/Bundle.lean`) gates it tightly (small `k`, small `m`-range).
-/

namespace Shor

open Operations

/-- The `q k × q k` interpolation matrix for a concrete point list. -/
def coeffMatrix (k : ℕ) (pts : List Point) (hpts : pts.length = q k) :
    Matrix (Fin (q k)) (Fin (q k)) ℚ :=
  interpMatrix k (ptsToFin k pts hpts)

/-- Row-major dense form of an `n × n` `Matrix`, for the Gauss-Jordan
eliminator below. -/
def matrixToRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Array (Array ℚ) :=
  ((List.finRange n).map fun i => ((List.finRange n).map fun j => M i j).toArray).toArray

/-- Exact Gauss-Jordan elimination over `ℚ`: given the `n` rows of `M`,
returns the `n` rows of `M⁻¹`, or `none` if `M` is singular (shouldn't happen
here — `GoodToomCookPoints`/`interpMatrix`'s invertibility is what the
compiler's own `cramerCoeffFromPtsWidth` already relies on). `O(n³)`. -/
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

/-- Blocking check 1: `M · M⁻¹ = I` exactly, entrywise, `O(n³)`. -/
def check1_inverseOf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (inv : Array (Array ℚ)) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all fun j =>
      decide
        ((List.finRange n).foldl (fun acc r => acc + M i r * (inv.getD r.val #[]).getD j.val 0) 0
          = if i = j then (1 : ℚ) else 0)

/-- Blocking check 2: for `m = 1..mMax`, evaluating the polynomial at `2^m`
agrees with the compiler's own `cramerCoeffFromPtsWidth` at chunk width `m`,
for every row `l`. Each call to `cramerCoeffFromPtsWidth` is itself an
`O(n!)` `Matrix.det`/`Matrix.cramer` evaluation (it is the pre-existing
ground truth, not something this file can speed up) — the caller keeps `k`
and `mMax` small here. -/
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
