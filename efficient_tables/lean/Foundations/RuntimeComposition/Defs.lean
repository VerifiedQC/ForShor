import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sigma

namespace RuntimeComposition

/-- Bit length `bl x = ⌊log₂ x⌋ + 1`. -/
def bl (x : ℕ) : ℕ := Nat.log 2 x + 1

/-- `S k = (6k²+1) · (6k²)! · (8k²)^(6k²)`. -/
def S (k : ℕ) : ℕ := (6 * k ^ 2 + 1) * (6 * k ^ 2).factorial * (8 * k ^ 2) ^ (6 * k ^ 2)

/-- Triples `(k,d,C)` with `2 ≤ k ≤ K`, `d < k`, `C ≤ 27 k³`. -/
def tripleSet (K : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 2 K).sigma (fun k => Finset.range k ×ˢ Finset.range (27 * k ^ 3 + 1))
    |>.image (fun x => (x.1, x.2.1, x.2.2))

/-- Sum of the local counts `Loc k d C` over `tripleSet K`. -/
def localTotal (Loc : ℕ → ℕ → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ t ∈ tripleSet K, Loc t.1 t.2.1 t.2.2

end RuntimeComposition
