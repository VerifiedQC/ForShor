import Provider.Ceiling.SourceFixedWord

/-! # Dyadic Points
Defines `pointMagnitude` and the predicate `PointDyadic` on evaluation points. Proves that the literal F2 points are dyadic (`f2Point_dyadic`) and that the grouped points are dyadic (`groupedPoint_dyadic`), for arity `k` at least two.
-/

namespace Paper.F3ChargeCeiling

open Paper.F2CatalogTransfer TableGeneration.Operations

def pointMagnitude : Point → Int
  | .int z => z
  | .frac z => z

def PointDyadic (k : Nat) (p : Point) : Prop :=
  ∃ e, e ≤ k ∧ (pointMagnitude p = 0 ∨ (pointMagnitude p).natAbs = 2^e)

theorem f2Point_dyadic {k n : Nat} (hk : 2 ≤ k) (hn : n < 2*k-1) :
    PointDyadic k (f2Point n) := by
  by_cases hsmall : n < 4
  · interval_cases n <;> refine ⟨0, by omega, ?_⟩ <;> simp [pointMagnitude, f2Point]
  · let m := n - 4
    have hnm : n = m + 4 := by dsimp [m]; omega
    have he : 1 + m / 4 ≤ k := by dsimp [m]; omega
    rw [hnm]
    dsimp [f2Point]
    split <;> refine ⟨1 + m / 4, he, Or.inr ?_⟩ <;>
      simp [pointMagnitude, Int.natAbs_pow, Int.natAbs_neg]


theorem groupedPoint_dyadic {k : Nat} (hk : 2 ≤ k)
    {p : Point} (hp : p ∈ groupedF2Points k) : PointDyadic k p := by
  have hmem : p ∈ f2Points k := (groupedF2Points_perm k).mem_iff.mp hp
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hmem
  exact f2Point_dyadic hk (List.mem_range.mp hn)
end Paper.F3ChargeCeiling
