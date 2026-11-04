import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace Paper

-- An invertible remaining-row update cannot erase a nonzero excluded column.
-- The combinatorial application establishing the map is not formalized here.
theorem injective_restoration_column_zero
    {V W : Type*} [Zero V] [Zero W]
    (f : V → W) (hinj : Function.Injective f) (hzero : f 0 = 0)
    (x : V) (hx : f x = 0) : x = 0 := by
  apply hinj
  exact hx.trans hzero.symm

-- Exact upper/lower separation excludes a candidate family.
theorem strict_incumbent_excludes_family
    (optimum upper familyLower candidate : Int)
    (hopt : optimum ≤ upper) (hgap : upper < familyLower)
    (hfamily : familyLower ≤ candidate) : optimum < candidate := by
  omega

-- Identical-profile replacement preserves weights and saves positive cost.
theorem positive_shared_table_saving
    (oldCharge newCharge totalWeight : Int)
    (hc : newCharge < oldCharge) (hw : 0 < totalWeight) :
    0 < 8 * (oldCharge - newCharge) * totalWeight := by
  have hdiff : 0 < oldCharge - newCharge := by omega
  exact Int.mul_pos (Int.mul_pos (by omega) hdiff) hw

-- Constants only; the optimization/legality premises are separately reviewed.
theorem certified_n79_gap :
    (327272 : Int) < 345851 ∧ (345851 : Int) < 356352 := by
  omega

end Paper
