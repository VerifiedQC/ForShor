import ILPEncoding.Affine.Offsets

/-! # Cleared Costs
Defines the cost `Term D` with `localCost`, `clearedCost`, `totalCost` and `totalCleared` over a common denominator `D`. Proves `clear_one` and `clear_sum` and the budget equivalences `cleared_budget_iff` and `cleared_total_budget_iff`.
-/

namespace Paper.AffineCost

structure Term (D : ℤ) where
  P : ℤ
  N : ℤ
  c : ℤ
  x : ℤ
  hPx : P ∣ x
  hPD : P ∣ D
  hP : 0 < P

def localCost {D : ℤ} (s : Term D) : ℤ :=
  8 * s.N * s.c * (s.x / s.P - 1)

def clearedCost {D : ℤ} (s : Term D) : ℤ :=
  8 * s.N * s.c * ((D / s.P) * s.x - D)

theorem clear_one {D : ℤ} (s : Term D) :
    D * localCost s = clearedCost s := by
  obtain ⟨w, hw⟩ := s.hPx
  obtain ⟨m, hm⟩ := s.hPD
  have hP0 : s.P ≠ 0 := ne_of_gt s.hP
  simp only [localCost, clearedCost, hw, hm]
  rw [Int.mul_ediv_cancel_left _ hP0, Int.mul_ediv_cancel_left _ hP0]
  ring

def totalCost {D : ℤ} (terms : List (Term D)) : ℤ :=
  (terms.map localCost).sum

def totalCleared {D : ℤ} (terms : List (Term D)) : ℤ :=
  (terms.map clearedCost).sum

theorem clear_sum {D : ℤ} (terms : List (Term D)) :
    D * totalCost terms = totalCleared terms := by
  induction terms with
  | nil => simp [totalCost, totalCleared]
  | cons s rest ih =>
      have ih' : D * (rest.map localCost).sum =
          (rest.map clearedCost).sum := by
        simpa [totalCost, totalCleared] using ih
      simp [totalCost, totalCleared, List.map_cons, List.sum_cons,
        mul_add, clear_one s, ih']

theorem cleared_budget_iff (D cost target : ℤ) (hD : 0 < D) :
    D * cost ≤ D * target ↔ cost ≤ target := by
  constructor
  · intro h
    by_contra hn
    have hd : target + 1 ≤ cost := by omega
    have hm : 0 ≤ D * (cost - target - 1) :=
      mul_nonneg (le_of_lt hD) (by omega)
    nlinarith
  · intro h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hD)

theorem cleared_total_budget_iff {D : ℤ} (terms : List (Term D))
    (target : ℤ) (hD : 0 < D) :
    totalCleared terms ≤ D * target ↔ totalCost terms ≤ target := by
  rw [← clear_sum]
  exact cleared_budget_iff D _ _ hD

end Paper.AffineCost
