import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace Paper

theorem compensated_crossing_arithmetic (x y z a b : Int) :
    x + a * (y + b * z) - (a * b) * z = x + a * y := by
  ring

theorem compensated_crossing_scanner
    (x y z p q prior : Nat) :
    let afterJ := 1 + max y (z + q)
    let oldI1 := 1 + max x (afterJ + p)
    let oldI2 := 1 + max oldI1 (z + (p + q))
    let newI := 1 + max x (y + p)
    newI ≤ oldI2 ∧ max prior (max newI afterJ) ≤ max prior (max oldI2 afterJ) := by
  dsimp
  constructor <;> omega

theorem reverse_shortcut_width_counterexample :
    (1 + max (1 + max (0 : Nat) 0) 2 = 3) ∧
    (1 + max (0 : Nat) (1 + max 0 2) = 4) := by
  decide

end Paper
