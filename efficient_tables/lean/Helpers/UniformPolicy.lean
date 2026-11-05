import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

namespace Paper

theorem oversized_arity_cannot_contract
    (w k a b : Nat) (hkw : w < k) :
    w < w / k + 1 + max a (w % k + b) := by
  rw [Nat.div_eq_of_lt hkw, Nat.mod_eq_of_lt hkw]
  omega

theorem used_cap_inside_root
    (a b r q W w n : Nat)
    (hW : W = q + 1 + max a (r + b))
    (hc : W < w) (hn : w ≤ n) : a ≤ n - 2 := by
  omega

theorem restoration_extra_bit
    (marked current next peak exponent negations : Nat)
    (hcurrent : current = marked + exponent + negations)
    (hnext : current + 1 ≤ next) (hpeak : next ≤ peak) :
    marked + 1 ≤ peak := by
  omega

theorem charge_floor_from_projective_count
    (k additions negatives negations : Nat) (hk : 1 ≤ k)
    (hadds : 2 * k - 2 ≤ additions)
    (hsign : 1 ≤ negatives ∨ 2 ≤ negations) :
    2 * k ≤ additions + 2 * negatives + negations := by
  omega

theorem matching_bounds_certify
    (lower optimum incumbent : Nat)
    (hl : lower ≤ optimum) (hu : optimum ≤ incumbent)
    (heq : lower = incumbent) : optimum = incumbent := by
  omega

end Paper
