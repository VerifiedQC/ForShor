import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

namespace Paper

theorem max_injection_lipschitz
    (x y u v M : Int)
    (hx : x ≤ u) (hy : y ≤ v)
    (hu : u ≤ x + M) (hv : v ≤ y + M) :
    max x y ≤ max u v ∧ max u v ≤ max x y + M := by
  omega

theorem signed_shift_preserves_interval
    (x u M shift : Int) (hx : x ≤ u) (hu : u ≤ x + M) :
    x + shift ≤ u + shift ∧ u + shift ≤ x + shift + M := by
  omega

theorem canonical_ray_saturation
    (a0 b0 a b d M cap : Int)
    (ha : a ≤ a0 + M) (hb : b ≤ b0 + M)
    (hcap : max a0 (b0 + d) + M ≤ cap) :
    a ≤ cap ∧ b ≤ cap - d := by
  omega

theorem signed_support_charge_corollary
    (k additions negatives negations : Int)
    (ha : 4 * k - 6 ≤ additions)
    (hn : 0 ≤ negatives) (hv : 0 ≤ negations)
    (hs : 1 ≤ negatives ∨ 2 ≤ negations) :
    4 * k - 4 ≤ additions + 2 * negatives + negations := by
  omega

end Paper
