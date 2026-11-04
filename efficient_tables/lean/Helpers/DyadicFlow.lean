import Mathlib.Tactic

namespace Paper

theorem maxplus_add_preserves_join (ad bd ah bh e : ℤ) :
    1 + max (max ad bd) (max ah bh + e) =
      max (1 + max ad (ah + e)) (1 + max bd (bh + e)) := by
  omega

theorem translation_preserves_join (a b c : ℤ) :
    max a b + c = max (a + c) (b + c) := by
  omega

theorem join_cap_iff (a b cap : ℤ) :
    max a b ≤ cap ↔ a ≤ cap ∧ b ≤ cap := by
  omega

theorem parity_quotas_unique (even odd count diff : ℤ)
    (hc : even + odd = count) (hd : even - odd = diff) :
    2 * even = count + diff ∧ 2 * odd = count - diff := by
  omega

end Paper
