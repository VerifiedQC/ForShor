import Mathlib.Data.Int.Basic

/- Elementary integer implications only. The signed-power scale bounds,
   denominator clearing, table semantics, global induction and complexity
   theorem remain outside this file. -/
namespace Paper

theorem separated_cluster_cancellation (low high modulus : ℤ)
    (hzero : low + high = 0) (hhigh : modulus ∣ high)
    (hsmall : low.natAbs < modulus.natAbs) : low = 0 := by
  have hlow : modulus ∣ low := by
    have hmodzero : modulus ∣ (0 : ℤ) := ⟨0, by simp⟩
    have h := Int.dvd_sub hmodzero hhigh
    have heq : (0 : ℤ) - high = low := by omega
    simpa only [heq] using h
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hlow hsmall

theorem anchored_cluster_cancellation (low high total modulus : ℤ)
    (hsum : total = low + high) (htotal : modulus ∣ total)
    (hhigh : modulus ∣ high)
    (hsmall : low.natAbs < modulus.natAbs) : low = 0 := by
  have h := Int.dvd_sub htotal hhigh
  have heq : total - high = low := by omega
  have hlow : modulus ∣ low := by simpa only [heq] using h
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hlow hsmall

theorem relaxed_addition_dominates (u v upperU upperV shift upperNext : ℤ)
    (hu : u ≤ upperU) (hv : v ≤ upperV)
    (hleft : upperU + 1 ≤ upperNext)
    (hright : upperV + shift + 1 ≤ upperNext) :
    1 + max u (v + shift) ≤ upperNext := by omega

theorem exact_right_shift_dominates (u upper shift : ℤ)
    (hbound : u ≤ upper) (hlegal : shift ≤ u) :
    max 0 (u - shift) ≤ upper - shift := by omega

theorem normalized_negative_exponent_shift (u s g : ℤ)
    (hs : 0 ≤ s) (hg : 0 ≤ g) : u - s - g ≤ u := by omega

end Paper
