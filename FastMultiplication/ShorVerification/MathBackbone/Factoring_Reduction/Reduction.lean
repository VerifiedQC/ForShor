import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.MathBackbone.Factoring_Reduction.ProbabilityBound

open Classical

/- Helper Lemmas -/

/-- Show equivalence between two period definitions -/
lemma is_period_ord (a N : ℕ) (hgcd : Nat.gcd a N = 1) :
  is_period a (ord a N hgcd) N := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime a ((Nat.coprime_iff_gcd_eq_one).mpr hgcd)
  exact orderOf_injective (Units.coeHom (ZMod N)) Units.val_injective u

lemma factorization_identity {N : ℕ} (x : ZMod N) : x^2 - 1 = (x - 1) * (x + 1) := by ring

-- If r is even and a^r ≡ 1 (mod N), then (a^(r/2) - 1)(a^(r/2) + 1) ≡ 0 (mod N)
lemma shor_key_identity (a r N : ℕ)
(h : (a : ZMod N) ^ r = 1)
(h_even : Even r) :
let x := (a : ZMod N) ^ (r / 2)
x ^ 2 = 1 := by {
  ring_nf
  rw [Nat.div_mul_cancel (Even.two_dvd h_even), h]
}

-- Given that N divides the product (x - 1)(x + 1), and x is not congruent
-- to ±1 mod N, then one of the two GCDs will yield a non-trivial factor of N.
lemma gcd_nontrivial_from_product (x N : ℕ)
  (hx : 1 ≤ x)
  (h : N ∣ (x - 1) * (x + 1))
  (hN : N > 2)
  (h_not_one : (x : ZMod N) ≠ 1)
  (h_not_minus_one : (x : ZMod N) ≠ -1) :
  is_nontrivial_factor (Nat.gcd (x - 1) N) N ∨
  is_nontrivial_factor (Nat.gcd (x + 1) N) N := by {
  have h_N_ndvd_xm1 : ¬(N ∣ (x - 1)) := by
    intro h_dvd
    apply h_not_one
    have h0 := (zmod_eq_zero_iff_dvd (x - 1)).mpr h_dvd
    rw [Nat.cast_sub hx, sub_eq_zero] at h0
    exact_mod_cast h0
  have h_N_ndvd_xp1 : ¬(N ∣ (x + 1)) := by
    intro h_dvd
    apply h_not_minus_one
    have h0 := (zmod_eq_zero_iff_dvd (x + 1)).mpr h_dvd
    push_cast at h0
    calc (↑x : ZMod N) = ↑x + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h0]
      _ = -1 := by ring
  left
  refine ⟨?_, ?_, Nat.gcd_dvd_right _ _⟩
  · by_contra h_le
    push_neg at h_le
    have h_cop : Nat.gcd (x - 1) N = 1 := by
      have := Nat.gcd_pos_of_pos_right (x - 1) (show 0 < N by omega)
      omega
    exact h_N_ndvd_xp1 ((Nat.Coprime.symm h_cop).dvd_of_dvd_mul_left h)
  · exact lt_of_le_of_ne
      (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _))
      (fun h_eq => h_N_ndvd_xm1 (h_eq ▸ Nat.gcd_dvd_left _ _))
}

/- Classical Reduction Theorem: Factoring to Order Finding -/

/-- If we find the period r, and it meets the success conditions,
    then one of the two GCD equations will output a non-trivial factor of N. -/
theorem shors_classical_reduction (a r N : ℕ)
(h_N : N > 2)
(h_a : 1 < a ∧ a < N)
(h_coprime : Nat.gcd a N = 1)
(h_period : is_period a r N)
(h_success : shor_success_conditions a r N) :
is_nontrivial_factor (Nat.gcd ((a ^ (r / 2)) - 1) N) N ∨
is_nontrivial_factor (Nat.gcd ((a ^ (r / 2)) + 1) N) N := by {
  have h_even : Even r := h_success.1
  have h_not_minus_one : (a : ZMod N) ^ (r / 2) ≠ -1 := h_success.2
  have h_pow_r_eq_one : (a : ZMod N) ^ r = 1 := by {
    unfold is_period at h_period
    rw [← h_period]
    exact pow_orderOf_eq_one _
  }
  have h_sq_eq_one : ((a : ZMod N) ^ (r / 2)) ^ 2 = 1 :=
    shor_key_identity a r N h_pow_r_eq_one h_even

  have h_prod_eq_zero : ((a : ZMod N) ^ (r / 2) - 1) * ((a : ZMod N) ^ (r / 2) + 1) = 0 := by {
    rw [←factorization_identity]
    ring_nf
    rw [pow_mul, h_sq_eq_one]
    simp
  }

  have h_divides : N ∣ ((a ^ (r / 2) - 1) * (a ^ (r / 2) + 1)) := by {
    rw [← zmod_eq_zero_iff_dvd]
    have h1 : 1 ≤ a ^ (r / 2) := Nat.one_le_pow _ _ (by linarith [h_a.1])
    simp [Nat.cast_sub h1]
    exact h_prod_eq_zero
  }

  have h_not_one : (a : ZMod N) ^ (r / 2) ≠ 1 := by {
    unfold is_period at h_period
    intro h_eq_one
    have h_ord_dvd : r ∣ r / 2 := by
      nth_rw 1 [← h_period]
      exact orderOf_dvd_of_pow_eq_one h_eq_one
    have hr_pos : 0 < r := by
      haveI : NeZero N := ⟨by linarith⟩
      let u : (ZMod N)ˣ := ZMod.unitOfCoprime a h_coprime
      have horder : orderOf u = r := by
        have hinj := orderOf_injective (Units.coeHom (ZMod N)) Units.val_injective u
        rw [Units.coeHom_apply, ZMod.coe_unitOfCoprime, h_period] at hinj
        exact hinj.symm
      rw [← horder]
      exact orderOf_pos u
    have h_lt : r / 2 < r := Nat.div_lt_self hr_pos (by norm_num)
    have h_r_dvd_pos : 0 < r / 2 := by {
      obtain ⟨k, hk⟩ := h_even
      omega
    }
    exact absurd (Nat.le_of_dvd h_r_dvd_pos h_ord_dvd) (by omega)
  }

  have hx : 1 ≤ a ^ (r / 2) := Nat.one_le_pow _ _ (by linarith [h_a.1])

  have h_divides : N ∣ ((a ^ (r / 2) - 1) * (a ^ (r / 2) + 1)) := by {
    rw [← zmod_eq_zero_iff_dvd]
    simp [Nat.cast_sub hx]
    exact h_prod_eq_zero
  }

  have h_not_one_cast : ((a ^ (r / 2) : ℕ) : ZMod N) ≠ 1 := by {
    push_cast
    exact h_not_one
  }

  have h_not_minus_one_cast : ((a ^ (r / 2) : ℕ) : ZMod N) ≠ -1 := by {
    push_cast
    exact h_not_minus_one
  }

  exact gcd_nontrivial_from_product (a ^ (r / 2)) N hx h_divides h_N h_not_one_cast h_not_minus_one_cast
}
