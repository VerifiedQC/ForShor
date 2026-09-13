import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates

/-!
# `qftPhase` facts

Pure facts about `qftPhase`/`ωPow` (`Framework/AbstractMachine/Gates.lean`): the
grid-exponential form of `qftPhase`, its conjugate, periodicity of `ω r` and of
`qftPhase` in its first numeric argument mod `r`, and its unit norm. Used by
`Shor/Proofs/NaiveShor/Lemmas.lean` and `ModularExponentiation/Proofs/CmpLtNW.lean`.
-/

namespace Shor

lemma qftPhase_eq_exp_grid_shor (M z t : ℕ) :
    qftPhase M z t = Complex.exp (((2 * Real.pi) / (M : ℝ)) * Complex.I * ((z : ℂ) * (t : ℂ))) := by
  simp [qftPhase, ωPow, ω, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma star_qftPhase_eq_negative_grid_phase_shor (M z t : ℕ) :
    star (qftPhase M z t)
      = Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((z : ℂ) * (t : ℂ)) / (M : ℂ)))) := by
  rw [qftPhase_eq_exp_grid_shor]
  simp
  rw [← Complex.exp_conj]
  congr 1
  simp [div_eq_mul_inv]
  simp [starRingEnd]
  ring

lemma omega_pow_self_shor (r : ℕ) (hr : 0 < r) : (ω r) ^ r = 1 := by
  unfold ω
  rw [← Complex.exp_nat_mul]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have harg : (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I := by
    field_simp [hr0]
  rw [harg, Complex.exp_two_pi_mul_I]

lemma qftPhase_mod_left_shor (r t k : ℕ) (hr : 0 < r) :
    qftPhase r t k = qftPhase r (t % r) k := by
  unfold qftPhase ωPow
  have ht : t * k = (t % r) * k + r * ((t / r) * k) := by
    calc
      t * k = (t % r + r * (t / r)) * k := by rw [Nat.mod_add_div]
      _ = (t % r) * k + r * ((t / r) * k) := by ring
  rw [ht, pow_add]
  have hp : (ω r) ^ (r * ((t / r) * k)) = 1 := by
    rw [pow_mul, omega_pow_self_shor r hr]
    simp
  rw [hp, mul_one]

lemma norm_qftPhase_one_shor (M x y : ℕ) : ‖qftPhase M x y‖ = 1 := by
  rw [qftPhase_eq_exp_grid_shor, Complex.norm_exp]
  simp

end Shor
