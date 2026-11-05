import ForShor.ShorVerification.Implementation.Reference.Standard.Proofs.Success
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reference: the 2048-bit headline

At the fixed level `m2048` (`η = 2⁻¹⁵⁰`), the declared bound keeps at least 99% of
the ideal `κ / log(log₂ N + 1)` baseline for every 2048-bit modulus
(`headline_success_bound`), and `headlineTrialCount` trials amplify that to 99%.
-/

namespace Shor
namespace Reference

/-! ## 2048-bit numerics -/

-- `Is2048Bit`'s `2 ^ 2047` bound trips the default `exponentiation.threshold` of 256.
set_option exponentiation.threshold 4100 in
theorem _root_.Shor.Is2048Bit.log2_eq {N : ℕ} (hN : Is2048Bit N) : Nat.log2 N = 2047 := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow hN.1 hN.2

set_option exponentiation.threshold 4100 in
/-- The exponent register has at most `4096` bits for any 2048-bit modulus (`2 * N^2`
can straddle a power of two). -/
theorem _root_.Shor.Is2048Bit.tbits_le {N : ℕ} (hN : Is2048Bit N) :
    Nat.log2 (2 * N ^ 2) ≤ 4096 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN.1
  have hynz : (2 * N ^ 2 : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) (pow_ne_zero 2 hNpos.ne')
  rw [Nat.log2_eq_log_two]
  apply Nat.le_of_lt_succ
  apply Nat.log_lt_of_lt_pow hynz
  calc
    2 * N ^ 2 < 2 * (2 ^ 2048 : ℕ) ^ 2 := by gcongr; exact hN.2
    _ = 2 ^ 1 * 2 ^ (2048 * 2) := by rw [pow_mul]; norm_num
    _ = 2 ^ 4097 := by rw [← pow_add]

theorem referencePrecision_m2048 : referencePrecision m2048 = 1 / (2 : ℝ) ^ 150 := by
  have h3 : (3 : ℕ) ≤ 2 ^ 150 := by norm_num
  unfold referencePrecision m2048
  rw [Nat.cast_sub h3]
  push_cast
  ring

/-- `κ = 1 / π² ≈ 0.1013` is above `1/10`. -/
theorem kappa_ge_one_div_ten : (1 : ℝ) / 10 ≤ κ := by
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith
  have hpi2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  rw [κ, le_div_iff₀ hpi2pos]
  linarith

/-! ## The single-run bound at the headline level -/

/-- At `m2048`, the declared bound keeps at least 99% of `κ / log 2048` for every
2048-bit modulus. -/
theorem headline_success_bound {N : ℕ} (hN : Is2048Bit N) :
    (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤ referenceSuccessProbabilityAt m2048 N := by
  have hlog : Nat.log2 N = 2047 := hN.log2_eq
  have htbits : Nat.log2 (2 * N ^ 2) ≤ 4096 := hN.tbits_le
  have htbits_eq :
      regSize (Reg.interval 0 (Nat.log2 (2 * N ^ 2))) = Nat.log2 (2 * N ^ 2) := by
    simp [regSize, Reg.width, Reg.interval]
  -- The error term at `η = 2⁻¹⁵⁰`, `K = 1600`, is at most `2⁻⁵⁶`.
  have herr : referenceApproximationErrorAt m2048 N ≤ (1 : ℝ) / 2 ^ 56 := by
    unfold referenceApproximationErrorAt
    rw [referencePrecision_m2048, htbits_eq]
    have htbits_cast : (Nat.log2 (2 * N ^ 2) : ℝ) ≤ 4096 := by exact_mod_cast htbits
    have hradicand : (2 : ℝ) * (referenceK * (1 / (2 : ℝ) ^ 150)) ≤ 1 / 2 ^ 138 := by
      norm_num [referenceK]
    have hsqrt :
        Real.sqrt (2 * (referenceK * (1 / (2 : ℝ) ^ 150))) ≤ 1 / (2 : ℝ) ^ 69 := by
      have heq : (1 / (2 : ℝ) ^ 138) = (1 / (2 : ℝ) ^ 69) ^ 2 := by norm_num
      calc Real.sqrt (2 * (referenceK * (1 / (2 : ℝ) ^ 150)))
          ≤ Real.sqrt (1 / (2 : ℝ) ^ 138) := Real.sqrt_le_sqrt hradicand
        _ = 1 / (2 : ℝ) ^ 69 := by rw [heq]; exact Real.sqrt_sq (by positivity)
    calc
      2 * (Nat.log2 (2 * N ^ 2) : ℝ) * Real.sqrt (2 * (referenceK * (1 / (2 : ℝ) ^ 150)))
        ≤ 2 * 4096 * (1 / (2 : ℝ) ^ 69) := by gcongr
      _ = 1 / 2 ^ 56 := by norm_num
  have hkappa : (1 : ℝ) / 10 ≤ κ := kappa_ge_one_div_ten
  -- `log 2048 = 11 log 2`, bracketed by `Real.log_two_gt_d9` / `Real.log_two_lt_d9`.
  have hlog_pos : (0 : ℝ) < Real.log (2048 : ℝ) := Real.log_pos (by norm_num)
  have hlog11 : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; norm_num
  have hlog_le : Real.log (2048 : ℝ) ≤ 763 / 100 := by
    rw [hlog11]; linarith [Real.log_two_lt_d9]
  have hlog_ge : (1 : ℝ) ≤ Real.log (2048 : ℝ) := by
    rw [hlog11]; linarith [Real.log_two_gt_d9]
  have hrational : (1 : ℝ) / 2 ^ 56 ≤ (1 / 100) * (κ / Real.log (2048 : ℝ)) := by
    have hstep : ((1 : ℝ) / 10) / (763 / 100 : ℝ) ≤ κ / Real.log (2048 : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hlog_pos]
      nlinarith [hkappa, hlog_le, hlog_pos]
    have hkey : (1 : ℝ) / 2 ^ 56 ≤ (1 / 100) * (((1 : ℝ) / 10) / (763 / 100 : ℝ)) := by
      norm_num
    linarith [mul_le_mul_of_nonneg_left hstep (show (0 : ℝ) ≤ 1 / 100 by norm_num)]
  have hraw : (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤
      referenceRawSuccessProbabilityAt m2048 N := by
    unfold referenceRawSuccessProbabilityAt
    rw [hlog]
    have hcomb : referenceApproximationErrorAt m2048 N ≤ (1 / 100) * (κ / Real.log (2048 : ℝ)) :=
      le_trans herr hrational
    have hkappa_nonneg : 0 ≤ κ := by rw [κ]; positivity
    nlinarith [hcomb, hkappa_nonneg]
  -- The 99%-of-baseline value is a small positive number, so it sits unclamped
  -- inside `max 0 (min 1 raw)` without needing `raw ≤ 1`.
  have hP_le_one : (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤ 1 := by
    have hkappa_le_one : κ ≤ 1 := by
      rw [κ, div_le_one (show (0 : ℝ) < Real.pi ^ 2 by positivity)]
      nlinarith [Real.pi_gt_three]
    have hratio : κ / Real.log (2048 : ℝ) ≤ 1 := by
      rw [div_le_one hlog_pos]
      linarith
    linarith
  have hP_nonneg : (0 : ℝ) ≤ (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) := by
    have hkappa_nonneg : 0 ≤ κ := κ_pos.le
    have : 0 ≤ κ / Real.log (2048 : ℝ) := div_nonneg hkappa_nonneg hlog_pos.le
    linarith
  unfold referenceSuccessProbabilityAt
  rw [max_eq_right (le_trans hP_nonneg (le_min hP_le_one hraw))]
  exact le_min hP_le_one hraw

/-! ## The trial count at the headline level -/

theorem headlineP_pos : 0 < headlineP := by
  unfold headlineP κ
  positivity

theorem exists_headline_trialCount : ∃ k : ℕ, (99 / 100 : ℝ) ≤ 1 - (1 - headlineP) ^ k := by
  have hp : 0 < headlineP := headlineP_pos
  have hlt : 1 - headlineP < (1 : ℝ) := by linarith
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one (K := ℝ) (x := (1 / 100 : ℝ)) (y := 1 - headlineP) (by norm_num) hlt
  refine ⟨k, ?_⟩
  linarith

theorem headlineTrialCount_correct : (99 / 100 : ℝ) ≤ 1 - (1 - headlineP) ^ headlineTrialCount := by
  have hex := exists_headline_trialCount
  rw [headlineTrialCount, dite_eq_left hex]
  exact Nat.find_spec hex

end Reference
end Shor
