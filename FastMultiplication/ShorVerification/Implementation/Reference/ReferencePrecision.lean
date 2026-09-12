import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Defs

namespace Shor
namespace Reference

/-!
# Reference precision schedule

The reference implementation exposes only a natural-number precision level
`m` to its framework-facing interface. Internally it still needs the real
approximation parameter `η = referencePrecision m` to state Algorithm 1's
precision requirement (`Algorithm1Precision`), but the *width* that parameter
forces on the work register is computable: `algorithm1ExtraBitsNat` computes
it directly from `m` with `Nat.clog`, without going through `Real.logb`, and
`algorithm1ExtraBits_referencePrecision` proves the two agree.
-/

/--
Approximation parameter used by the reference implementation at precision
level `m`.

The offset by `3` ensures that every precision level satisfies

    0 < η < 1 / 2,

including `m = 0`, while `η → 0` as `m → ∞`.
-/
noncomputable def referencePrecision (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 3)

/-- Every reference precision parameter is positive. -/
theorem referencePrecision_pos (m : ℕ) :
    0 < referencePrecision m := by
  unfold referencePrecision
  positivity

/-- Every reference precision parameter lies below `1 / 2`. -/
theorem referencePrecision_lt_half (m : ℕ) :
    referencePrecision m < (1 / 2 : ℝ) := by
  unfold referencePrecision

  have hden :
      (0 : ℝ) < (m : ℝ) + 3 := by
    positivity

  rw [div_lt_iff₀ hden]

  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by
    positivity
  nlinarith

/-- Computable work-width extra-bits count at precision level `m`, avoiding
`Real.logb`. See `algorithm1ExtraBits_referencePrecision` for the bridge to
`algorithm1ExtraBits (referencePrecision m)`. -/
def algorithm1ExtraBitsNat (m : ℕ) : ℕ :=
  Nat.clog 2 ((m + 7) ^ 2) - 2

example : algorithm1ExtraBitsNat 0 = 4 := by decide
example : algorithm1ExtraBitsNat 1 = 4 := by decide

/-- `algorithm1ExtraBitsNat` computes exactly `algorithm1ExtraBits` at the
reference precision schedule. -/
theorem algorithm1ExtraBits_referencePrecision (m : ℕ) :
    algorithm1ExtraBits (referencePrecision m) = algorithm1ExtraBitsNat m := by
  unfold algorithm1ExtraBits algorithm1ExtraBitsNat referencePrecision

  have hstep :
      (2 + 1 / (2 * (1 / ((m : ℝ) + 3)))) = ((m : ℝ) + 7) / 2 := by
    have hm3 : ((m : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring

  rw [hstep]

  have hlogb :
      2 * Real.logb 2 (((m : ℝ) + 7) / 2) =
        Real.logb 2 (((((m + 7) ^ 2 : ℕ)) : ℝ)) - 2 := by
    rw [Real.logb_div (by positivity) (by norm_num)]
    have hpow :
        Real.logb 2 ((((m + 7) ^ 2 : ℕ) : ℝ)) =
          2 * Real.logb 2 (((m : ℝ) + 7)) := by
      rw [show (((((m + 7) ^ 2 : ℕ)) : ℝ)) = (((m : ℝ) + 7)) ^ 2 by push_cast; ring]
      rw [Real.logb_pow]
      push_cast
      ring
    rw [hpow, Real.logb_self_eq_one (by norm_num)]
    ring

  rw [hlogb]

  have hcast2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hcast2, Nat.ceil_sub_natCast, Real.natCeil_logb_natCast]

end Reference
end Shor
