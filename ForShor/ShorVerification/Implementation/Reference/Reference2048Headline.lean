import ForShor.ShorVerification.Implementation.Reference.ReferenceShorImplementation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concrete 2048-bit headline results

`ReferenceShorImplementation.lean` builds a `ShorImplementation` that is
correct and gate-counted for *every* modulus `N`, choosing its internal
precision level `m` automatically (via `Nat.find`, an unspecified and
generally very weak choice: it only guarantees a *positive* success
probability, not any particular fraction of the ideal baseline).

This file does not change that general result. It
answers a narrower, concrete question for the case the whole codebase is
ultimately aimed at — `N` a 2048-bit modulus — by fixing a single explicit
precision `η = 2⁻¹⁵⁰` (via an explicit level `m2048`) and proving that,
*at that fixed level*, the single-run success probability is at least
99% of the ideal `κ / log(log₂ N + 1)` baseline. Combined with the trial-count
amplification already proved in `ReferenceShorImplementation.lean`, this
gives a genuine "trials × single-run gate count" total for the 2048-bit
case, which is what a submission-vs-naive-Shor comparison should be based
on.

No closed-form or concrete-numeral gate count exists anywhere in this
codebase (`Shor_GateCount.lean` only proves asymptotic bounds with unnamed
existential constants), so `headlineGateCount` below is declared, honestly,
as the actual (structurally opaque) `LowGate.gateCount` of the submitted
circuit — not a computed number. It is nonetheless exactly the quantity a
gate-count comparison against another counted circuit would need to bound.
-/

namespace Shor
namespace Reference

noncomputable section

variable {qs : QSemantics}
variable [RegEncoding qs.Basis]
variable [MeasureClass qs]
variable [GateSemanticsFacts qs]
variable [LowerGateClass qs]

/-! =========================================================
    Section 1: 2048-bit numerics
========================================================= -/

-- `Is2048Bit`'s `2 ^ 2047` bound trips the default `exponentiation.threshold` of 256.
set_option exponentiation.threshold 4100 in
theorem _root_.Shor.Is2048Bit.log2_eq {N : ℕ} (hN : Is2048Bit N) :
    Nat.log2 N = 2047 := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow hN.1 hN.2

-- The `2 ^ 4097` step below trips the default `exponentiation.threshold` of 256.
set_option exponentiation.threshold 4100 in
/-- The exponent/output-register width `tbits` is at most `4096` bits for any
2048-bit modulus (it need not be exactly `4096`: `2*N^2` can straddle a power
of two boundary depending on where exactly `N` sits in `[2^2047, 2^2048)`). -/
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

/-! =========================================================
    Section 2: A fixed, explicit precision level for `N ~ 2^2048`
========================================================= -/

/-- The explicit precision level chosen for the 2048-bit headline: under the
reference schedule `referencePrecision m = 1/(m+3)`, this level gives
`η = 2⁻¹⁵⁰` exactly. -/
def m2048 : ℕ := 2 ^ 150 - 3

theorem referencePrecision_m2048 :
    referencePrecision m2048 = 1 / (2 : ℝ) ^ 150 := by
  have h3 : (3 : ℕ) ≤ 2 ^ 150 := by norm_num
  unfold referencePrecision m2048
  rw [Nat.cast_sub h3]
  push_cast
  ring

/-! =========================================================
    Section 3: A safe rational lower bound for `κ`
========================================================= -/

/-- A safe rational lower bound for `κ = 1 / π²`: the true value is
`≈ 0.1013`, above `1/10` (equivalently `π² ≤ 10`). -/
theorem kappa_ge_one_div_ten : (1 : ℝ) / 10 ≤ κ := by
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith
  have hpi2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  rw [κ, le_div_iff₀ hpi2pos]
  linarith

/-! =========================================================
    Section 4: Single-run success bound at the 2048-bit headline level
========================================================= -/

/-- The declared success bound at the fixed 2048-bit precision level retains
at least 99% of the ideal `κ / log(log₂ N + 1)` baseline, for every 2048-bit
modulus. This is the concrete statement of "choosing `η` and proving the
achieved success probability" for the case the submission is aimed at. -/
theorem headline_success_bound {N : ℕ} (hN : Is2048Bit N) :
    (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤
      referenceSuccessProbabilityAt m2048 N := by
  have hlog : Nat.log2 N = 2047 := hN.log2_eq
  have htbits : Nat.log2 (2 * N ^ 2) ≤ 4096 := hN.tbits_le
  have htbits_eq :
      tbits (Reg.interval 0 (Nat.log2 (2 * N ^ 2))) = Nat.log2 (2 * N ^ 2) := by
    simp [tbits, regSize, Reg.width, Reg.interval]
  -- The error term at `η = 2⁻¹⁵⁰`, `K = referenceK = 2048`, is at most `2⁻⁵⁶`.
  have herr : referenceApproximationErrorAt m2048 N ≤ (1 : ℝ) / 2 ^ 56 := by
    unfold referenceApproximationErrorAt
    rw [referencePrecision_m2048, htbits_eq]
    have htbits_cast : (Nat.log2 (2 * N ^ 2) : ℝ) ≤ 4096 := by exact_mod_cast htbits
    have hK : referenceK = 2048 := rfl
    have hradicand : (2 : ℝ) * (referenceK * (1 / (2 : ℝ) ^ 150)) = 1 / 2 ^ 138 := by
      rw [hK]
      rw [show (2 : ℝ) * (2048 * (1 / (2 : ℝ) ^ 150)) = (2 * 2048) / (2 : ℝ) ^ 150 by ring]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      have h2048 : (2 : ℝ) * 2048 = 2 ^ 12 := by norm_num
      rw [h2048, ← pow_add]
      norm_num
    rw [hradicand]
    have hsqrt : Real.sqrt (1 / (2 : ℝ) ^ 138) = 1 / (2 : ℝ) ^ 69 := by
      have heq : (1 / (2 : ℝ) ^ 138) = (1 / (2 : ℝ) ^ 69) ^ 2 := by norm_num
      rw [heq]
      exact Real.sqrt_sq (by positivity)
    rw [hsqrt]
    calc
      2 * (Nat.log2 (2 * N ^ 2) : ℝ) * (1 / (2 : ℝ) ^ 69)
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
  -- `headlineP` (the 99%-of-baseline value) is a tiny positive number, so it
  -- lands unclamped inside `max 0 (min 1 raw)` without needing `raw ≤ 1`.
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

/-- Single-run success of the fixed-level reference program, for a 2048-bit
instance, is at least 99% of the ideal `κ / log(log₂ N + 1)` baseline. -/
theorem headline_program_success
    (P : ShorLoweringPolicy) (hP : P.Admissible) {N : ℕ} (hN : Is2048Bit N)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (hinstN : inst.N = N) :
    (99 / 100 : ℝ) * (κ / Real.log (2048 : ℝ)) ≤
      probability_of_success
        (qs := qs)
        (evalC := LowerGateClass.evalL (qs := qs))
        (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (referenceProgramAt P hP m2048 inst).output)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (referenceProgramAt P hP m2048 inst).output)
        (C := (referenceProgramAt P hP m2048 inst).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  have h := referenceProgramAt_success (qs := qs) P hP m2048 T hT inst
  rw [← hinstN] at hN
  exact le_trans (headline_success_bound hN) h

/-! =========================================================
    Section 5: Trial count and total gate count at the headline level
========================================================= -/

/-- The clean 99%-of-baseline success value used to amplify to overall 99%
success. -/
def headlineP : ℝ := (99 / 100) * (κ / Real.log (2048 : ℝ))

theorem headlineP_pos : 0 < headlineP := by
  unfold headlineP κ
  positivity

theorem exists_headline_trialCount :
    ∃ k : ℕ, (99 / 100 : ℝ) ≤ 1 - (1 - headlineP) ^ k := by
  have hp : 0 < headlineP := headlineP_pos
  have hlt : 1 - headlineP < (1 : ℝ) := by linarith
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one (K := ℝ) (x := (1 / 100 : ℝ)) (y := 1 - headlineP)
      (by norm_num) hlt
  refine ⟨k, ?_⟩
  linarith

/-- Number of independent trials sufficient to amplify the headline
single-run bound to at least 99% overall success. -/
def headlineTrialCount : ℕ := Nat.find exists_headline_trialCount

theorem headlineTrialCount_correct :
    (99 / 100 : ℝ) ≤ 1 - (1 - headlineP) ^ headlineTrialCount :=
  Nat.find_spec exists_headline_trialCount

/-- The actual (structurally opaque) logical gate count of a single run of the
headline-level reference circuit for a 2048-bit instance. There is no
closed-form/concrete-numeral formula for this quantity anywhere in the
codebase (`Shor_GateCount.lean` proves only asymptotic bounds with unnamed
constants); this is the honest declared value. -/
def headlineGateCount
    (P : ShorLoweringPolicy) (hP : P.Admissible) (inst : ShorOrderFindingInstance) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (referenceProgramAt P hP m2048 inst).circuit

/-- Total gate count across all `headlineTrialCount` independent runs: this is
the quantity ("trials × single-run gate count") that a fast-vs-naive Shor
comparison should be made against, for a 2048-bit modulus, given that
`headlineTrialCount` independent runs are proved sufficient for ≥99% overall
success. -/
def headlineTotalGateCount
    (P : ShorLoweringPolicy) (hP : P.Admissible) (inst : ShorOrderFindingInstance) : ℕ :=
  headlineTrialCount * headlineGateCount P hP inst

end

end Reference
end Shor
