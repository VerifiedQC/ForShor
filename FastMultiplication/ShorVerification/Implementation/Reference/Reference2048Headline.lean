import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation
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

This file is additive: it does not change that general submission. It
answers a narrower, concrete question for the case the whole codebase is
ultimately aimed at — `N` a 2048-bit modulus — by fixing a single explicit
precision `η = 2⁻¹⁵⁰` (via an explicit level `m2048`) and proving that,
*at that fixed level*, the single-run success probability is at least
99% of the ideal `κ / (log₂ N)⁴` baseline. Combined with the trial-count
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
variable [IdealCtrlModMulExactSemantics qs]

/-! =========================================================
    Section 1: 2048-bit numerics
========================================================= -/

/-- `N` has exactly 2048 bits: `2^2047 ≤ N < 2^2048`. -/
def Is2048Bit (N : ℕ) : Prop := 2 ^ 2047 ≤ N ∧ N < 2 ^ 2048

theorem Is2048Bit.log2_eq {N : ℕ} (hN : Is2048Bit N) : Nat.log2 N = 2047 := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow hN.1 hN.2

/-- The exponent/output-register width `tbits` is at most `4096` bits for any
2048-bit modulus (it need not be exactly `4096`: `2*N^2` can straddle a power
of two boundary depending on where exactly `N` sits in `[2^2047, 2^2048)`). -/
theorem Is2048Bit.tbits_le {N : ℕ} (hN : Is2048Bit N) :
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

/-- A comfortably safe rational lower bound for `κ = 4 e⁻² / π²`: the true
value is `≈ 0.05485`, well above `1/25 = 0.04`. -/
theorem kappa_ge_one_div_25 : (1 : ℝ) / 25 ≤ κ := by
  have he1 : Real.exp 1 < 2.7183 :=
    lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num)
  have he1pos : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : Real.exp 2 < 7.39 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    nlinarith [he1, he1pos]
  have he2pos : 0 < Real.exp 2 := Real.exp_pos 2
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 9.9225 := by nlinarith [hpi, hpipos]
  have hprod : Real.pi ^ 2 * Real.exp 2 < 100 := by
    have hstep : Real.pi ^ 2 * Real.exp 2 < 9.9225 * Real.exp 2 := by
      apply mul_lt_mul_of_pos_right hpi2 he2pos
    have hstep2 : (9.9225 : ℝ) * Real.exp 2 < 9.9225 * 7.39 := by
      apply mul_lt_mul_of_pos_left he2 (by norm_num)
    linarith [hstep, hstep2]
  have hexpnegpos : 0 < Real.exp (-2) := Real.exp_pos (-2)
  have hpi2pos : 0 < Real.pi ^ 2 := by positivity
  have hcomm : Real.exp 2 * Real.exp (-2) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hkey : Real.pi ^ 2 < 100 * Real.exp (-2) := by
    have h := mul_lt_mul_of_pos_right hprod hexpnegpos
    have heq : Real.pi ^ 2 * Real.exp 2 * Real.exp (-2) = Real.pi ^ 2 := by
      calc Real.pi ^ 2 * Real.exp 2 * Real.exp (-2)
          = Real.pi ^ 2 * (Real.exp 2 * Real.exp (-2)) := by ring
        _ = Real.pi ^ 2 * 1 := by rw [hcomm]
        _ = Real.pi ^ 2 := by ring
    rwa [heq] at h
  rw [κ, le_div_iff₀ hpi2pos]
  linarith [hkey]

/-! =========================================================
    Section 4: Single-run success bound at the 2048-bit headline level
========================================================= -/

/-- The declared success bound at the fixed 2048-bit precision level retains
at least 99% of the ideal `κ / (log₂ N)^4` baseline, for every 2048-bit
modulus. This is the concrete statement of "choosing `η` and proving the
achieved success probability" for the case the submission is aimed at. -/
theorem headline_success_bound {N : ℕ} (hN : Is2048Bit N) :
    (99 / 100 : ℝ) * (κ / (2047 : ℝ) ^ 4) ≤
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
  have hkappa : (1 : ℝ) / 25 ≤ κ := kappa_ge_one_div_25
  have hrational : (1 : ℝ) / 2 ^ 56 ≤ (1 / 100) * (κ / (2047 : ℝ) ^ 4) := by
    have hnum : (1 : ℝ) / 100 * ((1 : ℝ) / 25) / (2047 : ℝ) ^ 4 ≤
        (1 / 100) * (κ / (2047 : ℝ) ^ 4) := by
      have hstep : (1 : ℝ) / 25 / (2047 : ℝ) ^ 4 ≤ κ / (2047 : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right hkappa (by positivity)
      have heq : (1 : ℝ) / 100 * ((1 : ℝ) / 25) / (2047 : ℝ) ^ 4 =
          (1 / 100) * ((1 : ℝ) / 25 / (2047 : ℝ) ^ 4) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    have hkey : (1 : ℝ) / 2 ^ 56 ≤ (1 : ℝ) / 100 * ((1 : ℝ) / 25) / (2047 : ℝ) ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num
    exact le_trans hkey hnum
  have hraw : (99 / 100 : ℝ) * (κ / (2047 : ℝ) ^ 4) ≤
      referenceRawSuccessProbabilityAt m2048 N := by
    unfold referenceRawSuccessProbabilityAt
    rw [hlog]
    have hcomb : referenceApproximationErrorAt m2048 N ≤ (1 / 100) * (κ / (2047 : ℝ) ^ 4) :=
      le_trans herr hrational
    have hkappa_nonneg : 0 ≤ κ := by rw [κ]; positivity
    nlinarith [hcomb, hkappa_nonneg]
  -- `headlineP` (the 99%-of-baseline value) is a tiny positive number, so it
  -- lands unclamped inside `max 0 (min 1 raw)` without needing `raw ≤ 1`.
  have hP_le_one : (99 / 100 : ℝ) * (κ / (2047 : ℝ) ^ 4) ≤ 1 := by
    have hkappa_small : κ < 4 := by
      rw [κ]
      have he2 : Real.exp (-2 : ℝ) < 1 := by
        have h := Real.exp_lt_exp.mpr (show (-2 : ℝ) < 0 by norm_num)
        rwa [Real.exp_zero] at h
      have hpi2 : (1 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
      rw [div_lt_iff₀ (show (0 : ℝ) < Real.pi ^ 2 by positivity)]
      linarith [he2, hpi2]
    have hdenbig : (4 : ℝ) ≤ (2047 : ℝ) ^ 4 := by norm_num
    have hratio : κ / (2047 : ℝ) ^ 4 ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [hkappa_small, hdenbig]
    nlinarith [hratio]
  have hP_nonneg : (0 : ℝ) ≤ (99 / 100 : ℝ) * (κ / (2047 : ℝ) ^ 4) := by
    have hkappa_nonneg : 0 ≤ κ := by rw [κ]; positivity
    have : 0 ≤ κ / (2047 : ℝ) ^ 4 := div_nonneg hkappa_nonneg (by positivity)
    linarith [mul_nonneg (show (0:ℝ) ≤ 99/100 by norm_num) this]
  unfold referenceSuccessProbabilityAt
  rw [max_eq_right (le_trans hP_nonneg (le_min hP_le_one hraw))]
  exact le_min hP_le_one hraw

/-- Single-run success of the fixed-level reference program, for a 2048-bit
instance, is at least 99% of the ideal `κ/(log₂N)^4` baseline. -/
theorem headline_program_success
    (lowering : ShorLoweringSetup) {N : ℕ} (hN : Is2048Bit N)
    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)
    (inst : ShorOrderFindingInstance) (hinstN : inst.N = N) :
    (99 / 100 : ℝ) * (κ / (2047 : ℝ) ^ 4) ≤
      probability_of_success
        (qs := qs)
        (evalC := LowerGateClass.evalL (qs := qs))
        (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := (referenceProgramAt lowering m2048 inst).output)
        (r := ord inst.a inst.N inst.coprime)
        (Q := ASize (referenceProgramAt lowering m2048 inst).output)
        (C := (referenceProgramAt lowering m2048 inst).circuit)
        (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) := by
  have h := referenceProgramAt_success (qs := qs) lowering m2048 T hT inst
  rw [← hinstN] at hN
  exact le_trans (headline_success_bound hN) h

/-! =========================================================
    Section 5: Trial count and total gate count at the headline level
========================================================= -/

/-- The clean 99%-of-baseline success value used to amplify to overall 99%
success. -/
def headlineP : ℝ := (99 / 100) * (κ / (2047 : ℝ) ^ 4)

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
  change (99 / 100 : ℝ) ≤ 1 - (1 - headlineP) ^ k
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
    (lowering : ShorLoweringSetup) (inst : ShorOrderFindingInstance) : ℕ :=
  LowGate.gateCount shorGateCostModel
    (referenceProgramAt lowering m2048 inst).circuit

/-- Total gate count across all `headlineTrialCount` independent runs: this is
the quantity ("trials × single-run gate count") that a fast-vs-naive Shor
comparison should be made against, for a 2048-bit modulus, given that
`headlineTrialCount` independent runs are proved sufficient for ≥99% overall
success. -/
def headlineTotalGateCount
    (lowering : ShorLoweringSetup) (inst : ShorOrderFindingInstance) : ℕ :=
  headlineTrialCount * headlineGateCount lowering inst

end

end Reference
end Shor
