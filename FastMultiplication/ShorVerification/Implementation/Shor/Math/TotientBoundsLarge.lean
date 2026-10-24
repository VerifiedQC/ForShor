import FastMultiplication.ShorVerification.Implementation.Shor.Math.TotientBounds
import FastMultiplication.ShorVerification.Vendor.Mertens.Theorems

/-!
# The `1 / log log` totient bound above `2 ^ 2048`

`Math/TotientBounds.lean` proves `1 / (4 log (log₂ (r+1) + 1)) ≤ φ(r)/r` for `r < 2 ^ 2048`
by a finite case split.  This file covers the complementary range with Mertens' third
theorem, taking the threshold in the split lemma to be `M = ⌊log r⌋₊`:

* `∏_{p < M} (1 - 1/p) = e^{-γ} e^{E₃(M-1)} / log (M-1)` (`prod_prime_one_minus_inv_eq_nat`),
  with `|E₃ x| ≤ (log 4 + 3)/log x + 1/⌊x⌋₊` (`E₃_bound`), both from the vendored Mertens
  files in `Vendor/Mertens/`;
* at most `log r / log M` prime factors of `r` are `≥ M`, so the large-prime factor is
  at least `1 - 1.015 / log (M-1)`;
* `γ < 0.609` from `γ < harmonic 16 - log 16` (`eulerMascheroniConstant_lt_eulerMascheroniSeq'`).

Writing `v = log (M - 1) ≥ 7.2`, these give `φ(r)/r ≥ (0.2917/v)(1 - 1.015/v)`, while the
target is `1 / (4 (v + 0.35))`; the resulting polynomial inequality holds for `v ≥ 5.14`.
The margin at `r = 2 ^ 2048` is about 5%.

All exponential and logarithm estimates come from `1 + x ≤ exp x`, `Real.exp_one_lt_d9` and
`Real.log_two_gt_d9` / `Real.log_two_lt_d9`; nothing here needs numerical evaluation.
-/

namespace Shor

open Finset

/-- `γ < 0.609`, from `γ < harmonic 16 - log 16` and `log 2 > 0.6931471803`. -/
lemma gamma_lt : Real.eulerMascheroniConstant < 609 / 1000 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 16
  rw [Real.eulerMascheroniSeq'] at h
  norm_num at h
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [h16] at h
  have := Real.log_two_gt_d9
  linarith

/-- `exp 0.0875 ≤ 1 / 0.9125`. -/
private lemma exp_small_le : Real.exp (875 / 10000) ≤ 10000 / 9125 := by
  have h := Real.add_one_le_exp (-(875 / 10000 : ℝ))
  have hpos : (0 : ℝ) < Real.exp (875 / 10000) := Real.exp_pos _
  rw [Real.exp_neg] at h
  rw [le_div_iff₀ (by norm_num)]
  have h2 : (9125 / 10000 : ℝ) ≤ (Real.exp (875 / 10000))⁻¹ := by linarith
  rw [le_inv_comm₀ (by norm_num) hpos] at h2
  linarith

/-- `-log (log 2) ≥ 0.35`, i.e. `log 2 ≤ exp (-0.35)`. -/
lemma neg_log_log_two_ge : (35 / 100 : ℝ) ≤ -Real.log (Real.log 2) := by
  have hexp : Real.exp (35 / 100 : ℝ) ≤ 14426 / 10000 := by
    have h4 : Real.exp (35 / 100 : ℝ) = (Real.exp (875 / 10000)) ^ (4 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    calc (Real.exp (875 / 10000)) ^ (4 : ℕ) ≤ (10000 / 9125 : ℝ) ^ (4 : ℕ) :=
          by gcongr; exact exp_small_le
      _ ≤ 14426 / 10000 := by norm_num
  have hlog2 : Real.log 2 < 6931471808 / 10 ^ 10 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log 2 ≤ Real.exp (-(35 / 100 : ℝ)) := by
    rw [Real.exp_neg, le_inv_comm₀ hlog2pos (Real.exp_pos _)]
    calc Real.exp (35 / 100 : ℝ) ≤ 14426 / 10000 := hexp
      _ ≤ (Real.log 2)⁻¹ := by
          rw [le_inv_comm₀ (by norm_num) hlog2pos]
          nlinarith
  have := Real.log_le_log hlog2pos key
  rw [Real.log_exp] at this
  linarith


set_option maxHeartbeats 1000000 in
/-- The Mertens-type lower bound on the product over the primes below `M`. -/
lemma prod_primesBelow_ge {M : ℕ} {v : ℝ} (hM : 1419 ≤ M)
    (hv : v = Real.log ((M - 1 : ℕ) : ℝ)) :
    Real.exp (-(609 / 1000) - (4387 / 1000 / v + 1 / 1418))
      ≤ (∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹)) * v := by
  set N := M - 1 with hNdef
  have hN : 1418 ≤ N := by omega
  have hNM : N + 1 = M := by omega
  have hNR : (1418 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hvpos : (72 / 10 : ℝ) ≤ v := by
    rw [hv]
    have h := log_ge_of_two_pow_le (k := 10) (x := (N : ℝ)) (by norm_num; linarith)
    have h2 := Real.log_two_gt_d9
    have h3 : (1024 : ℝ) / (N : ℝ) ≤ 1024 / 1418 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNR
    norm_num at h h2 h3 ⊢
    nlinarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hprimes : Nat.primesBelow M = Nat.primesLE N := by rw [Nat.primesLE, hNM]
  have hmert := Mertens.prod_prime_one_minus_inv_eq_nat (N := N) (by omega)
  have hE := Mertens.E₃_bound (x := (N : ℝ)) (by linarith)
  rw [Nat.floor_natCast] at hE
  have hrw : (∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹))
      = ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) := by
    rw [hprimes]; exact Finset.prod_congr rfl fun p _ => by rw [one_div]
  rw [hrw, hmert, ← hv, div_mul_cancel₀ _ hv0.ne', ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hγ := gamma_lt
  have hE' : -((4387 / 1000) / v + 1 / 1418) ≤ Mertens.E₃ (N : ℝ) := by
    have h1 : |Mertens.E₃ (N : ℝ)| ≤ (Real.log 4 + 3) / v + 1 / (N : ℝ) := by
      rw [hv]; exact hE
    have h2 : Real.log 4 ≤ 13863 / 10000 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
    have h3 : (Real.log 4 + 3) / v ≤ (4387 / 1000) / v :=
      by gcongr; linarith
    have h4 : (1 : ℝ) / (N : ℝ) ≤ 1 / 1418 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNR
    have h5 := abs_le.mp h1
    linarith [h5.1]
  linarith

/-- `exp (-1) ≥ 0.36787`. -/
private lemma exp_neg_one_ge : (36787 / 100000 : ℝ) ≤ Real.exp (-1) := by
  have h := Real.exp_one_lt_d9
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
  norm_num at h ⊢
  linarith

/-- `0.2917 ≤ exp (-1.219012)`, via `exp (-c) = exp (-1) · (exp ((1-c)/2))²`
and `1 + t ≤ exp t`. -/
private lemma exp_neg_c_ge : (2917 / 10000 : ℝ) ≤ Real.exp (-(1219012 / 1000000)) := by
  have hsplit : Real.exp (-(1219012 / 1000000 : ℝ))
      = Real.exp (-1) * (Real.exp ((1 - 1219012 / 1000000) / 2)) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have hlin : (890494 / 1000000 : ℝ) ≤ Real.exp ((1 - 1219012 / 1000000) / 2) := by
    have := Real.add_one_le_exp ((1 - 1219012 / 1000000 : ℝ) / 2)
    linarith
  have hsq : (890494 / 1000000 : ℝ) ^ (2 : ℕ)
      ≤ (Real.exp ((1 - 1219012 / 1000000) / 2)) ^ (2 : ℕ) := by
    gcongr
  rw [hsplit]
  calc (2917 / 10000 : ℝ) ≤ (36787 / 100000) * (890494 / 1000000 : ℝ) ^ (2 : ℕ) := by norm_num
    _ ≤ Real.exp (-1) * (Real.exp ((1 - 1219012 / 1000000) / 2)) ^ (2 : ℕ) := by
        gcongr; exact exp_neg_one_ge

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 5000 in
/-- **Region C.**  For `r ≥ 2 ^ 2048`, Mertens' third theorem with the explicit error
term `E₃` gives `φ(r)/r ≥ 1 / (4 log (log₂ (r+1) + 1))`. -/
theorem totient_ratio_loglog_of_ge {r : ℕ} (hr : 2 ^ 2048 ≤ r) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  classical
  have hr0 : 0 < r := lt_of_lt_of_le (Nat.two_pow_pos _) hr
  have hrR : ((2 : ℝ) ^ 2048) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) 2048]
  -- `L = log r ≥ 1419`
  set L : ℝ := Real.log r with hLdef
  have hL : (1419 : ℝ) ≤ L := by
    have h1 : Real.log ((2 : ℝ) ^ 2048) ≤ L := Real.log_le_log (by positivity) hrR
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    norm_num at h1 this ⊢
    nlinarith
  -- `M = ⌊L⌋₊`
  set M : ℕ := ⌊L⌋₊ with hMdef
  have hMle : (M : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hLM : L < (M : ℝ) + 1 := Nat.lt_floor_add_one L
  have hM : 1419 ≤ M := Nat.le_floor (by exact_mod_cast hL)
  have hMR : (1419 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set N : ℕ := M - 1 with hNdef
  have hN : 1418 ≤ N := by omega
  have hNR : (1418 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNM : (N : ℝ) + 1 = (M : ℝ) := by
    have : N + 1 = M := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  set v : ℝ := Real.log (N : ℝ) with hvdef
  have hv : (72 / 10 : ℝ) ≤ v := by
    rw [hvdef]
    have h := log_ge_of_two_pow_le (k := 10) (x := (N : ℝ)) (by norm_num; linarith)
    have h2 := Real.log_two_gt_d9
    have h3 : (1024 : ℝ) / (N : ℝ) ≤ 1024 / 1418 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNR
    norm_num at h h2 h3 ⊢
    nlinarith
  have hv0 : (0 : ℝ) < v := by linarith
  -- the prime product
  set P : ℝ := ∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹) with hPdef
  have hPv : Real.exp (-(609 / 1000) - (4387 / 1000 / v + 1 / 1418)) ≤ P * v :=
    prod_primesBelow_ge hM (by rw [hvdef, hNdef])
  have hA : (2917 / 10000 : ℝ) ≤ Real.exp (-(609 / 1000) - (4387 / 1000 / v + 1 / 1418)) := by
    refine le_trans exp_neg_c_ge (Real.exp_le_exp.mpr ?_)
    have h1 : (4387 / 1000 : ℝ) / v ≤ 4387 / 1000 / (72 / 10) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hv
    norm_num at h1 ⊢
    linarith
  have hP : (2917 / 10000 : ℝ) / v ≤ P := by
    rw [div_le_iff₀ hv0]
    linarith
  -- the large prime factors
  set k : ℕ := (r.primeFactors.filter (fun p => M ≤ p)).card with hkdef
  have hkM : (M : ℝ) ^ k ≤ (r : ℝ) := by exact_mod_cast pow_card_filter_le (M := M) hr0
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM : v ≤ Real.log (M : ℝ) := by
    rw [hvdef]; exact Real.log_le_log (by linarith) (by linarith)
  have hkv : (k : ℝ) * v ≤ L := by
    have h1 : Real.log ((M : ℝ) ^ k) ≤ L := Real.log_le_log (by positivity) hkM
    rw [Real.log_pow] at h1
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hkMle : (k : ℝ) / (M : ℝ) ≤ 1015 / 1000 / v := by
    rw [div_le_div_iff₀ hMpos hv0]
    have h1 : (k : ℝ) * v ≤ L := hkv
    have h2 : L < (N : ℝ) + 2 := by linarith
    have h3 : (N : ℝ) ≤ (M : ℝ) := by linarith
    nlinarith [hNR, hv0, Nat.cast_nonneg (α := ℝ) k]
  -- split bound
  have hsplit := totient_ratio_ge_split (r := r) (M := M) hr0 (by omega)
  have hfac : (1 : ℝ) - 1015 / 1000 / v ≤ 1 - (k : ℝ) / (M : ℝ) := by linarith
  have hfac0 : (0 : ℝ) ≤ 1 - 1015 / 1000 / v := by
    have : (1015 / 1000 : ℝ) / v ≤ 1015 / 1000 / (72 / 10) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hv
    norm_num at this ⊢
    linarith
  have hmain : ((2917 / 10000 : ℝ) / v) * (1 - 1015 / 1000 / v) ≤ (Nat.totient r : ℝ) / r :=
    le_trans (mul_le_mul hP hfac hfac0 (le_trans (by positivity) hP)) hsplit
  -- the denominator
  have hD : v + 35 / 100 ≤ Real.log ((Nat.log2 (r + 1) : ℝ) + 1) := by
    have hJ : ((r : ℝ) + 1) < 2 ^ (Nat.log2 (r + 1) + 1) := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (r + 1)
      rw [← Nat.log2_eq_log_two] at this
      exact_mod_cast this
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hJlog : L < ((Nat.log2 (r + 1) : ℝ) + 1) * Real.log 2 := by
      have h1 : L ≤ Real.log ((r : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
      have h2 : Real.log ((r : ℝ) + 1) < Real.log ((2 : ℝ) ^ (Nat.log2 (r + 1) + 1)) :=
        Real.log_lt_log (by linarith) hJ
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have hJpos : (0 : ℝ) < (Nat.log2 (r + 1) : ℝ) + 1 := by positivity
    have hge : L / Real.log 2 ≤ (Nat.log2 (r + 1) : ℝ) + 1 := by
      rw [div_le_iff₀ hlog2]; linarith
    have hstep : Real.log (L / Real.log 2) ≤ Real.log ((Nat.log2 (r + 1) : ℝ) + 1) :=
      Real.log_le_log (by positivity) hge
    have hdiv : Real.log (L / Real.log 2) = Real.log L - Real.log (Real.log 2) := by
      rw [Real.log_div (by linarith) hlog2.ne']
    have hlogL : v ≤ Real.log L := by
      rw [hvdef]; exact Real.log_le_log (by linarith) (by linarith)
    have := neg_log_log_two_ge
    rw [hdiv] at hstep
    linarith
  -- assemble
  refine le_trans ?_ hmain
  have hDpos : (0 : ℝ) < Real.log ((Nat.log2 (r + 1) : ℝ) + 1) := by linarith
  have hnum : 1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ 1 / (4 * (v + 35 / 100)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  refine le_trans hnum ?_
  rw [div_le_iff₀ (by positivity)]
  have hid : (2917 / 10000 : ℝ) / v * (1 - 1015 / 1000 / v) * (4 * (v + 35 / 100))
      = (2917 / 10000 * 4 * ((v - 1015 / 1000) * (v + 35 / 100))) / v ^ 2 := by
    field_simp
  rw [hid, le_div_iff₀ (by positivity : (0 : ℝ) < v ^ 2)]
  nlinarith [hv, hv0]

/-- **The totient bound, unconditionally.**  For every `0 < r`,

    1 / (4 · log (log₂ (r+1) + 1)) ≤ φ(r) / r.

Below `2 ^ 2048` this is the finite case split of `Math/TotientBounds.lean`; above it, the
Mertens argument of this file. -/
theorem totient_ratio_loglog {r : ℕ} (hr : 0 < r) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  rcases lt_or_ge r (2 ^ 2048) with h | h
  · exact totient_ratio_loglog_of_lt hr h
  · exact totient_ratio_loglog_of_ge h

/-- The `N`-indexed form consumed by `shor_totient_ratio_lower_bound`. -/
theorem shor_totient_ratio {r N : ℕ} (hr : 0 < r) (hrN : r < N) :
    1 / (4 * Real.log ((Nat.log2 N : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine le_trans ?_ (totient_ratio_loglog hr)
  have hmono : Nat.log2 (r + 1) ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  have hL1 : 1 ≤ Nat.log2 (r + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le Nat.one_lt_two (by norm_num; omega)
  have hL1R : (1 : ℝ) ≤ (Nat.log2 (r + 1) : ℝ) := by exact_mod_cast hL1
  have hcast : ((Nat.log2 (r + 1) : ℝ) + 1) ≤ ((Nat.log2 N : ℝ) + 1) := by
    have : (Nat.log2 (r + 1) : ℝ) ≤ (Nat.log2 N : ℝ) := by exact_mod_cast hmono
    linarith
  have hlogpos : 0 < Real.log ((Nat.log2 (r + 1) : ℝ) + 1) := Real.log_pos (by linarith)
  have hlogmono : Real.log ((Nat.log2 (r + 1) : ℝ) + 1)
      ≤ Real.log ((Nat.log2 N : ℝ) + 1) :=
    Real.log_le_log (by linarith) hcast
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

end Shor
