import ForShor.ShorVerification.Implementation.Shor.Math.OrderFindingAnalysis
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A `1 / log log` lower bound for the totient ratio

This file proves, for every order `r` below `2 ^ 2048`,

    1 / (4 · log (log₂ (r+1) + 1)) ≤ φ(r) / r,

and the `N`-indexed form `shor_totient_ratio_of_lt` used by
`Proofs/NaiveShor/GoodOutcomeMassLowerBound.lean`.  This is the `Ω(1 / log log N)`
Mertens-type bound behind the success constant `κ = 1/π²`; the elementary chain
in `OrderFindingAnalysis.lean` only gives `Ω(1 / log N)`.

## Method

`φ(r)/r = ∏_{p ∣ r} (1 - 1/p)`.  Fix a threshold `M` and split the prime
divisors of `r` at `M`:

* the ones below `M` form a subset of the primes below `M`, and each factor lies
  in `[0,1]`, so they contribute at least `∏_{p < M, p prime} (1 - 1/p)`;
* if `k` of them are `≥ M` then they contribute at least `(1 - 1/M)^k ≥ 1 - k/M`
  (Bernoulli), and `M ^ k ≤ r`, so `k` is bounded by a pure `ℕ` computation.

For `r ∈ [2^a, 2^b)` this gives `φ(r)/r ≥ P(M) · (1 - K/M)` with `K` the largest
`k` with `M ^ k < 2 ^ b`, and the target `1 / (4 log (a+1))` is a rational bound
once `log (a+1)` is bounded below.  Eight dyadic regions cover `[255, 2^2048)`;
below `255` the elementary `totient_ratio_ge_inv_log2_succ` already suffices.

Logarithms are bounded below by `log x ≥ k·log 2 + (1 - 2^k/x)` for `2^k ≤ x`
(`log_ge_of_two_pow_le`), with `Real.log_two_gt_d9` for `log 2`.

The complementary range `2 ^ 2048 ≤ r` is `TotientBoundsLarge.lean`, which evaluates
the prime product below the threshold by Mertens' third theorem.
-/

namespace Shor

open Finset

-- The dyadic regions compare `2 ^ 2048` against `M ^ (K+1)`, far above the
-- default `exponentiation.threshold` of 256, and the `decide`s that evaluate
-- `Nat.primesBelow M` for `M` in the hundreds need a deeper recursion limit.
set_option exponentiation.threshold 5000
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-! ### Elementary bounds on `1 - 1/p` -/

private lemma one_sub_inv_nonneg {p : ℕ} (hp : 1 ≤ p) : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
  have h : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have := inv_le_one_of_one_le₀ h
  linarith

private lemma one_sub_inv_le_one (p : ℕ) : (1 : ℝ) - (p : ℝ)⁻¹ ≤ 1 := by
  have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  linarith

lemma prod_primesBelow_nonneg (M : ℕ) :
    0 ≤ ∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹) :=
  Finset.prod_nonneg fun _ hi =>
    one_sub_inv_nonneg (Nat.Prime.one_lt (Nat.prime_of_mem_primesBelow hi)).le

/-! ### Logarithm lower bounds -/

/-- `log x ≥ k·log 2 + (1 − 2^k / x)` whenever `2^k ≤ x`: split off the largest
power of two below `x` and use `1 - y⁻¹ ≤ log y` on the remainder. -/
lemma log_ge_of_two_pow_le {k : ℕ} {x : ℝ} (hx : (2 : ℝ) ^ k ≤ x) :
    (k : ℝ) * Real.log 2 + (1 - 2 ^ k / x) ≤ Real.log x := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le h2k hx
  have hq : 0 < x / 2 ^ k := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at h
  have hsplit : Real.log x = (k : ℝ) * Real.log 2 + Real.log (x / 2 ^ k) := by
    rw [Real.log_div hx0.ne' h2k.ne', Real.log_pow]
    ring
  rw [hsplit]
  linarith

/-- `log_ge_of_two_pow_le` with `log 2` replaced by the rational
`Real.log_two_gt_d9` bound, so the side condition is `norm_num`-checkable. -/
private lemma log_ge_aux {k : ℕ} {x q : ℝ} (hx : (2 : ℝ) ^ k ≤ x)
    (hq : q ≤ (k : ℝ) * (6931471803 / 10000000000) + (1 - 2 ^ k / x)) :
    q ≤ Real.log x := by
  have h := log_ge_of_two_pow_le hx
  have h2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-! ### The product formula and the split at a threshold -/

/-- `φ(r)/r` as a product over the prime divisors of `r` (Euler's product
formula, transported from `ℚ`). -/
lemma totient_ratio_eq_prod {r : ℕ} (hr : 0 < r) :
    (Nat.totient r : ℝ) / r = ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have h := Nat.totient_eq_mul_prod_factors r
  have hQ : (Nat.totient r : ℚ) / r = ∏ p ∈ r.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [h]; field_simp
  have := congrArg (fun q : ℚ => (q : ℝ)) hQ
  push_cast at this
  exact this

/-- The prime divisors of `r` that are at least `M` contribute a factor `M ^ k`
to `r`, so there are at most `log r / log M` of them. -/
lemma pow_card_filter_le {r M : ℕ} (hr : 0 < r) :
    M ^ ((r.primeFactors.filter (fun p => M ≤ p)).card) ≤ r := by
  classical
  have h1 : M ^ ((r.primeFactors.filter (fun p => M ≤ p)).card)
      ≤ ∏ p ∈ r.primeFactors.filter (fun p => M ≤ p), p :=
    Finset.pow_card_le_prod _ _ _ (fun x hx => (Finset.mem_filter.mp hx).2)
  have h2 : ∏ p ∈ r.primeFactors.filter (fun p => M ≤ p), p ≤ ∏ p ∈ r.primeFactors, p :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
      (fun i hi _ => Nat.pos_of_mem_primeFactors hi)
  exact le_trans h1 (le_trans h2 (Nat.le_of_dvd hr (Nat.prod_primeFactors_dvd r)))

/-- **The split lemma.**  At a natural threshold `M ≥ 2`, the prime divisors of
`r` below `M` contribute at least the full product over the primes below `M`,
and the `k` divisors at least `M` contribute at least `1 - k/M`. -/
lemma totient_ratio_ge_split {r M : ℕ} (hr : 0 < r) (hM : 2 ≤ M) :
    (∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹)) *
        (1 - ((r.primeFactors.filter (fun p => M ≤ p)).card : ℝ) / M)
      ≤ (Nat.totient r : ℝ) / r := by
  classical
  set f : ℕ → ℝ := fun p => 1 - (p : ℝ)⁻¹ with hfdef
  set large := r.primeFactors.filter (fun p => M ≤ p) with hlarge
  set small := r.primeFactors.filter (fun p => ¬ M ≤ p) with hsmall
  have hM0 : (0 : ℝ) < M := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hPnn : 0 ≤ ∏ p ∈ Nat.primesBelow M, f p := prod_primesBelow_nonneg M
  have hsplit : (∏ p ∈ large, f p) * (∏ p ∈ small, f p) = ∏ p ∈ r.primeFactors, f p :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hsub : small ⊆ Nat.primesBelow M := by
    intro p hp
    rw [hsmall, Finset.mem_filter] at hp
    exact Nat.mem_primesBelow.mpr ⟨Nat.lt_of_not_le hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  have hsmallnn : 0 ≤ ∏ p ∈ small, f p :=
    Finset.prod_nonneg fun i hi =>
      one_sub_inv_nonneg (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hi).1)
  have hsmallbound : (∏ p ∈ Nat.primesBelow M, f p) ≤ ∏ p ∈ small, f p := by
    have hsd := Finset.prod_sdiff (f := f) hsub
    have h1 : (∏ p ∈ Nat.primesBelow M \ small, f p) ≤ 1 :=
      Finset.prod_le_one₀
        (fun i hi => one_sub_inv_nonneg
          (Nat.Prime.one_lt (Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hi).1)).le)
        (fun i _ => one_sub_inv_le_one i)
    calc (∏ p ∈ Nat.primesBelow M, f p)
        = (∏ p ∈ Nat.primesBelow M \ small, f p) * (∏ p ∈ small, f p) := hsd.symm
      _ ≤ 1 * (∏ p ∈ small, f p) := mul_le_mul_of_nonneg_right h1 hsmallnn
      _ = ∏ p ∈ small, f p := one_mul _
  have hlargebound : 1 - ((large.card : ℝ)) / M ≤ ∏ p ∈ large, f p := by
    have hconst : ∀ i ∈ large, (1 - (M : ℝ)⁻¹) ≤ f i := by
      intro i hi
      have hMi : M ≤ i := (Finset.mem_filter.mp hi).2
      have hr' : (M : ℝ) ≤ i := by exact_mod_cast hMi
      have := inv_anti₀ hM0 hr'
      simp only [hfdef]
      linarith
    have hpow : (1 - (M : ℝ)⁻¹) ^ large.card ≤ ∏ p ∈ large, f p := by
      calc (1 - (M : ℝ)⁻¹) ^ large.card = ∏ _p ∈ large, (1 - (M : ℝ)⁻¹) :=
            (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ large, f p :=
            Finset.prod_le_prod₀ (fun _ _ => one_sub_inv_nonneg (p := M) (by omega)) hconst
    have hbern : 1 - (large.card : ℝ) / M ≤ (1 - (M : ℝ)⁻¹) ^ large.card := by
      have hMge : (-2 : ℝ) ≤ -(M : ℝ)⁻¹ := by
        have h0 : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
        have h1 : (M : ℝ)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]; right; exact_mod_cast hM.trans' (by norm_num)
        linarith
      have h := one_add_mul_le_pow hMge large.card
      have heq : (1 : ℝ) + (large.card : ℝ) * (-(M : ℝ)⁻¹) = 1 - (large.card : ℝ) / M := by
        field_simp
        ring
      have heq2 : (1 : ℝ) + -(M : ℝ)⁻¹ = 1 - (M : ℝ)⁻¹ := by ring
      rw [heq, heq2] at h
      exact h
    linarith
  rw [totient_ratio_eq_prod hr, ← hsplit]
  rcases le_or_gt 0 (1 - (large.card : ℝ) / M) with hpos | hneg
  · calc (∏ p ∈ Nat.primesBelow M, f p) * (1 - (large.card : ℝ) / M)
        ≤ (∏ p ∈ small, f p) * (∏ p ∈ large, f p) :=
          mul_le_mul hsmallbound hlargebound hpos hsmallnn
      _ = (∏ p ∈ large, f p) * (∏ p ∈ small, f p) := mul_comm _ _
  · refine le_trans (mul_nonpos_of_nonneg_of_nonpos hPnn hneg.le) ?_
    rw [hsplit]
    exact Finset.prod_nonneg fun i hi =>
      one_sub_inv_nonneg (Nat.pos_of_mem_primeFactors hi)

/-! ### Evaluating the product over the primes below `M` -/

/-- The product over the primes below `M` as a ratio of two naturals, so that a
rational lower bound for it is two `decide`s and a `norm_num`. -/
lemma prod_primesBelow_eq_div (M : ℕ) :
    ∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹)
      = ((∏ p ∈ Nat.primesBelow M, (p - 1) : ℕ) : ℝ)
          / ((∏ p ∈ Nat.primesBelow M, p : ℕ) : ℝ) := by
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : 1 ≤ p := (Nat.prime_of_mem_primesBelow hp).one_lt.le
  have hp0 : (p : ℝ) ≠ 0 := by
    have : 0 < p := hp1
    positivity
  rw [Nat.cast_sub hp1]
  push_cast
  field_simp

/-- A rational lower bound for `∏_{p < M, p prime} (1 - 1/p)`. -/
lemma le_prod_primesBelow {M A B : ℕ} {c : ℝ}
    (hA : ∏ p ∈ Nat.primesBelow M, (p - 1) = A)
    (hB : ∏ p ∈ Nat.primesBelow M, p = B)
    (hB0 : (0 : ℝ) < (B : ℝ)) (hcB : c * (B : ℝ) ≤ (A : ℝ)) :
    c ≤ ∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹) := by
  rw [prod_primesBelow_eq_div, hA, hB, le_div_iff₀ hB0]
  exact hcB

/-! ### One dyadic region -/

/-- `φ(r)/r ≥ c · (1 - K/M)` for `r < 2 ^ b`, where `c` bounds the product over
the primes below `M` and `K` is any exponent with `2 ^ b ≤ M ^ (K+1)`. -/
lemma totient_ratio_region {r M K b : ℕ} {c : ℝ}
    (hr : 0 < r) (hM : 2 ≤ M) (hKM : K ≤ M)
    (hb : r < 2 ^ b) (hK : 2 ^ b ≤ M ^ (K + 1))
    (hc : c ≤ ∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹)) :
    c * (1 - (K : ℝ) / M) ≤ (Nat.totient r : ℝ) / r := by
  classical
  have hk : (r.primeFactors.filter (fun p => M ≤ p)).card ≤ K := by
    by_contra hcon
    push Not at hcon
    have h1 : M ^ (K + 1) ≤ M ^ ((r.primeFactors.filter (fun p => M ≤ p)).card) :=
      Nat.pow_le_pow_right (by omega) hcon
    exact absurd (le_trans h1 (pow_card_filter_le (r := r) (M := M) hr))
      (not_le.mpr (lt_of_lt_of_le hb hK))
  have hM0 : (0 : ℝ) < M := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hkR : ((r.primeFactors.filter (fun p => M ≤ p)).card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hk
  have hstep : (1 : ℝ) - (K : ℝ) / M
      ≤ 1 - ((r.primeFactors.filter (fun p => M ≤ p)).card : ℝ) / M := by
    have : ((r.primeFactors.filter (fun p => M ≤ p)).card : ℝ) / M ≤ (K : ℝ) / M := by
      gcongr
    linarith
  have hKMR : (K : ℝ) ≤ (M : ℝ) := by exact_mod_cast hKM
  have hnn : (0 : ℝ) ≤ 1 - (K : ℝ) / M := by
    rw [sub_nonneg, div_le_one hM0]; exact hKMR
  exact le_trans (mul_le_mul hc hstep hnn (prod_primesBelow_nonneg M))
    (totient_ratio_ge_split hr hM)

/-- The shape every region instance below is an instance of. -/
private lemma region_bound {r a b M K : ℕ} {c q x : ℝ}
    (hr : 0 < r) (ha : 2 ^ a ≤ r + 1) (hb : r < 2 ^ b)
    (hM : 2 ≤ M) (hKM : K ≤ M) (hK : 2 ^ b ≤ M ^ (K + 1))
    (hc : c ≤ ∏ p ∈ Nat.primesBelow M, (1 - (p : ℝ)⁻¹))
    (hax : (a : ℝ) + 1 = x) (hq : q ≤ Real.log x) (hq0 : 0 < q)
    (hfinal : 1 / (4 * q) ≤ c * (1 - (K : ℝ) / M)) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  subst hax
  refine le_trans ?_ (le_trans hfinal (totient_ratio_region hr hM hKM hb hK hc))
  have halog : a ≤ Nat.log2 (r + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le Nat.one_lt_two ha
  have hcast : ((a : ℝ) + 1) ≤ ((Nat.log2 (r + 1) : ℝ) + 1) := by
    have : (a : ℝ) ≤ (Nat.log2 (r + 1) : ℝ) := by exact_mod_cast halog
    linarith
  have hposa : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hlogmono : Real.log ((a : ℝ) + 1) ≤ Real.log ((Nat.log2 (r + 1) : ℝ) + 1) :=
    Real.log_le_log hposa hcast
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-! ### Region A: `r < 255` -/

private lemma log_two_ge : (1 / 2 : ℝ) ≤ Real.log 2 :=
  log_ge_aux (k := 1) (by norm_num) (by norm_num)
private lemma log_three_ge : (3 / 4 : ℝ) ≤ Real.log 3 :=
  log_ge_aux (k := 1) (by norm_num) (by norm_num)
private lemma log_four_ge : (1 : ℝ) ≤ Real.log 4 :=
  log_ge_aux (k := 2) (by norm_num) (by norm_num)
private lemma log_five_ge : (5 / 4 : ℝ) ≤ Real.log 5 :=
  log_ge_aux (k := 2) (by norm_num) (by norm_num)
private lemma log_six_ge : (3 / 2 : ℝ) ≤ Real.log 6 :=
  log_ge_aux (k := 2) (by norm_num) (by norm_num)
private lemma log_seven_ge : (7 / 4 : ℝ) ≤ Real.log 7 :=
  log_ge_aux (k := 2) (by norm_num) (by norm_num)
private lemma log_eight_ge : (2 : ℝ) ≤ Real.log 8 :=
  log_ge_aux (k := 3) (by norm_num) (by norm_num)

/-- `L + 1 ≤ 4 · log (L + 1)` for `1 ≤ L ≤ 7`.  The two tight cases are `L = 6`
(`log 7 ≥ 1.75`) and `L = 7` (`log 8 ≥ 2`); both hold with about 4% to spare. -/
private lemma log_succ_bound {L : ℕ} (hL1 : 1 ≤ L) (hL7 : L ≤ 7) :
    ((L : ℝ) + 1) ≤ 4 * Real.log ((L : ℝ) + 1) := by
  interval_cases L <;> norm_num
  · linarith [log_two_ge]
  · linarith [log_three_ge]
  · linarith [log_four_ge]
  · linarith [log_five_ge]
  · linarith [log_six_ge]
  · linarith [log_seven_ge]
  · linarith [log_eight_ge]

/-- Region A: below `255` the elementary bound `1/(log₂(r+1) + 1) ≤ φ(r)/r` from
`OrderFindingAnalysis.lean` already beats `1 / (4 log (log₂ (r+1) + 1))`. -/
private lemma region_A {r : ℕ} (hr : 0 < r) (hr2 : r < 255) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  have hbase := totient_ratio_ge_inv_log2_succ hr (show r < r + 1 by omega)
  have hL1 : 1 ≤ Nat.log2 (r + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le Nat.one_lt_two (by norm_num; omega)
  have hL7 : Nat.log2 (r + 1) ≤ 7 := by
    rw [Nat.log2_eq_log_two]
    have h : Nat.log 2 (r + 1) < 8 := Nat.log_lt_of_lt_pow (by omega) (by norm_num; omega)
    omega
  have hnum := log_succ_bound hL1 hL7
  have hcast : (((Nat.log2 (r + 1) + 1 : ℕ)) : ℝ) = (Nat.log2 (r + 1) : ℝ) + 1 := by
    push_cast; ring
  rw [hcast] at hbase
  exact le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) hbase

/-- Region B1: `255 ≤ r < 2 ^ 16`.  Threshold `M = 17` (6 primes below it);
at most `K = 3` prime factors of `r` are `≥ 17`, since `17 ^ 4 ≥ 2 ^ 16`.
Margin over the target `1 / (4 log 9)`: about 1.3. -/
private lemma region_B1 {r : ℕ} (hr : 0 < r) (h1 : 255 ≤ r) (h2 : r < 2 ^ 16) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 8) (b := 16) (M := 17) (K := 3) (c := 959/5000)
    (q := 4381/2000) (x := 9) hr (by norm_num; omega) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 5760)
      (B := 30030)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 3) (by norm_num) (by norm_num)

/-- Region B2: `2 ^ 16 ≤ r < 2 ^ 32`.  Threshold `M = 23` (8 primes below it);
at most `K = 7` prime factors of `r` are `≥ 23`, since `23 ^ 8 ≥ 2 ^ 32`.
Margin over the target `1 / (4 log 17)`: about 1.3. -/
private lemma region_B2 {r : ℕ} (hr : 0 < r) (h1 : 2 ^ 16 ≤ r) (h2 : r < 2 ^ 32) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 16) (b := 32) (M := 23) (K := 7) (c := 8551/50000)
    (q := 14157/5000) (x := 17) hr (Nat.le_succ_of_le h1) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 1658880)
      (B := 9699690)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 4) (by norm_num) (by norm_num)

/-- Region B3: `2 ^ 32 ≤ r < 2 ^ 64`.  Threshold `M = 31` (10 primes below it);
at most `K = 12` prime factors of `r` are `≥ 31`, since `31 ^ 13 ≥ 2 ^ 64`.
Margin over the target `1 / (4 log 33)`: about 1.3. -/
private lemma region_B3 {r : ℕ} (hr : 0 < r) (h1 : 2 ^ 32 ≤ r) (h2 : r < 2 ^ 64) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 32) (b := 64) (M := 31) (K := 12) (c := 7897/50000)
    (q := 437/125) (x := 33) hr (Nat.le_succ_of_le h1) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 1021870080)
      (B := 6469693230)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 5) (by norm_num) (by norm_num)

/-- Region B4: `2 ^ 64 ≤ r < 2 ^ 128`.  Threshold `M = 53` (15 primes below it);
at most `K = 22` prime factors of `r` are `≥ 53`, since `53 ^ 23 ≥ 2 ^ 128`.
Margin over the target `1 / (4 log 65)`: about 1.3. -/
private lemma region_B4 {r : ℕ} (hr : 0 < r) (h1 : 2 ^ 64 ≤ r) (h2 : r < 2 ^ 128) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 64) (b := 128) (M := 53) (K := 22) (c := 1387/10000)
    (q := 20871/5000) (x := 65) hr (Nat.le_succ_of_le h1) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 85287729364992000)
      (B := 614889782588491410)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 6) (by norm_num) (by norm_num)

/-- Region B5: `2 ^ 128 ≤ r < 2 ^ 256`.  Threshold `M = 89` (23 primes below it);
at most `K = 39` prime factors of `r` are `≥ 89`, since `89 ^ 40 ≥ 2 ^ 256`.
Margin over the target `1 / (4 log 129)`: about 1.3. -/
private lemma region_B5 {r : ℕ} (hr : 0 < r) (h1 : 2 ^ 128 ≤ r) (h2 : r < 2 ^ 256) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 128) (b := 256) (M := 89) (K := 39) (c := 2459/20000)
    (q := 48597/10000) (x := 129) hr (Nat.le_succ_of_le h1) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 32836137597980331433839820800000)
      (B := 267064515689275851355624017992790)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 7) (by norm_num) (by norm_num)

/-- Region B6: `2 ^ 256 ≤ r < 2 ^ 512`.  Threshold `M = 151` (35 primes below it);
at most `K = 70` prime factors of `r` are `≥ 151`, since `151 ^ 71 ≥ 2 ^ 512`.
Margin over the target `1 / (4 log 257)`: about 1.3. -/
private lemma region_B6 {r : ℕ} (hr : 0 < r) (h1 : 2 ^ 256 ≤ r) (h2 : r < 2 ^ 512) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 256) (b := 512) (M := 151) (K := 70) (c := 11061/100000)
    (q := 5549/1000) (x := 257) hr (Nat.le_succ_of_le h1) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 165062110921422523175104166476600499887194872217600000000)
      (B := 1492182350939279320058875736615841068547583863326864530410)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 8) (by norm_num) (by norm_num)

/-- Region B7: `2 ^ 512 ≤ r < 2 ^ 1024`.  Threshold `M = 269` (56 primes below it);
at most `K = 126` prime factors of `r` are `≥ 269`, since `269 ^ 127 ≥ 2 ^ 1024`.
Margin over the target `1 / (4 log 513)`: about 1.3. -/
private lemma region_B7 {r : ℕ} (hr : 0 < r) (h1 : 2 ^ 512 ≤ r) (h2 : r < 2 ^ 1024) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 512) (b := 1024) (M := 269) (K := 126) (c := 4979/50000)
    (q := 31201/5000) (x := 513) hr (Nat.le_succ_of_le h1) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 432570008148554189380498305896735347241193418779905246241879383065974494032118303372083200000000000000000)
      (B := 4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 9) (by norm_num) (by norm_num)

/-- Region B8: `2 ^ 1024 ≤ r < 2 ^ 2048`.  Threshold `M = 479` (91 primes below it);
at most `K = 230` prime factors of `r` are `≥ 479`, since `479 ^ 231 ≥ 2 ^ 2048`.
Margin over the target `1 / (4 log 1025)`: about 1.3. -/
private lemma region_B8 {r : ℕ} (hr : 0 < r) (h1 : 2 ^ 1024 ≤ r) (h2 : r < 2 ^ 2048) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine region_bound (a := 1024) (b := 2048) (M := 479) (K := 230) (c := 4517/50000)
    (q := 17331/2500) (x := 1025) hr (Nat.le_succ_of_le h1) h2 (by norm_num) (by norm_num) (by norm_num) ?_
    (by norm_num) ?_ (by norm_num) (by norm_num)
  · exact le_prod_primesBelow (A := 197352245467874955087499571094350014063796041528213110153502914681530497486969760522206714275070672331583951034243189125939421587302642593898365306698574290888780310118400000000000000000000000000)
      (B := 2184388827958183606469810778001988127598001347644753877628597514732473285653996655943128229044607914390526120724168070692914015911034911541522425303161947419103871515655013288351117524591190137770)
      (by decide) (by decide) (by norm_num) (by norm_num)
  · exact log_ge_aux (k := 10) (by norm_num) (by norm_num)

/-! ### Assembly below `2 ^ 2048` -/

/-- **The totient bound below `2 ^ 2048`.**  For every order `r` with
`0 < r < 2 ^ 2048`,

    1 / (4 · log (log₂ (r+1) + 1)) ≤ φ(r) / r.

Nine cases: `r < 255` elementarily, then the eight dyadic regions. -/
theorem totient_ratio_loglog_of_lt {r : ℕ} (hr : 0 < r) (hr2 : r < 2 ^ 2048) :
    1 / (4 * Real.log ((Nat.log2 (r + 1) : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  rcases lt_or_ge r 255 with h | h0
  · exact region_A hr h
  rcases lt_or_ge r (2 ^ 16) with h | h1
  · exact region_B1 hr h0 h
  rcases lt_or_ge r (2 ^ 32) with h | h2
  · exact region_B2 hr h1 h
  rcases lt_or_ge r (2 ^ 64) with h | h3
  · exact region_B3 hr h2 h
  rcases lt_or_ge r (2 ^ 128) with h | h4
  · exact region_B4 hr h3 h
  rcases lt_or_ge r (2 ^ 256) with h | h5
  · exact region_B5 hr h4 h
  rcases lt_or_ge r (2 ^ 512) with h | h6
  · exact region_B6 hr h5 h
  rcases lt_or_ge r (2 ^ 1024) with h | h7
  · exact region_B7 hr h6 h
  exact region_B8 hr h7 hr2

/-- The `N`-indexed form consumed by `shor_totient_ratio_lower_bound`: `log₂` and
`log` are monotone and `r + 1 ≤ N`, so the `N` denominator is the larger one. -/
theorem shor_totient_ratio_of_lt {r N : ℕ} (hr : 0 < r) (hrN : r < N)
    (hr2 : r < 2 ^ 2048) :
    1 / (4 * Real.log ((Nat.log2 N : ℝ) + 1)) ≤ (Nat.totient r : ℝ) / r := by
  refine le_trans ?_ (totient_ratio_loglog_of_lt hr hr2)
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
  have hlogpos : 0 < Real.log ((Nat.log2 (r + 1) : ℝ) + 1) :=
    Real.log_pos (by linarith)
  have hlogmono : Real.log ((Nat.log2 (r + 1) : ℝ) + 1)
      ≤ Real.log ((Nat.log2 N : ℝ) + 1) :=
    Real.log_le_log (by linarith) hcast
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

end Shor
