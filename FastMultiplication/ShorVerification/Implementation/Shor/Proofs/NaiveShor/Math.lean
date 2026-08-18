import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import FastMultiplication.ShorVerification.Framework.Math.ShorDefinition
import FastMultiplication.ShorVerification.Framework.AbstractMachine.Gates

/-!
# NaiveShor — purely mathematical lemmas

Number-theory, Fourier / geometric-sum, and counting lemmas backing the ideal
order-finding good-outcome analysis.  Their import closure is Mathlib plus the
project's semantics-free vocabulary (`ord`, `qftPhase`, `GoodOutcome`) — no
`QSemantics`, `eval`, or measurement.
-/

namespace Shor

noncomputable def goodOutcomeIndicator (o Q r : ℕ) : ℝ := by
  classical
  exact if GoodOutcome o Q r then 1 else 0

lemma ord_pos_of_gcd
    (a N : ℕ)
    (hgcd : Nat.gcd a N = 1) :
    0 < ord a N hgcd := by
  unfold ord
  exact orderOf_pos
    (ZMod.unitOfCoprime a
      ((Nat.coprime_iff_gcd_eq_one).2 hgcd))

lemma pow_ord_mod_eq_one
    (a N : ℕ)
    (hgcd : Nat.gcd a N = 1)
    (hN : 1 < N) :
    (a ^ ord a N hgcd) % N = 1 := by
  let u : (ZMod N)ˣ :=
    ZMod.unitOfCoprime a
      ((Nat.coprime_iff_gcd_eq_one).2 hgcd)

  have hu : u ^ orderOf u = 1 :=
    pow_orderOf_eq_one u

  have hz :
      ((a ^ ord a N hgcd : ℕ) : ZMod N) =
        ((1 : ℕ) : ZMod N) := by
    have hcoe :=
      congrArg (fun z : (ZMod N)ˣ => (z : ZMod N)) hu
    have hunit :
        ((u : ZMod N) ^ orderOf u) = 1 :=
      hcoe
    have hcast :
        ((a : ZMod N) ^ ord a N hgcd) = 1 := by
      simpa [u, ord, ZMod.coe_unitOfCoprime] using hunit
    simpa [Nat.cast_pow] using hcast

  have hmod :
      (a ^ ord a N hgcd) % N = 1 % N :=
    (ZMod.natCast_eq_natCast_iff'
      (a ^ ord a N hgcd) 1 N).1 hz

  have hone_lt : 1 < N := hN
  simpa [Nat.mod_eq_of_lt hone_lt] using hmod

lemma ord_le_of_pow_mod_eq_one
    (a N d : ℕ)
    (hgcd : Nat.gcd a N = 1)
    (hd : 0 < d)
    (hpow : (a ^ d) % N = 1) :
    ord a N hgcd ≤ d := by
  let u : (ZMod N)ˣ :=
    ZMod.unitOfCoprime a
      ((Nat.coprime_iff_gcd_eq_one).2 hgcd)

  have hz : ((a ^ d : ℕ) : ZMod N) = 1 := by
    calc
      ((a ^ d : ℕ) : ZMod N)
          = (((a ^ d) % N : ℕ) : ZMod N) := by
              symm
              exact ZMod.natCast_mod (a ^ d) N
      _ = 1 := by simp [hpow]

  have hu : u ^ d = 1 := by
    apply Units.ext
    simpa [u, ZMod.coe_unitOfCoprime] using hz

  have hle : orderOf u ≤ d :=
    orderOf_le_of_pow_eq_one hd hu

  simpa [u, ord] using hle

lemma pow_log2_two_mul_bounds
    (n : ℕ) (hn : 0 < n) :
    n < 2 ^ Nat.log2 (2 * n) ∧
    2 ^ Nat.log2 (2 * n) ≤ 2 * n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h2n0 : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) hn0

  rw [Nat.log2_eq_log_two]
  constructor

  · have hlog :
        Nat.log 2 (2 * n) = Nat.log 2 n + 1 := by
      calc
        Nat.log 2 (2 * n)
            = Nat.log 2 (n * 2) := by rw [Nat.mul_comm]
        _ = Nat.log 2 n + 1 :=
          Nat.log_mul_base (by norm_num) hn0

    rw [hlog]

    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self
        (b := 2) (by norm_num) n)

  · exact Nat.pow_log_le_self 2 h2n0

lemma modexp_step_arith
    (a N e y0 t : ℕ)
    (bit : Bool) :
    ((if bit then
        ((((a ^ (2 ^ e)) % N) * y0) % N)
      else
        y0) *
        a ^ (2 ^ (e + 1) * t)) % N
      =
    (y0 *
      a ^ (2 ^ e *
        ((if bit then 1 else 0) + 2 * t))) % N := by
  cases bit with
  | false =>
      change
        (y0 * a ^ (2 ^ (e + 1) * t)) % N =
          (y0 * a ^ (2 ^ e * (0 + 2 * t))) % N

      have hexp :
          2 ^ (e + 1) * t =
            2 ^ e * (2 * t) := by
        rw [pow_succ]
        ring

      simpa using
        congrArg
          (fun k => (y0 * a ^ k) % N)
          hexp

  | true =>
      change
        (((((a ^ (2 ^ e)) % N) * y0) % N) *
            a ^ (2 ^ (e + 1) * t)) % N
          =
        (y0 *
          a ^ (2 ^ e * (1 + 2 * t))) % N

      have hexp :
          2 ^ e * (1 + 2 * t) =
            2 ^ e + 2 ^ (e + 1) * t := by
        rw [pow_succ]
        ring

      rw [hexp]
      conv_rhs => rw [pow_add]

      let A : ℕ :=
        a ^ (2 ^ e)

      let B : ℕ :=
        a ^ (2 ^ (e + 1) * t)

      have hA :
          A % N ≡ A [MOD N] :=
        Nat.mod_modEq A N

      have hAy :
          (A % N) * y0 ≡ A * y0 [MOD N] :=
        hA.mul_right y0

      have hAyMod :
          ((A % N) * y0) % N ≡ A * y0 [MOD N] :=
        (Nat.mod_modEq ((A % N) * y0) N).trans hAy

      have hmain :
          ((A % N) * y0) % N * B ≡
            y0 * (A * B) [MOD N] := by
        exact
          (hAyMod.mul_right B).trans
            (by
              rw [Nat.ModEq]
              simp [Nat.mul_assoc, Nat.mul_comm])

      exact hmain

/-- Binary decomposition: a natural below `2^w` is the weighted sum of its
low `w` bits. Used to bridge the per-qubit exponent accumulation to
`toNat x b`. -/
lemma sum_two_pow_toNat_testBit :
    ∀ (w n : ℕ), n < 2 ^ w →
      ∑ i ∈ Finset.range w, 2 ^ i * (n.testBit i).toNat = n := by
  intro w
  induction w with
  | zero =>
      intro n h
      simp only [pow_zero, Nat.lt_one_iff] at h
      subst h
      simp
  | succ w ih =>
      intro n h
      rw [Finset.sum_range_succ']
      have hshift :
          (∑ i ∈ Finset.range w, 2 ^ (i + 1) * (n.testBit (i + 1)).toNat)
            = 2 * ∑ i ∈ Finset.range w, 2 ^ i * ((n / 2).testBit i).toNat := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.testBit_succ]
        ring
      have hlow : (2 : ℕ) ^ 0 * (n.testBit 0).toNat = n % 2 := by
        rw [Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
        · simp [h0]
        · simp [h1]
      have hdiv : n / 2 < 2 ^ w := by
        rw [pow_succ] at h
        omega
      rw [hshift, hlow, ih (n / 2) hdiv]
      omega

/--
The contribution from one residue class `s mod r` to output `o`.

The filter

    { t < Q | t % r = s }

is exactly Shor's substitution `t = j*r + s`.

Because the circuit uses IQFT, the QFT phase is conjugated.
-/
noncomputable def shorPeriodClassAmplitude
    (Q r s o : ℕ) : ℂ :=
  (1 / (Q : ℂ)) *
    ∑ t ∈ (Finset.range Q).filter (fun t => t % r = s),
      star (qftPhase Q t o)

/--
Shor's probability of observing exponent-register output `o`,
after summing over the `r` possible values of the modular-data register.

This is the marginal version of equations (5.5)--(5.7).
-/
noncomputable def shorPaperOutcomeProb
    (Q r o : ℕ) : ℝ :=
  ∑ s ∈ Finset.range r,
    ‖shorPeriodClassAmplitude Q r s o‖ ^ 2

lemma sum_range_group_by_mod
    {M : Type*}
    [AddCommMonoid M]
    (Q r : ℕ)
    (hr : 0 < r)
    (f : ℕ → ℕ → M) :
    (∑ t ∈ Finset.range Q,
        f (t % r) t)
      =
    ∑ s ∈ Finset.range r,
      ∑ t ∈
          (Finset.range Q).filter
            (fun t => t % r = s),
        f s t := by
  classical
  symm

  calc
    (∑ s ∈ Finset.range r,
        ∑ t ∈
            (Finset.range Q).filter
              (fun t => t % r = s),
          f s t)
        =
      ∑ s ∈ Finset.range r,
        ∑ t ∈ Finset.range Q,
          if t % r = s then
            f s t
          else
            0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_filter]

    _ =
      ∑ t ∈ Finset.range Q,
        ∑ s ∈ Finset.range r,
          if t % r = s then
            f s t
          else
            0 := by
      rw [Finset.sum_comm]

    _ =
      ∑ t ∈ Finset.range Q,
        f (t % r) t := by
      apply Finset.sum_congr rfl
      intro t ht

      have hm :
          t % r ∈ Finset.range r :=
        Finset.mem_range.mpr
          (Nat.mod_lt t hr)

      rw [
        Finset.sum_eq_single
          (t % r)
      ]

      · simp

      · intro s hs hne
        have hne' : t % r ≠ s :=
          Ne.symm hne
        simp [hne']

      · intro hnot
        exact False.elim (hnot hm)

/--
The Fourier coefficient of the period-class amplitude vector
in character `k`.
-/
private noncomputable def shorSpectralAmplitude
    (Q r k o : ℕ) : ℂ :=
  (1 / (Q : ℂ)) *
    ∑ t ∈ Finset.range Q,
      qftPhase r t k * star (qftPhase Q t o)

/--
The ordinary normalized QPE geometric sum corresponding to
the rational-frequency difference `k/r - o/Q`.
-/
private noncomputable def shorQPEAmplitude
    (Q r k o : ℕ) : ℂ :=
  let δ : ℝ :=
    (k : ℝ) / (r : ℝ) -
      (o : ℝ) / (Q : ℝ)
  let ζ : ℂ :=
    Complex.exp
      (Complex.I *
        ((2 * Real.pi * δ : ℝ) : ℂ))
  (1 / (Q : ℂ)) *
    ∑ t ∈ Finset.range Q, ζ ^ t

private lemma qftPhase_eq_exp_grid_shor
    (M z t : ℕ) :
    qftPhase M z t
      =
    Complex.exp
      (((2 * Real.pi) / (M : ℝ)) * Complex.I *
        ((z : ℂ) * (t : ℂ))) := by
  simp [
    qftPhase,
    ωPow,
    ω,
    div_eq_mul_inv,
    mul_assoc,
    mul_left_comm,
    mul_comm
  ]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma star_qftPhase_eq_negative_grid_phase_shor
    (M z t : ℕ) :
    star (qftPhase M z t)
      =
    Complex.exp
      (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (((z : ℂ) * (t : ℂ)) / (M : ℂ)))) := by
  rw [qftPhase_eq_exp_grid_shor]
  simp
  rw [← Complex.exp_conj]
  congr 1
  simp [div_eq_mul_inv]
  simp [starRingEnd]
  ring

private lemma omega_pow_self_shor
    (r : ℕ)
    (hr : 0 < r) :
    (ω r) ^ r = 1 := by
  unfold ω

  rw [← Complex.exp_nat_mul]

  have hr0 : (r : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hr

  have harg :
      (r : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I /
            (r : ℂ))
        =
      2 * (Real.pi : ℂ) * Complex.I := by
    field_simp [hr0]

  rw [harg, Complex.exp_two_pi_mul_I]

private lemma qftPhase_mod_left_shor
    (r t k : ℕ)
    (hr : 0 < r) :
    qftPhase r t k =
      qftPhase r (t % r) k := by
  unfold qftPhase ωPow

  have ht :
      t * k =
        (t % r) * k +
          r * ((t / r) * k) := by
    calc
      t * k
          =
        (t % r + r * (t / r)) * k := by
          rw [Nat.mod_add_div]
      _ =
        (t % r) * k +
          r * ((t / r) * k) := by
            ring

  rw [ht, pow_add]

  have hp :
      (ω r) ^ (r * ((t / r) * k)) = 1 := by
    rw [pow_mul, omega_pow_self_shor r hr]
    simp

  rw [hp, mul_one]

private lemma norm_qftPhase_one_shor
    (M x y : ℕ) :
    ‖qftPhase M x y‖ = 1 := by
  rw [qftPhase_eq_exp_grid_shor, Complex.norm_exp]
  simp

private lemma shorSpectralAmplitude_eq_period_classes
    {Q r k o : ℕ}
    (hr : 0 < r) :
    shorSpectralAmplitude Q r k o
      =
    ∑ s ∈ Finset.range r,
      qftPhase r s k *
        shorPeriodClassAmplitude Q r s o := by
  classical

  unfold shorSpectralAmplitude
  unfold shorPeriodClassAmplitude

  calc
    (1 / (Q : ℂ)) *
        ∑ t ∈ Finset.range Q,
          qftPhase r t k *
            star (qftPhase Q t o)
        =
      (1 / (Q : ℂ)) *
        ∑ t ∈ Finset.range Q,
          qftPhase r (t % r) k *
            star (qftPhase Q t o) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [qftPhase_mod_left_shor r t k hr]

    _ =
      (1 / (Q : ℂ)) *
        ∑ s ∈ Finset.range r,
          ∑ t ∈
              (Finset.range Q).filter
                (fun t => t % r = s),
            qftPhase r s k *
              star (qftPhase Q t o) := by
      congr 1
      exact
        sum_range_group_by_mod
          Q r hr
          (fun s t =>
            qftPhase r s k *
              star (qftPhase Q t o))

    _ =
      ∑ s ∈ Finset.range r,
        qftPhase r s k *
          ((1 / (Q : ℂ)) *
            ∑ t ∈
                (Finset.range Q).filter
                  (fun t => t % r = s),
              star (qftPhase Q t o)) := by
      rw [Finset.mul_sum]

      apply Finset.sum_congr rfl
      intro s hs

      rw [← Finset.mul_sum]
      ring

private lemma sq_sum_le_card_mul_sum_sq_shor
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℝ) :
    (∑ i ∈ S, f i) ^ 2
      ≤
    (S.card : ℝ) *
      ∑ i ∈ S, (f i) ^ 2 := by
  classical

  induction S using Finset.induction_on with
  | empty =>
      simp

  | @insert a S ha ih =>
      by_cases hS : S = ∅

      · subst S
        simp

      ·
        have hcardNat : 0 < S.card :=
          Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr hS)

        have hcard :
            0 < (S.card : ℝ) := by
          exact_mod_cast hcardNat

        let A : ℝ :=
          ∑ i ∈ S, f i

        let B : ℝ :=
          ∑ i ∈ S, (f i) ^ 2

        have hih :
            A ^ 2 ≤
              (S.card : ℝ) * B := by
          simpa [A, B] using ih

        have hcross :
            2 * f a * A
              ≤
            B + (S.card : ℝ) * (f a) ^ 2 := by
          have hsquare :
              0 ≤
                (A - (S.card : ℝ) * f a) ^ 2 :=
            sq_nonneg _

          nlinarith [hih, hsquare]

        simp [
          Finset.sum_insert,
          ha,
          Finset.card_insert_of_notMem,
          Nat.cast_add,
          Nat.cast_one
        ]

        change
          (f a + A) ^ 2
            ≤
          ((S.card : ℝ) + 1) *
            ((f a) ^ 2 + B)

        nlinarith [hih, hcross]

private lemma norm_sum_le_sum_norm_shor
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖
      ≤
    ∑ i ∈ S, ‖f i‖ := by
  classical

  induction S using Finset.induction_on with
  | empty =>
      simp

  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha]

      exact
        le_trans
          (norm_add_le (f a) (∑ i ∈ S, f i))
          (add_le_add (le_refl ‖f a‖) ih)

private lemma shorSpectralAmplitude_sq_le_paper
    {Q r k o : ℕ}
    (hr : 0 < r) :
    ‖shorSpectralAmplitude Q r k o‖ ^ 2
      ≤
    (r : ℝ) *
      shorPaperOutcomeProb Q r o := by
  classical

  let A : ℕ → ℂ :=
    fun s =>
      shorPeriodClassAmplitude
        Q r s o

  have hregroup :
      shorSpectralAmplitude Q r k o
        =
      ∑ s ∈ Finset.range r,
        qftPhase r s k * A s := by
    simpa [A] using
      (shorSpectralAmplitude_eq_period_classes
        (Q := Q) (r := r) (k := k) (o := o) hr)

  rw [hregroup]

  have htri0 :
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖
        ≤
      ∑ s ∈ Finset.range r,
        ‖qftPhase r s k * A s‖ :=
    norm_sum_le_sum_norm_shor
      (Finset.range r)
      (fun s =>
        qftPhase r s k * A s)

  have hterms :
      (∑ s ∈ Finset.range r,
          ‖qftPhase r s k * A s‖)
        =
      ∑ s ∈ Finset.range r,
        ‖A s‖ := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [norm_mul, norm_qftPhase_one_shor]
    simp

  have htri :
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖
        ≤
      ∑ s ∈ Finset.range r,
        ‖A s‖ := by
    exact htri0.trans_eq hterms

  have hsum_nonneg :
      0 ≤
      ∑ s ∈ Finset.range r,
        ‖A s‖ :=
    Finset.sum_nonneg
      (fun s hs => norm_nonneg _)

  have hnorm_nonneg :
      0 ≤
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖ :=
    norm_nonneg _

  have hsquare :
      ‖∑ s ∈ Finset.range r,
          qftPhase r s k * A s‖ ^ 2
        ≤
      (∑ s ∈ Finset.range r,
          ‖A s‖) ^ 2 := by

    have hprod :
        0 ≤
          ((∑ s ∈ Finset.range r, ‖A s‖) -
              ‖∑ s ∈ Finset.range r,
                  qftPhase r s k * A s‖) *
          ((∑ s ∈ Finset.range r, ‖A s‖) +
              ‖∑ s ∈ Finset.range r,
                  qftPhase r s k * A s‖) :=
      mul_nonneg
        (sub_nonneg.mpr htri)
        (add_nonneg hsum_nonneg hnorm_nonneg)

    nlinarith [hprod]

  have hcauchy :=
    sq_sum_le_card_mul_sum_sq_shor
      (Finset.range r)
      (fun s => ‖A s‖)

  calc
    ‖∑ s ∈ Finset.range r,
        qftPhase r s k * A s‖ ^ 2
        ≤
      (∑ s ∈ Finset.range r,
        ‖A s‖) ^ 2 :=
      hsquare

    _ ≤
      (r : ℝ) *
        ∑ s ∈ Finset.range r,
          ‖A s‖ ^ 2 := by
      simpa using hcauchy

    _ =
      (r : ℝ) *
        shorPaperOutcomeProb Q r o := by
      simp [
        A,
        shorPaperOutcomeProb
      ]

private lemma shorSpectralAmplitude_eq_qpe
    (Q r k o : ℕ) :
    shorSpectralAmplitude Q r k o
      =
    shorQPEAmplitude Q r k o := by
  classical

  unfold shorSpectralAmplitude
  unfold shorQPEAmplitude
  dsimp

  congr 1

  apply Finset.sum_congr rfl
  intro t ht

  rw [qftPhase_eq_exp_grid_shor]

  have hstar :
      (starRingEnd ℂ) (qftPhase Q t o)
        =
      Complex.exp
        (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((t : ℂ) * (o : ℂ)) / (Q : ℂ)))) := by
    simpa only [starRingEnd] using
      (star_qftPhase_eq_negative_grid_phase_shor Q t o)

  rw [hstar, ← Complex.exp_add, ← Complex.exp_nat_mul]

  congr 1
  push_cast
  simp [div_eq_mul_inv]
  ring

private lemma norm_natCast_complex_shor
    (n : ℕ) :
    ‖(n : ℂ)‖ = (n : ℝ) := by
  simp

private lemma shor_normalized_geometric_peak
    (Q : ℕ)
    (δ : ℝ)
    (hQ : 0 < Q)
    (hδ :
      |δ| ≤ 1 / (2 * (Q : ℝ))) :
    2 / Real.pi
      ≤
    ‖(1 / (Q : ℂ)) *
      ∑ t ∈ Finset.range Q,
        (Complex.exp
          (Complex.I *
            ((2 * Real.pi * δ : ℝ) : ℂ))) ^ t‖ := by
  classical

  have hQr :
      0 < (Q : ℝ) := by
    exact_mod_cast hQ

  have hQC :
      (Q : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hQ

  let ζ : ℂ :=
    Complex.exp
      (Complex.I *
        ((2 * Real.pi * δ : ℝ) : ℂ))

  let G : ℂ :=
    ∑ t ∈ Finset.range Q, ζ ^ t

  change
    2 / Real.pi ≤
      ‖(1 / (Q : ℂ)) * G‖

  by_cases hδ0 : δ = 0

  ·
    have hζ :
        ζ = 1 := by
      simp [ζ, hδ0]

    have hG :
        G = (Q : ℂ) := by
      simp [G, hζ]

    have htwo :
        2 / Real.pi ≤ 1 := by
      apply (div_le_iff₀ Real.pi_pos).2
      simpa using Real.two_le_pi

    rw [hG]
    simpa [hQC] using htwo

  ·
    have hδpos :
        0 < |δ| :=
      abs_pos.mpr hδ0

    /- geometric-series identity -/
    have hgeom :
        G * (ζ - 1) =
          ζ ^ Q - 1 := by
      dsimp [G]
      exact geom_sum_mul ζ Q

    /-
    Upper bound on the denominator chord:

        |e^{2πiδ} - 1| ≤ 2π|δ|.
    -/
    have hden_upper :
        ‖ζ - 1‖
          ≤
        2 * Real.pi * |δ| := by
      dsimp [ζ]

      have h :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
          (x := 2 * Real.pi * δ)

      calc
        ‖Complex.exp
            (Complex.I *
              ((2 * Real.pi * δ : ℝ) : ℂ)) - 1‖
            ≤
          ‖2 * Real.pi * δ‖ :=
            h

        _ =
          2 * Real.pi * |δ| := by
          rw [
            Real.norm_eq_abs,
            abs_mul,
            abs_mul,
            abs_of_nonneg
              (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_pos Real.pi_pos
          ]

    /-
    From |δ| ≤ 1/(2Q),

        |π Q δ| ≤ π/2.
    -/
    have hQδ :
        (Q : ℝ) * |δ| ≤ 1 / 2 := by
      calc
        (Q : ℝ) * |δ|
            ≤
          (Q : ℝ) *
            (1 / (2 * (Q : ℝ))) :=
          mul_le_mul_of_nonneg_left
            hδ
            (le_of_lt hQr)

        _ = 1 / 2 := by
          field_simp [ne_of_gt hQr]

    have harg :
        |Real.pi * (Q : ℝ) * δ|
          ≤
        Real.pi / 2 := by
      calc
        |Real.pi * (Q : ℝ) * δ|
            =
          Real.pi *
            ((Q : ℝ) * |δ|) := by
          rw [
            abs_mul,
            abs_mul,
            abs_of_pos Real.pi_pos,
            abs_of_pos hQr
          ]
          ring

        _ ≤
          Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left
            hQδ
            (le_of_lt Real.pi_pos)

        _ =
          Real.pi / 2 := by
          ring

    /-
    Jordan:

        2/π |πQδ| ≤ |sin(πQδ)|,

    hence

        2Q|δ| ≤ |sin(πQδ)|.
    -/
    have hjordan :
        2 / Real.pi *
            |Real.pi * (Q : ℝ) * δ|
          ≤
        |Real.sin
          (Real.pi * (Q : ℝ) * δ)| :=
      Real.mul_abs_le_abs_sin harg

    have hsin_lower :
        2 * (Q : ℝ) * |δ|
          ≤
        |Real.sin
          (Real.pi * (Q : ℝ) * δ)| := by
      calc
        2 * (Q : ℝ) * |δ|
            =
          2 / Real.pi *
            |Real.pi * (Q : ℝ) * δ| := by
          rw [
            abs_mul,
            abs_mul,
            abs_of_pos Real.pi_pos,
            abs_of_pos hQr
          ]
          field_simp [Real.pi_ne_zero]

        _ ≤
          |Real.sin
            (Real.pi * (Q : ℝ) * δ)| :=
          hjordan

    /-
    ζ^Q = exp(i · 2πQδ).
    -/
    have hζpow :
        ζ ^ Q =
          Complex.exp
            (Complex.I *
              ((2 * Real.pi *
                  (Q : ℝ) * δ : ℝ) : ℂ)) := by
      dsimp [ζ]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring

    /-
    Exact numerator chord:

        |ζ^Q - 1| = 2 |sin(πQδ)|.
    -/
    have hnum_eq :
        ‖ζ ^ Q - 1‖
          =
        2 *
          |Real.sin
            (Real.pi * (Q : ℝ) * δ)| := by
      rw [
        hζpow,
        Complex.norm_exp_I_mul_ofReal_sub_one
      ]

      rw [Real.norm_eq_abs]

      have hhalf :
          (2 * Real.pi *
              (Q : ℝ) * δ) / 2
            =
          Real.pi * (Q : ℝ) * δ := by
        ring

      rw [hhalf, abs_mul]
      norm_num

    have hnum_lower :
        4 * (Q : ℝ) * |δ|
          ≤
        ‖ζ ^ Q - 1‖ := by
      rw [hnum_eq]
      nlinarith [hsin_lower]

    /-
    Multiply the geometric identity by norms:
      |G| |ζ-1| = |ζ^Q-1|.
    -/
    have hprod :
        ‖G‖ * ‖ζ - 1‖ =
          ‖ζ ^ Q - 1‖ := by
      calc
        ‖G‖ * ‖ζ - 1‖
            =
          ‖G * (ζ - 1)‖ := by
            rw [norm_mul]

        _ =
          ‖ζ ^ Q - 1‖ := by
            rw [hgeom]

    have hmain :
        4 * (Q : ℝ) * |δ|
          ≤
        ‖G‖ *
          (2 * Real.pi * |δ|) := by
      calc
        4 * (Q : ℝ) * |δ|
            ≤
          ‖ζ ^ Q - 1‖ :=
          hnum_lower

        _ =
          ‖G‖ * ‖ζ - 1‖ :=
          hprod.symm

        _ ≤
          ‖G‖ *
            (2 * Real.pi * |δ|) :=
          mul_le_mul_of_nonneg_left
            hden_upper
            (norm_nonneg _)

    /-
    Cancel the positive `2π|δ|`.
    -/
    have hD :
        0 <
          2 * Real.pi * |δ| := by
      positivity

    have hmul :
        (2 * (Q : ℝ) / Real.pi) *
            (2 * Real.pi * |δ|)
          ≤
        ‖G‖ *
            (2 * Real.pi * |δ|) := by
      calc
        (2 * (Q : ℝ) / Real.pi) *
            (2 * Real.pi * |δ|)
            =
          4 * (Q : ℝ) * |δ| := by
            field_simp [Real.pi_ne_zero]
            ring

        _ ≤
          ‖G‖ *
            (2 * Real.pi * |δ|) :=
          hmain

    have hG_lower :
        2 * (Q : ℝ) / Real.pi
          ≤
        ‖G‖ := by
      exact le_of_mul_le_mul_right hmul (by omega)

    /- put back the `1/Q` normalization -/
    have hscale :
        ‖(1 / (Q : ℂ))‖ =
          1 / (Q : ℝ) := by
      rw [
        norm_div,
        norm_one,
        norm_natCast_complex_shor
      ]

    rw [norm_mul, hscale]

    calc
      2 / Real.pi
          =
        (1 / (Q : ℝ)) *
          (2 * (Q : ℝ) / Real.pi) := by
        field_simp [
          ne_of_gt hQr,
          Real.pi_ne_zero
        ]

      _ ≤
        (1 / (Q : ℝ)) * ‖G‖ :=
        mul_le_mul_of_nonneg_left
          hG_lower
          (by positivity)

/--
The Fourier-peak estimate.

If

    |o/Q - k/r| ≤ 1/(2Q),

then the phases in each period class lie sufficiently close together.
Summing the resulting geometric progression gives the standard
`4 / π²` phase-estimation lower bound after marginalizing over the
second register:

    P(o) ≥ (4 / π²) / r.

This is the analytic heart of Shor's equations (5.7)--(5.13).
-/
lemma shor_paper_peak_lower_bound
    {Q r o k : ℕ}
    (happrox :
      approxRat o Q k r
        (1 / (2 * (Q : ℝ)))) :
    (4 / Real.pi ^ 2) *
        (1 / (r : ℝ))
      ≤
    shorPaperOutcomeProb Q r o := by
  classical

  rcases happrox with
    ⟨hQ, hr, happ⟩

  let δ : ℝ :=
    (k : ℝ) / (r : ℝ) -
      (o : ℝ) / (Q : ℝ)

  have hδ :
      |δ| ≤
        1 / (2 * (Q : ℝ)) := by
    dsimp [δ]
    simpa [abs_sub_comm] using happ

  /-
  The relevant Fourier mode has amplitude at least `2 / π`.
  -/
  have hgeom :
      2 / Real.pi
        ≤
      ‖shorQPEAmplitude Q r k o‖ := by
    simpa [shorQPEAmplitude, δ] using
      (shor_normalized_geometric_peak
        Q δ hQ hδ)

  have hpeak :
      2 / Real.pi
        ≤
      ‖shorSpectralAmplitude Q r k o‖ := by
    rw [shorSpectralAmplitude_eq_qpe]
    exact hgeom

  /-
  Square the `2 / π` bound.
  -/
  have htwo_nonneg :
      0 ≤ 2 / Real.pi := by
    positivity

  have hsqprod :
      0 ≤
        (‖shorSpectralAmplitude Q r k o‖ -
            2 / Real.pi) *
        (‖shorSpectralAmplitude Q r k o‖ +
            2 / Real.pi) :=
    mul_nonneg
      (sub_nonneg.mpr hpeak)
      (add_nonneg
        (norm_nonneg _)
        htwo_nonneg)

  have hpeak_sq :
      4 / Real.pi ^ 2
        ≤
      ‖shorSpectralAmplitude Q r k o‖ ^ 2 := by
    have hsq :
        (2 / Real.pi) ^ 2
          ≤
        ‖shorSpectralAmplitude Q r k o‖ ^ 2 := by
      nlinarith [hsqprod]

    calc
      4 / Real.pi ^ 2
          =
        (2 / Real.pi) ^ 2 := by
          field_simp [Real.pi_ne_zero]
          ring

      _ ≤
        ‖shorSpectralAmplitude Q r k o‖ ^ 2 :=
        hsq

  /-
  Cauchy-Schwarz:
      |B_k|² ≤ r · P(o).
  -/
  have hspectral :
      ‖shorSpectralAmplitude Q r k o‖ ^ 2
        ≤
      (r : ℝ) *
        shorPaperOutcomeProb Q r o :=
    shorSpectralAmplitude_sq_le_paper
      (Q := Q)
      (r := r)
      (k := k)
      (o := o)
      hr

  have hrR :
      0 < (r : ℝ) := by
    exact_mod_cast hr

  /-
  Divide the resulting inequality by `r`.
  -/
  have hmul :
      (r : ℝ) *
          ((4 / Real.pi ^ 2) *
            (1 / (r : ℝ)))
        ≤
      (r : ℝ) *
        shorPaperOutcomeProb Q r o := by
    calc
      (r : ℝ) *
          ((4 / Real.pi ^ 2) *
            (1 / (r : ℝ)))
          =
        4 / Real.pi ^ 2 := by
          field_simp [
            ne_of_gt hrR,
            Real.pi_ne_zero
          ]

      _ ≤
        ‖shorSpectralAmplitude Q r k o‖ ^ 2 :=
        hpeak_sq

      _ ≤
        (r : ℝ) *
          shorPaperOutcomeProb Q r o :=
        hspectral

  by_contra h
  have hlt :
      shorPaperOutcomeProb Q r o
        <
      (4 / Real.pi ^ 2) * (1 / (r : ℝ)) :=
    lt_of_not_ge h

  have hmul' :
      (r : ℝ) * shorPaperOutcomeProb Q r o
        <
      (r : ℝ) *
        ((4 / Real.pi ^ 2) * (1 / (r : ℝ))) :=
    mul_lt_mul_of_pos_left hlt hrR

  exact (not_lt_of_ge hmul) hmul'

/--
A `GoodOutcome` therefore has the Fourier lower bound.

This is only unpacking `GoodOutcome`; all analytic work stays in
`shor_paper_peak_lower_bound`.
-/
lemma shor_paper_goodOutcome_lower_bound
    {Q r o : ℕ}
    (hgood : GoodOutcome o Q r) :
    (4 / Real.pi ^ 2) * (1 / (r : ℝ))
      ≤
    shorPaperOutcomeProb Q r o := by
  rcases hgood with
    ⟨k, hk, _hcoprime, hrQ, happrox⟩

  exact shor_paper_peak_lower_bound happrox

/--
The finite set of exponent-register outputs satisfying `GoodOutcome`.
-/
noncomputable def goodOutcomeFinset
    (Q r : ℕ) :
    Finset (Fin Q) := by
  classical
  exact Finset.univ.filter
    (fun o => GoodOutcome o.1 Q r)

@[simp]
lemma mem_goodOutcomeFinset
    {Q r : ℕ}
    (o : Fin Q) :
    o ∈ goodOutcomeFinset Q r ↔
      GoodOutcome o.1 Q r := by
  classical
  simp [goodOutcomeFinset]

private noncomputable def shorNearestOutput
    (Q r k : ℕ) : ℕ :=
  ⌊((Q : ℝ) * (k : ℝ) / (r : ℝ) + (1 : ℝ) / 2)⌋₊

private lemma shorNearestOutput_spec
    {Q r k : ℕ}
    (hr : 0 < r)
    (hrQ : r ^ 2 ≤ Q)
    (hk : k < r) :
    shorNearestOutput Q r k < Q ∧
      approxRat
        (shorNearestOutput Q r k)
        Q k r
        (1 / (2 * (Q : ℝ))) := by
  classical

  have hQ : 0 < Q := by
    have hr2 : 0 < r ^ 2 := by positivity
    omega

  have hrR : 0 < (r : ℝ) := by
    exact_mod_cast hr

  have hQR : 0 < (Q : ℝ) := by
    exact_mod_cast hQ

  let x : ℝ :=
    (Q : ℝ) * (k : ℝ) / (r : ℝ)

  let a : ℝ :=
    x + 1 / 2

  let o : ℕ :=
    shorNearestOutput Q r k

  have ho_floor :
      o = ⌊a⌋₊ := by
    simp [o, shorNearestOutput, a, x]

  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity

  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity

  /-
  floor(a) ≤ a < floor(a) + 1.
  -/
  have hfloor_le :
      (o : ℝ) ≤ a := by
    rw [ho_floor]
    exact
      (Nat.le_floor_iff ha0).mp
        (le_refl ⌊a⌋₊)

  have hfloor_lt :
      a < (o : ℝ) + 1 := by
    rw [ho_floor]

    by_contra h

    have hge :
        ((⌊a⌋₊ : ℕ) : ℝ) + 1 ≤ a :=
      le_of_not_gt h

    have hbad :
        ⌊a⌋₊ + 1 ≤ ⌊a⌋₊ := by
      apply Nat.le_floor
      simpa [Nat.cast_add, Nat.cast_one] using hge

    omega

  /-
  Hence the rounded integer is within 1/2 of x.
  -/
  have hround :
      |(o : ℝ) - x| ≤ 1 / 2 := by
    rw [abs_le]

    constructor
    · dsimp [a] at hfloor_lt
      linarith

    · dsimp [a] at hfloor_le
      linarith

  /-
  Since k ≤ r - 1 and Q ≥ r²,

      Q - Q*k/r ≥ Q/r ≥ 1,

  so rounding cannot reach Q.
  -/
  have hr1 : 1 ≤ r := by
    omega

  have hr_le_sq :
      r ≤ r ^ 2 := by
    calc
      r = r * 1 := by simp
      _ ≤ r * r := by
        exact Nat.mul_le_mul_left r hr1
      _ = r ^ 2 := by
        ring

  have hrQ' :
      r ≤ Q :=
    le_trans hr_le_sq hrQ

  have hqdiv :
      (1 : ℝ) ≤ (Q : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrR).2
    have h : (r : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hrQ'
    simpa using h

  have hk1 :
      k + 1 ≤ r :=
    Nat.succ_le_of_lt hk

  have hkR :
      (k : ℝ) + 1 ≤ (r : ℝ) := by
    exact_mod_cast hk1

  have hgap :
      (1 : ℝ) ≤ (r : ℝ) - (k : ℝ) := by
    linarith

  have hprod :
      (1 : ℝ) ≤
        ((Q : ℝ) / (r : ℝ)) *
          ((r : ℝ) - (k : ℝ)) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤
          ((Q : ℝ) / (r : ℝ)) *
            ((r : ℝ) - (k : ℝ)) := by
        exact mul_le_mul
          hqdiv hgap
          (by norm_num)
          (by linarith)

  have hQminusx :
      (Q : ℝ) - x =
        ((Q : ℝ) / (r : ℝ)) *
          ((r : ℝ) - (k : ℝ)) := by
    dsimp [x]
    field_simp [ne_of_gt hrR]

  have hQgap :
      (1 : ℝ) ≤ (Q : ℝ) - x := by
    rw [hQminusx]
    exact hprod

  have haQ :
      a < (Q : ℝ) := by
    dsimp [a]
    linarith

  have hoQ_real :
      (o : ℝ) < (Q : ℝ) :=
    lt_of_le_of_lt hfloor_le haQ

  have hoQ :
      o < Q := by
    exact_mod_cast hoQ_real

  /-
  Divide the rounding error by Q.
  -/
  have hdiff :
      (o : ℝ) / (Q : ℝ) -
          (k : ℝ) / (r : ℝ)
        =
      ((o : ℝ) - x) / (Q : ℝ) := by
    dsimp [x]
    field_simp [
      ne_of_gt hQR,
      ne_of_gt hrR
    ]

  have happ :
      |(o : ℝ) / (Q : ℝ) -
          (k : ℝ) / (r : ℝ)|
        ≤
      1 / (2 * (Q : ℝ)) := by
    rw [
      hdiff,
      abs_div,
      abs_of_pos hQR
    ]

    calc
      |(o : ℝ) - x| / (Q : ℝ)
          ≤
        (1 / 2) / (Q : ℝ) :=
        div_le_div_of_nonneg_right
          hround
          (le_of_lt hQR)

      _ =
        1 / (2 * (Q : ℝ)) := by
          field_simp [ne_of_gt hQR]

  refine ⟨hoQ, ?_⟩

  refine ⟨hQ, hr, ?_⟩

  simpa [abs_sub_comm] using happ

private lemma shorNearestOutput_injective_below
    {Q r k₁ k₂ : ℕ}
    (hr : 0 < r)
    (hrQ : r ^ 2 ≤ Q)
    (hk₁ : k₁ < r)
    (hk₂ : k₂ < r)
    (heq : shorNearestOutput Q r k₁ = shorNearestOutput Q r k₂) :
    k₁ = k₂ := by

  by_cases hr1 : r = 1
  · omega

  have hrgt : 1 < r := by
    omega

  have hQ : 0 < Q := by
    have hr2 : 0 < r ^ 2 := by positivity
    omega

  have hrR : 0 < (r : ℝ) := by
    exact_mod_cast hr

  have hQR : 0 < (Q : ℝ) := by
    exact_mod_cast hQ

  by_contra hne

  have ha₁ :=
    (shorNearestOutput_spec
      (Q := Q) (r := r) (k := k₁)
      hr hrQ hk₁).2

  have ha₂ :=
    (shorNearestOutput_spec
      (Q := Q) (r := r) (k := k₂)
      hr hrQ hk₂).2

  rcases ha₁ with
    ⟨_hQ₁, _hr₁, ha₁⟩

  rcases ha₂ with
    ⟨_hQ₂, _hr₂, ha₂⟩

  rw [← heq] at ha₂

  /-
  If both rationals lie within 1/(2Q) of the same output,
  then they are within 1/Q of each other.
  -/
  have htri :
      |(k₁ : ℝ) / (r : ℝ) -
          (k₂ : ℝ) / (r : ℝ)|
        ≤
      1 / (Q : ℝ) := by
    calc
      |(k₁ : ℝ) / (r : ℝ) -
          (k₂ : ℝ) / (r : ℝ)|
          =
        |((k₁ : ℝ) / (r : ℝ) -
            (shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ))
          +
          ((shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ) -
            (k₂ : ℝ) / (r : ℝ))| := by
          congr 1
          ring

      _ ≤
        |(k₁ : ℝ) / (r : ℝ) -
            (shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ)|
        +
        |(shorNearestOutput Q r k₁ : ℝ) /
              (Q : ℝ) -
            (k₂ : ℝ) / (r : ℝ)| :=
          abs_add_le _ _

      _ ≤
        1 / (2 * (Q : ℝ)) +
        1 / (2 * (Q : ℝ)) := by
          apply add_le_add
          · simpa [abs_sub_comm] using ha₁
          · exact ha₂

      _ =
        1 / (Q : ℝ) := by
          field_simp [ne_of_gt hQR]
          ring

  have hfrac :
      |(k₁ : ℝ) - (k₂ : ℝ)| /
          (r : ℝ)
        ≤
      1 / (Q : ℝ) := by
    have he :
        |(k₁ : ℝ) / (r : ℝ) -
            (k₂ : ℝ) / (r : ℝ)|
          =
        |(k₁ : ℝ) - (k₂ : ℝ)| /
          (r : ℝ) := by
      rw [
        ← sub_div,
        abs_div,
        abs_of_pos hrR
      ]

    rw [← he]
    exact htri

  /-
  Distinct natural numbers differ by at least one.
  -/
  have hdiff :
      (1 : ℝ) ≤
        |(k₁ : ℝ) - (k₂ : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hlt | hgt

    · have hg :
          (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hlt

      have hnonpos :
          (k₁ : ℝ) - (k₂ : ℝ) ≤ 0 := by
        have hle : (k₁ : ℝ) ≤ (k₂ : ℝ) := by
          exact_mod_cast Nat.le_of_lt hlt
        linarith

      rw [abs_of_nonpos hnonpos]
      linarith

    · have hg :
          (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hgt

      have hnonneg :
          0 ≤ (k₁ : ℝ) - (k₂ : ℝ) := by
        have hle : (k₂ : ℝ) ≤ (k₁ : ℝ) := by
          exact_mod_cast Nat.le_of_lt hgt
        linarith

      rw [abs_of_nonneg hnonneg]
      linarith

  have hrecip :
      1 / (r : ℝ) ≤ 1 / (Q : ℝ) := by
    calc
      1 / (r : ℝ)
          ≤
        |(k₁ : ℝ) - (k₂ : ℝ)| /
          (r : ℝ) :=
        div_le_div_of_nonneg_right
          hdiff
          (le_of_lt hrR)

      _ ≤ 1 / (Q : ℝ) :=
        hfrac

  /-
  1/r ≤ 1/Q implies Q ≤ r.
  -/
  have hQrR :
      (Q : ℝ) ≤ (r : ℝ) :=
    le_of_one_div_le_one_div
      hrR hrecip

  have hQr :
      Q ≤ r := by
    exact_mod_cast hQrR

  have hrsq :
      r < r ^ 2 := by
    calc
      r = r * 1 := by simp
      _ < r * r :=
        Nat.mul_lt_mul_of_pos_left
          hrgt hr
      _ = r ^ 2 := by
        ring

  omega

/--
Shor's counting step.

For every `k < r` coprime to `r`, choose the integer `o` nearest to

    Q*k/r.

Because `r² ≤ Q`, that output satisfies

    |o/Q - k/r| ≤ 1/(2Q),

and different reduced fractions `k/r` give different outputs.

Hence there are at least `φ(r)` good outputs.
-/
lemma goodOutcome_card_ge_totient
    {Q r : ℕ}
    (hr : 0 < r)
    (hrQ : r ^ 2 ≤ Q) :
    Nat.totient r ≤
      (goodOutcomeFinset Q r).card := by
  classical

  let S : Finset ℕ :=
    (Finset.range r).filter (Nat.Coprime r)

  let f :
      ↥S →
        ↥(goodOutcomeFinset Q r) :=
    fun k => by
      have hkS :
          k.1 ∈ S :=
        k.2

      have hkdata :
          k.1 < r ∧
            Nat.Coprime r k.1 := by
        have hkfilter :
            k.1 ∈ (Finset.range r).filter (Nat.Coprime r) := by
          simp [S] at hkS ⊢
        exact
          ⟨
            Finset.mem_range.mp (Finset.mem_filter.mp hkfilter).1,
            (Finset.mem_filter.mp hkfilter).2
          ⟩

      have hk :
          k.1 < r :=
        hkdata.1

      have hspec :=
        shorNearestOutput_spec
          (Q := Q)
          (r := r)
          (k := k.1)
          hr hrQ hk

      exact
        ⟨
          ⟨shorNearestOutput Q r k.1,
            hspec.1⟩,
          by
            rw [mem_goodOutcomeFinset]

            refine
              ⟨k.1, hk, ?_, hrQ, hspec.2⟩

            exact hkdata.2.symm
        ⟩

  have hf :
      Function.Injective f := by
    intro k₁ k₂ h

    apply Subtype.ext

    have hk₁ :
        k₁.1 < r := by
      have hmem :
          k₁.1 ∈ (Finset.range r).filter (Nat.Coprime r) := by
        simp [S] at k₁ ⊢
      exact Finset.mem_range.mp (Finset.mem_filter.mp hmem).1

    have hk₂ :
        k₂.1 < r := by
      have hmem :
          k₂.1 ∈ (Finset.range r).filter (Nat.Coprime r) := by
        simp [S] at k₂ ⊢
      exact Finset.mem_range.mp (Finset.mem_filter.mp hmem).1

    have hout :
        shorNearestOutput Q r k₁.1 =
          shorNearestOutput Q r k₂.1 := by
      have h' :=
        congrArg
          (fun z :
            ↥(goodOutcomeFinset Q r) =>
              z.1.1)
          h

      simpa [f] using h'

    exact
      shorNearestOutput_injective_below
        hr hrQ hk₁ hk₂ hout

  calc
    Nat.totient r
        =
      S.card := by
        simpa [S] using
          Nat.totient_eq_card_coprime r

    _ ≤
      (goodOutcomeFinset Q r).card :=
        Finset.card_le_card_of_injective hf

/--
Pure finite-sum bookkeeping.

If:
* there are at least `φ(r)` good outputs, and
* every good output has probability at least `(4/π²)/r`,

then their total probability is at least

    (4/π²) * φ(r)/r.

This lemma contains no quantum reasoning.
-/
lemma goodOutcome_mass_lower_bound_from_card_and_pointwise
    (Q r : ℕ)
    (p : Fin Q → ℝ)
    (hr : 0 < r)
    (hcard :
      Nat.totient r ≤
        (goodOutcomeFinset Q r).card)
    (hpoint :
      ∀ o : Fin Q,
        GoodOutcome o.1 Q r →
          (4 / Real.pi ^ 2) * (1 / (r : ℝ))
            ≤ p o) :
    (4 / Real.pi ^ 2) *
        ((Nat.totient r : ℝ) / (r : ℝ))
      ≤
    ∑ o : Fin Q,
      goodOutcomeIndicator o.1 Q r * p o := by
  classical

  let c : ℝ :=
    (4 / Real.pi ^ 2) * (1 / (r : ℝ))

  have hc : 0 ≤ c := by
    dsimp [c]
    positivity

  have hcard_real :
      (Nat.totient r : ℝ) ≤
        ((goodOutcomeFinset Q r).card : ℝ) := by
    exact_mod_cast hcard

  calc
    (4 / Real.pi ^ 2) *
        ((Nat.totient r : ℝ) / (r : ℝ))
        =
      (Nat.totient r : ℝ) * c := by
        simp [c, div_eq_mul_inv]
        ring

    _ ≤
      ((goodOutcomeFinset Q r).card : ℝ) * c := by
        exact mul_le_mul_of_nonneg_right
          hcard_real hc

    _ =
      ∑ o ∈ goodOutcomeFinset Q r, c := by
        simp

    _ ≤
      ∑ o ∈ goodOutcomeFinset Q r, p o := by
        apply Finset.sum_le_sum
        intro o ho
        apply hpoint o
        exact (mem_goodOutcomeFinset o).mp ho

    _ =
      ∑ o : Fin Q,
        goodOutcomeIndicator o.1 Q r * p o := by
        simp [
          goodOutcomeFinset,
          goodOutcomeIndicator,
          Finset.sum_filter
        ]

/--
A deliberately weak consequence of the standard lower bounds for
Euler's totient ratio.

For an order `r < N`,

    φ(r) / r ≥ exp(-2) / log₂(N)^4.

This is much weaker than the classical asymptotic bound used by Shor,
but is convenient because it gives exactly the public theorem's
inverse-polylogarithmic form.
-/
lemma shor_totient_ratio_log4_lower_bound
    {a r N m n : ℕ}
    (hsetting : BasicSetting a r N m n) :
    Real.exp (-2) / (Nat.log2 N : ℝ) ^ 4
      ≤
    (Nat.totient r : ℝ) / (r : ℝ) := by
  sorry

end Shor
