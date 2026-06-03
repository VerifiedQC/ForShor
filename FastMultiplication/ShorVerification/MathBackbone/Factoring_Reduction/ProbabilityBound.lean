import FastMultiplication.ShorVerification.MathBackbone.Factoring_Reduction.Defs

open Classical

/-
  Math-related lemmas for success conditions
-/

lemma zmod_eq_zero_iff_dvd {N : ℕ} (x : ℕ) :
((x : ZMod N) = 0) ↔ N ∣ x := by
  exact ZMod.natCast_eq_zero_iff x N

/-- If N > 1 and N is not a prime power, then N has at least two distinct prime factors.
    Proof: take p = minFac, divide out all p-factors to get M = N / p^v_p(N).
    Since N ≠ p^k, M ≠ 1, so M has a prime factor q = minFac(M) with q ≠ p. -/
lemma exists_two_distinct_prime_factors {N : ℕ} (hN : N > 1)
    (h : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p ∣ N ∧ q ∣ N := by
  have hN0 : N ≠ 0 := by omega
  set p := N.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpN : p ∣ N := Nat.minFac_dvd N
  set M := N / p ^ N.factorization p
  have hM_ne_one : M ≠ 1 := by
    intro hM1
    apply h p (N.factorization p) hp
    have key : p ^ N.factorization p * M = N := Nat.ordProj_mul_ordCompl_eq_self N p
    rw [hM1, mul_one] at key
    exact key.symm
  set q := M.minFac
  have hq : q.Prime := Nat.minFac_prime hM_ne_one
  have hqM : q ∣ M := Nat.minFac_dvd M
  have hpq : p ≠ q := by
    intro heq
    have h_dvd : p ∣ M := by rwa [heq]
    exact (Nat.not_dvd_ordCompl hp hN0) h_dvd
  exact ⟨p, q, hp, hq, hpq, hpN, dvd_trans hqM (Nat.ordCompl_dvd N p)⟩

/-- For N > 1, valid_choices(N) has cardinality φ(N) - 1.
    valid_choices excludes a = 0 (not coprime) and a = 1 (trivial order),
    so it is the totient set minus {1}. -/
lemma valid_choices_card_general {N : ℕ} (hN : N > 1) :
    (valid_choices N).card = Nat.totient N - 1 := by
  have h1_mem : (1 : ℕ) ∈ (Finset.range N).filter (Nat.Coprime N) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.gcd_one_right N⟩
  have h_eq : valid_choices N = ((Finset.range N).filter (Nat.Coprime N)).erase 1 := by
    ext a
    simp only [valid_choices, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨ha_lt, ha_gt, ha_gcd⟩
      refine ⟨by omega, ha_lt, ?_⟩
      show Nat.gcd N a = 1
      rwa [Nat.gcd_comm]
    · rintro ⟨ha_ne, ha_lt, ha_cop⟩
      refine ⟨ha_lt, ?_, show Nat.gcd a N = 1 by rw [Nat.gcd_comm]; exact ha_cop⟩
      have : a ≠ 0 := by
        intro h0; subst h0
        unfold Nat.Coprime at ha_cop; rw [Nat.gcd_zero_right] at ha_cop; omega
      omega
  have hcard : ((Finset.range N).filter (Nat.Coprime N)).card = Nat.totient N := by
    unfold Nat.totient; congr 1
  rw [h_eq, Finset.card_erase_of_mem h1_mem, hcard]

/-- Element a = 1 is never a successful choice: its order is 1 (odd), so it
    fails the "even order" condition. -/
lemma one_not_successful_choice (N : ℕ) : ¬is_successful_choice 1 N := by
  rintro ⟨r, hr, heven, -⟩
  unfold is_period at hr
  rw [Nat.cast_one, orderOf_one] at hr
  obtain ⟨k, hk⟩ := heven; omega

/-- The number of coprime residues mod pq equals (p-1)(q-1), i.e., Euler's totient φ(pq). -/
lemma coprime_count {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    ((Finset.range (p * q)).filter (fun a => Nat.gcd a (p * q) = 1)).card
    = (p - 1) * (q - 1) := by
  -- Rewrite gcd a N = 1 to Coprime N a (totient's predicate uses Coprime N a = gcd N a = 1)
  have h_eq : (Finset.range (p * q)).filter (fun a => Nat.gcd a (p * q) = 1)
    = (Finset.range (p * q)).filter (fun a => Nat.Coprime (p * q) a) := by
    apply Finset.filter_congr
    intro a _
    show Nat.gcd a (p * q) = 1 ↔ Nat.gcd (p * q) a = 1
    rw [Nat.gcd_comm]
  rw [h_eq]
  -- Now the LHS is exactly Nat.totient (p * q)
  change Nat.totient (p * q) = (p - 1) * (q - 1)
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq),
      Nat.totient_prime hp, Nat.totient_prime hq]

/-- CRT sends natural number casts to the pair of casts. -/
lemma crt_natCast_eq {m n : ℕ} (h : Nat.Coprime m n) (a : ℕ) :
    ZMod.chineseRemainder h (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) :=
  Prod.ext (by simp [ZMod.chineseRemainder])
           (by simp [ZMod.chineseRemainder])

/-- Under CRT, orderOf equals lcm of component orders. -/
lemma orderOf_crt_eq_lcm {m n : ℕ} (h : Nat.Coprime m n) (a : ℕ) :
    orderOf (a : ZMod (m * n)) = Nat.lcm (orderOf (a : ZMod m)) (orderOf (a : ZMod n)) := by
  rw [← MulEquiv.orderOf_eq (ZMod.chineseRemainder h).toMulEquiv (a : ZMod (m * n)),
      show (ZMod.chineseRemainder h).toMulEquiv (a : ZMod (m * n)) =
        ZMod.chineseRemainder h (a : ZMod (m * n)) from rfl,
      crt_natCast_eq, Prod.orderOf_mk]

/-- Under CRT, a^k = -1 iff both components are -1. -/
lemma pow_eq_neg_one_crt {m n : ℕ} (h : Nat.Coprime m n) (a k : ℕ) :
    (a : ZMod (m * n)) ^ k = -1 ↔
    (a : ZMod m) ^ k = -1 ∧ (a : ZMod n) ^ k = -1 := by
  let φ := ZMod.chineseRemainder h
  constructor
  · intro heq
    have h1 := congr_arg φ heq
    rw [map_pow, crt_natCast_eq, map_neg, map_one, Prod.neg_mk, Prod.pow_mk] at h1
    exact ⟨(Prod.mk.inj h1).1, (Prod.mk.inj h1).2⟩
  · intro ⟨hp, hq⟩
    apply φ.injective
    rw [map_pow, crt_natCast_eq, map_neg, map_one, Prod.neg_mk, Prod.pow_mk]
    exact Prod.mk_inj.mpr ⟨hp, hq⟩

/-- ¬is_successful_choice iff order is odd or half-power equals -1. -/
lemma not_successful_iff (a N : ℕ) :
    ¬is_successful_choice a N ↔
    (¬Even (orderOf (a : ZMod N)) ∨
     (a : ZMod N) ^ (orderOf (a : ZMod N) / 2) = -1) := by
  unfold is_successful_choice is_period shor_success_conditions
  push_neg
  constructor
  · intro h
    by_cases heven : Even (orderOf (a : ZMod N))
    · right; exact h _ rfl heven
    · left; exact heven
  · rintro (hodd | hneg) r hr heven
    · exact absurd (hr ▸ heven) hodd
    · rw [← hr]; exact hneg

/-- If u^(n/2) ≠ 1 and orderOf u divides n, then n/orderOf u is odd. -/
lemma div_orderOf_odd_of_pow_ne_one {G : Type*} [Group G]
    {u : G} {n : ℕ} (hdvd : orderOf u ∣ n) (h : u ^ (n / 2) ≠ 1) :
    ¬Even (n / orderOf u) := by
  intro ⟨k, hk⟩
  apply h
  -- If orderOf u = 0 then 0 ∣ n forces n = 0, so u^0 = 1, contradicting h
  have ho_pos : 0 < orderOf u := by
    by_contra h0; push_neg at h0
    have : orderOf u = 0 := by omega
    rw [this, Nat.zero_dvd] at hdvd; subst hdvd; simp at h
  -- From n / orderOf u = 2k and orderOf u | n, derive n = orderOf u * (2 * k)
  have hn : n = orderOf u * (2 * k) := by
    have h1 := Nat.div_mul_cancel hdvd  -- n / orderOf u * orderOf u = n
    rw [hk] at h1; linarith
  -- Therefore n / 2 = orderOf u * k
  have h2 : n / 2 = orderOf u * k := by
    have : n = 2 * (orderOf u * k) := by linarith
    omega
  rw [h2, pow_mul, pow_orderOf_eq_one, one_pow]

/-- A positive natural is odd iff its factorization at 2 vanishes. -/
lemma odd_iff_factorization_two_eq_zero {n : ℕ} (hn : n ≠ 0) :
    Odd n ↔ n.factorization 2 = 0 := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  rw [Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn]
  omega

/-- For `d ∣ n`, the quotient `n / d` is odd iff `d` carries the full 2-part of `n`. -/
lemma odd_div_iff_factorization_two_eq {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    Odd (n / d) ↔ n.factorization 2 = d.factorization 2 := by
  have hd0 : d ≠ 0 := by
    intro h
    subst h
    rw [Nat.zero_dvd] at hd
    exact hn hd
  have hnd : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
      (Nat.pos_of_ne_zero hd0)).ne'
  rw [odd_iff_factorization_two_eq_zero hnd, Nat.factorization_div hd]
  change (n.factorization 2 - d.factorization 2 = 0) ↔ n.factorization 2 = d.factorization 2
  have hle : d.factorization 2 ≤ n.factorization 2 := by
    exact (Nat.factorization_le_iff_dvd hd0 hn).2 hd 2
  omega

/-- If `n` is even and nonzero, then `gcd n k` is odd exactly when `k` is odd. -/
lemma gcd_odd_iff_right_odd_of_left_even {n k : ℕ} (hn0 : n ≠ 0) (hn_even : Even n) :
    Odd (Nat.gcd n k) ↔ Odd k := by
  cases hk0 : k with
  | zero =>
      have hnot : ¬ Odd n := by simpa [Nat.not_even_iff_odd] using hn_even
      simpa [hk0, Nat.gcd_zero_right] using hnot
  | succ k =>
      have hkpos : Nat.succ k ≠ 0 := by simp
      have hg0 : Nat.gcd n (Nat.succ k) ≠ 0 := Nat.gcd_ne_zero_left hn0
      rw [odd_iff_factorization_two_eq_zero hg0, odd_iff_factorization_two_eq_zero hkpos]
      have hgfac :=
        congrArg (fun f => f 2) (Nat.factorization_gcd (a := n) (b := Nat.succ k) hn0 hkpos)
      simp only [Finsupp.inf_apply] at hgfac
      rw [hgfac]
      change min (n.factorization 2) ((Nat.succ k).factorization 2) = 0 ↔
        (Nat.succ k).factorization 2 = 0
      have hn2pos : 0 < n.factorization 2 := by
        have hdiv2 : 2 ∣ n := by rwa [← even_iff_two_dvd]
        exact lt_of_lt_of_le (by norm_num)
          ((Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn0).1 hdiv2)
      omega

/-- If `a * b` is even and `b` is odd, then `a` is even. -/
lemma even_of_even_mul_odd {a b : ℕ} (hab : Even (a * b)) (hb : Odd b) :
    Even a := by
  rw [even_iff_two_dvd] at hab ⊢
  exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_two_left).2 hb) hab

/-- In `ZMod p`, the half-order power of a unit of even order is `-1`. -/
lemma unit_pow_half_order_eq_neg_one {p : ℕ} (hp : Nat.Prime p) {x : (ZMod p)ˣ}
    (heven : Even (orderOf x)) :
    (x : ZMod p) ^ (orderOf x / 2) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsq : ((x : ZMod p) ^ (orderOf x / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel heven.two_dvd]
    simpa [orderOf_units] using pow_orderOf_eq_one (x : ZMod p)
  have hneq : (x : ZMod p) ^ (orderOf x / 2) ≠ 1 := by
    intro hx
    have hdiv : orderOf (x : ZMod p) ∣ orderOf x / 2 := orderOf_dvd_of_pow_eq_one hx
    have hpos : 0 < orderOf x := orderOf_pos x
    have hhalfpos : 0 < orderOf x / 2 := by
      obtain ⟨k, hk⟩ := heven
      omega
    rw [orderOf_units] at hdiv
    exact absurd (Nat.le_of_dvd hhalfpos hdiv) (by
      have hlt : orderOf x / 2 < orderOf x := Nat.div_lt_self hpos (by norm_num)
      omega)
  exact (sq_eq_one_iff.mp hsq).resolve_left hneq

/-- If a unit has even order and `n / orderOf x` is odd, then its `n/2`-th power is `-1`. -/
lemma unit_pow_half_mul_odd_eq_neg_one {p : ℕ} (hp : Nat.Prime p) {x : (ZMod p)ˣ}
    {n : ℕ} (hdvd : orderOf x ∣ n) (hodd : Odd (n / orderOf x))
    (heven : Even (orderOf x)) :
    (x : ZMod p) ^ (n / 2) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have heven' : Even (orderOf x) := heven
  obtain ⟨m, hm⟩ := hdvd
  have hquot : n / orderOf x = m := by
    rw [hm, Nat.mul_div_right _ (orderOf_pos x)]
  have hmodd : Odd m := by simpa [hquot] using hodd
  obtain ⟨k, hk⟩ := heven
  have hk2 : orderOf x / 2 = k := by
    rw [hk]
    omega
  have hmul : (k + k) * m = 2 * (k * m) := by ring
  have hn2 : n / 2 = (orderOf x / 2) * m := by
    calc
      n / 2 = ((k + k) * m) / 2 := by rw [hm, hk]
      _ = (2 * (k * m)) / 2 := by rw [hmul]
      _ = k * m := by rw [Nat.mul_div_right (k * m) (by norm_num)]
      _ = (orderOf x / 2) * m := by rw [hk2]
  rw [hn2, pow_mul, unit_pow_half_order_eq_neg_one hp heven']
  simpa using hmodd.neg_one_pow (α := ZMod p)

/-- For a generator `g` of `(ZMod p)ˣ`, the 2-part of `orderOf (g^k)` is maximal iff `k` is odd. -/
lemma order_factorization_two_eq_generator_iff_odd {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : orderOf g = p - 1) (k : ℕ) :
    (orderOf (g ^ k)).factorization 2 = (p - 1).factorization 2 ↔ Odd k := by
  have hEven : Even (p - 1) := by
    rcases hp.odd_of_ne_two hp2 with ⟨t, ht⟩
    use t
    rw [ht]
    omega
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  have hdiv : orderOf (g ^ k) ∣ p - 1 := by
    rw [← hg]
    exact orderOf_pow_dvd k
  have hquot : (p - 1) / orderOf (g ^ k) = Nat.gcd (p - 1) k := by
    rw [orderOf_pow g, hg]
    exact Nat.div_div_self (Nat.gcd_dvd_left _ _) hp1
  rw [eq_comm]
  exact (odd_div_iff_factorization_two_eq (n := p - 1) (d := orderOf (g ^ k)) hp1 hdiv).symm.trans
    (by
      simpa [hquot] using
        (gcd_odd_iff_right_odd_of_left_even hp1 hEven : Odd (Nat.gcd (p - 1) k) ↔ Odd k))

/-- CRT sends the unit corresponding to `a mod pq` to the pair of units modulo `p` and `q`. -/
lemma crt_units_unitOfCoprime {p q a : ℕ} (hcop : Nat.Coprime a (p * q))
    (hpqcop : Nat.Coprime p q) :
    ((Units.mapEquiv (ZMod.chineseRemainder hpqcop).toMulEquiv).trans
      (@MulEquiv.prodUnits (ZMod p) (ZMod q) _ _))
        (ZMod.unitOfCoprime a hcop)
    =
      (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_right p q) hcop),
       ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_left q p) hcop)) := by
  apply Prod.ext <;> apply Units.ext
  · change (ZMod.chineseRemainder hpqcop (a : ZMod (p * q))).1 = (a : ZMod p)
    simp
  · change (ZMod.chineseRemainder hpqcop (a : ZMod (p * q))).2 = (a : ZMod q)
    simp

/-- For a coprime residue mod `pq`, failure of Shor's conditions is equivalent to the
component orders having the same 2-adic valuation. -/
lemma bad_nat_iff_pair_factorization_eq {p q a : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hcop : Nat.Coprime a (p * q)) :
    let up : (ZMod p)ˣ :=
      ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_right p q) hcop)
    let uq : (ZMod q)ˣ :=
      ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_left q p) hcop)
    ¬is_successful_choice a (p * q) ↔
      (orderOf up).factorization 2 = (orderOf uq).factorization 2 := by
  let up : (ZMod p)ˣ :=
    ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_right p q) hcop)
  let uq : (ZMod q)ˣ :=
    ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_left q p) hcop)
  let r := orderOf up
  let s := orderOf uq
  let l := Nat.lcm r s
  have hpqcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hr : orderOf (a : ZMod p) = r := by
    change orderOf ((up : (ZMod p)ˣ) : ZMod p) = r
    simpa [r] using (orderOf_units (y := up))
  have hs : orderOf (a : ZMod q) = s := by
    change orderOf ((uq : (ZMod q)ˣ) : ZMod q) = s
    simpa [s] using (orderOf_units (y := uq))
  have hN : orderOf (a : ZMod (p * q)) = l := by
    simpa [l] using (orderOf_crt_eq_lcm hpqcop a).trans (by rw [hr, hs])
  have hr0 : r ≠ 0 := (orderOf_pos up).ne'
  have hs0 : s ≠ 0 := (orderOf_pos uq).ne'
  have hl0 : l ≠ 0 := Nat.lcm_ne_zero hr0 hs0
  have hl2 : l.factorization 2 = max (r.factorization 2) (s.factorization 2) := by
    simpa [l] using congrArg (fun f => f 2) (Nat.factorization_lcm hr0 hs0)
  constructor
  · intro hbad
    have hbad' := (not_successful_iff a (p * q)).1 hbad
    rcases hbad' with hodd | hneg
    · have hlodd : Odd l := Nat.not_even_iff_odd.mp (by simpa [hN] using hodd)
      have hlzero : l.factorization 2 = 0 := (odd_iff_factorization_two_eq_zero hl0).1 hlodd
      rw [hl2] at hlzero
      have hrzero : r.factorization 2 = 0 := by omega
      have hszero : s.factorization 2 = 0 := by omega
      exact hrzero.trans hszero.symm
    · have hneg' : (a : ZMod (p * q)) ^ (l / 2) = -1 := by simpa [hN] using hneg
      have hpair := (pow_eq_neg_one_crt hpqcop a (l / 2)).1 hneg'
      have hup_ne : up ^ (l / 2) ≠ 1 := by
        intro hup1
        have hpodd := hp.odd_of_ne_two hp2
        haveI : Fact (2 < p) := by
          have hp1 : 1 < p := hp.one_lt
          rcases hpodd with ⟨k, hk⟩
          exact ⟨by omega⟩
        have hEq : (1 : ZMod p) = -1 := by
          calc
            (1 : ZMod p) = ((up ^ (l / 2) : (ZMod p)ˣ) : ZMod p) := by simp [hup1]
            _ = (a : ZMod p) ^ (l / 2) := by simp [up, ZMod.coe_unitOfCoprime]
            _ = -1 := hpair.1
        exact ZMod.neg_one_ne_one hEq.symm
      have huq_ne : uq ^ (l / 2) ≠ 1 := by
        intro huq1
        have hqodd := hq.odd_of_ne_two hq2
        haveI : Fact (2 < q) := by
          have hq1 : 1 < q := hq.one_lt
          rcases hqodd with ⟨k, hk⟩
          exact ⟨by omega⟩
        have hEq : (1 : ZMod q) = -1 := by
          calc
            (1 : ZMod q) = ((uq ^ (l / 2) : (ZMod q)ˣ) : ZMod q) := by simp [huq1]
            _ = (a : ZMod q) ^ (l / 2) := by simp [uq, ZMod.coe_unitOfCoprime]
            _ = -1 := hpair.2
        exact ZMod.neg_one_ne_one hEq.symm
      have hlr_odd : Odd (l / r) := Nat.not_even_iff_odd.mp
        (div_orderOf_odd_of_pow_ne_one (hdvd := Nat.dvd_lcm_left r s) hup_ne)
      have hls_odd : Odd (l / s) := Nat.not_even_iff_odd.mp
        (div_orderOf_odd_of_pow_ne_one (hdvd := Nat.dvd_lcm_right r s) huq_ne)
      have hlr_eq : l.factorization 2 = r.factorization 2 :=
        (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_left r s)).1 hlr_odd
      have hls_eq : l.factorization 2 = s.factorization 2 :=
        (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_right r s)).1 hls_odd
      exact hlr_eq.symm.trans hls_eq
  · intro heq
    have hlr_eq : l.factorization 2 = r.factorization 2 := by
      rw [hl2, heq, max_eq_left le_rfl]
    have hls_eq : l.factorization 2 = s.factorization 2 := by
      rw [hl2, heq, max_eq_right le_rfl]
    have hlr_odd : Odd (l / r) :=
      (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_left r s)).2 hlr_eq
    have hls_odd : Odd (l / s) :=
      (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_right r s)).2 hls_eq
    by_cases hle : Even l
    · have hr_even : Even r := by
        have : Even (r * (l / r)) := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_lcm_left r s)]
          exact hle
        exact even_of_even_mul_odd this hlr_odd
      have hs_even : Even s := by
        have : Even (s * (l / s)) := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_lcm_right r s)]
          exact hle
        exact even_of_even_mul_odd this hls_odd
      have hpowp : (a : ZMod p) ^ (l / 2) = -1 := by
        simpa [up, ZMod.coe_unitOfCoprime] using
          unit_pow_half_mul_odd_eq_neg_one hp (x := up) (n := l) (Nat.dvd_lcm_left r s) hlr_odd hr_even
      have hpowq : (a : ZMod q) ^ (l / 2) = -1 := by
        simpa [uq, ZMod.coe_unitOfCoprime] using
          unit_pow_half_mul_odd_eq_neg_one hq (x := uq) (n := l) (Nat.dvd_lcm_right r s) hls_odd hs_even
      have hneg : (a : ZMod (p * q)) ^ (l / 2) = -1 :=
        (pow_eq_neg_one_crt hpqcop a (l / 2)).2 ⟨hpowp, hpowq⟩
      exact (not_successful_iff a (p * q)).2 (Or.inr (by simpa [hN] using hneg))
    · exact (not_successful_iff a (p * q)).2 (Or.inl (by simpa [hN] using hle))

/-- Multiplying by a generator of `(ZMod p)ˣ` changes the 2-adic valuation of the order. -/
lemma order_factorization_two_mul_generator_ne {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    {g u : (ZMod p)ˣ} (hg : orderOf g = p - 1) :
    (orderOf (u * g)).factorization 2 ≠ (orderOf u).factorization 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hgcard : orderOf g = Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card]
    exact hg.trans (ZMod.card_units p).symm
  have htop : Subgroup.zpowers g = ⊤ := by
    exact (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers g)).mp <| by
      rw [Nat.card_zpowers]
      exact hgcard
  have hu_z : u ∈ Subgroup.zpowers g := by
    simp [htop]
  have hu_p : u ∈ Submonoid.powers g := (mem_powers_iff_mem_zpowers).2 hu_z
  rcases (Submonoid.mem_powers_iff u g).1 hu_p with ⟨k, rfl⟩
  set m := (p - 1).factorization 2
  have hk : (orderOf (g ^ k)).factorization 2 = m ↔ Odd k := by
    simpa [m] using order_factorization_two_eq_generator_iff_odd hp hp2 hg k
  have hk1 : (orderOf (g ^ (k + 1))).factorization 2 = m ↔ Odd (k + 1) := by
    simpa [m] using order_factorization_two_eq_generator_iff_odd hp hp2 hg (k + 1)
  intro hEq
  have hEq' : (orderOf (g ^ (k + 1))).factorization 2 = (orderOf (g ^ k)).factorization 2 := by
    simpa [pow_succ] using hEq
  by_cases hodd : Odd k
  · have hold : (orderOf (g ^ k)).factorization 2 = m := hk.mpr hodd
    have hnew : (orderOf (g ^ (k + 1))).factorization 2 = m := hEq'.trans hold
    have hodd' : Odd (k + 1) := hk1.mp hnew
    rcases hodd with ⟨a, ha⟩
    rcases hodd' with ⟨b, hb⟩
    omega
  · have heven : Even k := (Nat.not_odd_iff_even).mp hodd
    have hodd' : Odd (k + 1) := by
      rcases heven with ⟨a, ha⟩
      use a
      omega
    have hnew : (orderOf (g ^ (k + 1))).factorization 2 = m := hk1.mpr hodd'
    have hold : (orderOf (g ^ k)).factorization 2 = m := hEq'.symm.trans hnew
    exact hodd (hk.mp hold)

/-- Among coprime residues mod pq, at most half are unsuccessful for Shor's algorithm.

    Proof strategy (injection via generator multiplication):
    By CRT, (ℤ/pqℤ)* ≅ (ℤ/pℤ)* × (ℤ/qℤ)*. Choose c via CRT with c ≡ g (mod p) where
    g generates (ℤ/pℤ)*, and c ≡ 1 (mod q). Then multiplication by c sends every
    unsuccessful element to a successful one, giving |unsuccessful| ≤ |successful|.

    The key insight: in a cyclic group of even order n with generator g, exactly one of
    {u, u·g} has order dividing n/2 (since u = g^j and j, j+1 have different parities).
    This means multiplying by g always changes the "2-adic type" of an element's order,
    breaking the v₂-matching condition that characterizes unsuccessful elements. -/
lemma unsuccessful_bound {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    2 * ((Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))).card
    ≤ (p - 1) * (q - 1) := by
  let hpqcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  let φ : (ZMod (p * q))ˣ ≃* ((ZMod p)ˣ × (ZMod q)ˣ) :=
    (Units.mapEquiv (ZMod.chineseRemainder hpqcop).toMulEquiv).trans
      (@MulEquiv.prodUnits (ZMod p) (ZMod q) _ _)
  let badNat :=
    (Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))
  let pairBadPred : ((ZMod p)ˣ × (ZMod q)ˣ) → Prop := fun uv =>
    (orderOf uv.1).factorization 2 = (orderOf uv.2).factorization 2
  let badPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := Finset.univ.filter pairBadPred
  let goodPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := Finset.univ.filter (fun uv => ¬pairBadPred uv)
  let natToPair : ℕ → ((ZMod p)ˣ × (ZMod q)ˣ) := fun a =>
    if hcop : Nat.Coprime a (p * q) then φ (ZMod.unitOfCoprime a hcop) else 1
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ :=
    isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  have hg : orderOf g = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
    exact hg
  let shift : ((ZMod p)ˣ × (ZMod q)ˣ) → ((ZMod p)ˣ × (ZMod q)ˣ) := fun uv => (uv.1 * g, uv.2)
  have h_badPairs_le_goodPairs : badPairs.card ≤ goodPairs.card := by
    apply Finset.card_le_card_of_injOn shift
    · intro uv huv
      have huv_bad : pairBadPred uv := by
        simpa [badPairs] using huv
      change shift uv ∈ Finset.univ.filter (fun uv => ¬pairBadPred uv)
      simp [Finset.mem_filter]
      intro hshift_bad
      exact order_factorization_two_mul_generator_ne hp hp2 hg <|
        hshift_bad.trans huv_bad.symm
    · intro uv _ vw _ hEq
      rcases Prod.mk.inj hEq with ⟨h1, h2⟩
      apply Prod.ext
      · exact mul_right_cancel h1
      · exact h2
  have h_pair_partition :
      badPairs.card + goodPairs.card = (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := by
    simpa [badPairs, goodPairs] using
      (Finset.card_filter_add_card_filter_not pairBadPred
        (s := (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ))))
  have h_badPairs_bound :
      2 * badPairs.card ≤ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := by
    omega
  have h_badNat_le_badPairs : badNat.card ≤ badPairs.card := by
    apply Finset.card_le_card_of_injOn natToPair
    · intro a ha
      change a ∈ (Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q)) at ha
      rw [Finset.mem_filter] at ha
      have hcop : Nat.Coprime a (p * q) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact ha.2.1
      change natToPair a ∈ Finset.univ.filter pairBadPred
      simp [Finset.mem_filter]
      have hnatToPair : natToPair a = φ (ZMod.unitOfCoprime a hcop) := by
        dsimp [natToPair]
        rw [dif_pos hcop]
      rw [hnatToPair, crt_units_unitOfCoprime hcop hpqcop]
      simpa [pairBadPred] using
        (bad_nat_iff_pair_factorization_eq hp hq hpq hp2 hq2 hcop).1 ha.2.2
    · intro a ha b hb hEq
      change a ∈ (Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q)) at ha
      change b ∈ (Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q)) at hb
      rw [Finset.mem_filter] at ha hb
      have hacop : Nat.Coprime a (p * q) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact ha.2.1
      have hbcop : Nat.Coprime b (p * q) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact hb.2.1
      have ha_lt : a < p * q := Finset.mem_range.mp ha.1
      have hb_lt : b < p * q := Finset.mem_range.mp hb.1
      have hnatToPairA : natToPair a = φ (ZMod.unitOfCoprime a hacop) := by
        dsimp [natToPair]
        rw [dif_pos hacop]
      have hnatToPairB : natToPair b = φ (ZMod.unitOfCoprime b hbcop) := by
        dsimp [natToPair]
        rw [dif_pos hbcop]
      have hunit : ZMod.unitOfCoprime a hacop = ZMod.unitOfCoprime b hbcop := by
        apply φ.injective
        calc
          φ (ZMod.unitOfCoprime a hacop) = natToPair a := hnatToPairA.symm
          _ = natToPair b := hEq
          _ = φ (ZMod.unitOfCoprime b hbcop) := hnatToPairB
      have hzmod : (a : ZMod (p * q)) = (b : ZMod (p * q)) := by
        simpa [ZMod.coe_unitOfCoprime] using congrArg (fun u : (ZMod (p * q))ˣ => (u : ZMod (p * q))) hunit
      have hmod := (ZMod.natCast_eq_natCast_iff' a b (p * q)).1 hzmod
      simpa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] using hmod
  have h_pair_card :
      (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card = (p - 1) * (q - 1) := by
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card_units, ZMod.card_units]
  calc
    2 * ((Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))).card
      = 2 * badNat.card := by rfl
    _ ≤ 2 * badPairs.card := Nat.mul_le_mul_left 2 h_badNat_le_badPairs
    _ ≤ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := h_badPairs_bound
    _ = (p - 1) * (q - 1) := h_pair_card

/-- Core CRT + cyclic counting bound.
    Among all φ(pq) = (p-1)(q-1) coprime residues mod pq, at least half satisfy
    Shor's success conditions. Proved from coprime_count + unsuccessful_bound
    via the partition identity: successful + unsuccessful = total. -/
lemma crt_counting_bound {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    2 * ((Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ is_successful_choice a (p * q))).card
    ≥ (p - 1) * (q - 1) := by
  -- Let S be the set of coprime residues
  set S := (Finset.range (p * q)).filter (fun a => Nat.gcd a (p * q) = 1) with hS_def
  set T := (p - 1) * (q - 1) with hT_def
  -- Express the successful and unsuccessful filters as sub-filters of S
  have h_succ : (Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ is_successful_choice a (p * q))
    = S.filter (fun a => is_successful_choice a (p * q)) := by
    rw [hS_def]; rw [Finset.filter_filter]
  have h_unsucc : (Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))
    = S.filter (fun a => ¬is_successful_choice a (p * q)) := by
    rw [hS_def]; rw [Finset.filter_filter]
  -- Partition: successful.card + unsuccessful.card = S.card = T
  have h_card_S : S.card = T := coprime_count hp hq hpq
  have h_partition := Finset.card_filter_add_card_filter_not
    (fun a => is_successful_choice a (p * q)) (s := S)
  -- Get the unsuccessful bound
  have h_unsucc_bound : 2 * (S.filter (fun a => ¬is_successful_choice a (p * q))).card ≤ T := by
    rw [← h_unsucc]; exact unsuccessful_bound hp hq hpq hp2 hq2
  rw [h_succ]
  omega

/-- For distinct odd primes p, q dividing N, if a is coprime to N and unsuccessful,
    then the 2-adic valuations of its orders mod p and mod q match.
    This is the forward direction of the "bad" characterization, generalised from N = pq
    to arbitrary N with p ∣ N, q ∣ N. -/
lemma unsuccessful_implies_v2_match {N p q a : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (_hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpN : p ∣ N) (hqN : q ∣ N)
    (hcop : Nat.Coprime a N)
    (hbad : ¬is_successful_choice a N) :
    (orderOf (a : ZMod p)).factorization 2 = (orderOf (a : ZMod q)).factorization 2 := by
  let l := orderOf (a : ZMod N)
  have hap : Nat.Coprime a p := Nat.Coprime.of_dvd_right hpN hcop
  have haq : Nat.Coprime a q := Nat.Coprime.of_dvd_right hqN hcop
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hap0 : (a : ZMod p) ≠ 0 := by
    intro h0
    exact (hp.coprime_iff_not_dvd).1 hap.symm <| (zmod_eq_zero_iff_dvd (N := p) a).1 h0
  have haq0 : (a : ZMod q) ≠ 0 := by
    intro h0
    exact (hq.coprime_iff_not_dvd).1 haq.symm <| (zmod_eq_zero_iff_dvd (N := q) a).1 h0
  let r := orderOf (a : ZMod p)
  let s := orderOf (a : ZMod q)
  have hpord_pos : 0 < r := by
    exact Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one hap0) (Nat.sub_pos_of_lt hp.one_lt)
  have hqord_pos : 0 < s := by
    exact Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one haq0) (Nat.sub_pos_of_lt hq.one_lt)
  have hpdvd : r ∣ l := by
    simpa [l, r] using (orderOf_map_dvd (ZMod.castHom hpN (ZMod p)).toMonoidHom (a : ZMod N))
  have hqdvd : s ∣ l := by
    simpa [l, s] using (orderOf_map_dvd (ZMod.castHom hqN (ZMod q)).toMonoidHom (a : ZMod N))
  have hbad' := (not_successful_iff a N).1 hbad
  rcases hbad' with hl_odd | hneg
  · have hlodd : Odd l := Nat.not_even_iff_odd.mp hl_odd
    have hl0 : l ≠ 0 := by
      rcases hlodd with ⟨k, hk⟩
      omega
    have hpfac0 : r.factorization 2 = 0 := by
      have hle := (Nat.factorization_le_iff_dvd hpord_pos.ne' hl0).2 hpdvd 2
      have hl2 : l.factorization 2 = 0 := (odd_iff_factorization_two_eq_zero hl0).1 hlodd
      omega
    have hqfac0 : s.factorization 2 = 0 := by
      have hle := (Nat.factorization_le_iff_dvd hqord_pos.ne' hl0).2 hqdvd 2
      have hl2 : l.factorization 2 = 0 := (odd_iff_factorization_two_eq_zero hl0).1 hlodd
      omega
    simpa [r, s] using hpfac0.trans hqfac0.symm
  · have hpowp : (a : ZMod p) ^ (l / 2) = -1 := by
      have hmap := congrArg (ZMod.castHom hpN (ZMod p)) hneg
      rw [map_pow, map_neg, map_one] at hmap
      simpa [l, ZMod.castHom_apply] using hmap
    have hpowq : (a : ZMod q) ^ (l / 2) = -1 := by
      have hmap := congrArg (ZMod.castHom hqN (ZMod q)) hneg
      rw [map_pow, map_neg, map_one] at hmap
      simpa [l, ZMod.castHom_apply] using hmap
    have hp_gt_two : 2 < p := by
      have hp1 : 1 < p := hp.one_lt
      omega
    have hq_gt_two : 2 < q := by
      have hq1 : 1 < q := hq.one_lt
      omega
    haveI : Fact (2 < p) := ⟨hp_gt_two⟩
    haveI : Fact (2 < q) := ⟨hq_gt_two⟩
    have hpowp_ne : (a : ZMod p) ^ (l / 2) ≠ 1 := by
      intro h1
      exact ZMod.neg_one_ne_one (hpowp.symm.trans h1)
    have hpowq_ne : (a : ZMod q) ^ (l / 2) ≠ 1 := by
      intro h1
      exact ZMod.neg_one_ne_one (hpowq.symm.trans h1)
    have hl0 : l ≠ 0 := by
      intro hlz
      exact ZMod.neg_one_ne_one (by simpa [hlz] using hpowp.symm)
    have hpodd : Odd (l / r) :=
      Nat.not_even_iff_odd.mp <| by
        intro hEven
        rcases hEven with ⟨k, hk⟩
        apply hpowp_ne
        have hl_eq : l = r * (2 * k) := by
          have hmul := Nat.div_mul_cancel hpdvd
          rw [hk] at hmul
          calc
            l = (k + k) * r := hmul.symm
            _ = r * (2 * k) := by ring
        have hhalf : l / 2 = r * k := by
          calc
            l / 2 = (r * (2 * k)) / 2 := by rw [hl_eq]
            _ = (2 * (r * k)) / 2 := by ring_nf
            _ = r * k := by rw [Nat.mul_div_right (r * k) (by norm_num)]
        have hpowr : (a : ZMod p) ^ r = 1 := by
          simp [r]
        rw [hhalf, pow_mul, hpowr, one_pow]
    have hqodd : Odd (l / s) :=
      Nat.not_even_iff_odd.mp <| by
        intro hEven
        rcases hEven with ⟨k, hk⟩
        apply hpowq_ne
        have hl_eq : l = s * (2 * k) := by
          have hmul := Nat.div_mul_cancel hqdvd
          rw [hk] at hmul
          calc
            l = (k + k) * s := hmul.symm
            _ = s * (2 * k) := by ring
        have hhalf : l / 2 = s * k := by
          calc
            l / 2 = (s * (2 * k)) / 2 := by rw [hl_eq]
            _ = (2 * (s * k)) / 2 := by ring_nf
            _ = s * k := by rw [Nat.mul_div_right (s * k) (by norm_num)]
        have hpows : (a : ZMod q) ^ s = 1 := by
          simp [s]
        rw [hhalf, pow_mul, hpows, one_pow]
    have hpfac : l.factorization 2 = r.factorization 2 :=
      (odd_div_iff_factorization_two_eq hl0 hpdvd).1 hpodd
    have hqfac : l.factorization 2 = s.factorization 2 :=
      (odd_div_iff_factorization_two_eq hl0 hqdvd).1 hqodd
    simpa [r, s] using hpfac.symm.trans hqfac

/-- Pure pair counting: among all pairs in (ℤ/pℤ)ˣ × (ℤ/qℤ)ˣ, at most half have
    matching 2-adic valuations of their component orders.
    Proved by the shift injection (u,v) ↦ (u·g, v) where g generates (ℤ/pℤ)ˣ. -/
lemma bad_pairs_le_half {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : p ≠ 2) (_hq2 : q ≠ 2) :
    letI : NeZero p := ⟨hp.ne_zero⟩; letI : NeZero q := ⟨hq.ne_zero⟩
    2 * (Finset.univ.filter (fun uv : (ZMod p)ˣ × (ZMod q)ˣ =>
      (orderOf uv.1).factorization 2 = (orderOf uv.2).factorization 2)).card
    ≤ Fintype.card ((ZMod p)ˣ × (ZMod q)ˣ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  let pairBadPred : ((ZMod p)ˣ × (ZMod q)ˣ) → Prop := fun uv =>
    (orderOf uv.1).factorization 2 = (orderOf uv.2).factorization 2
  let badPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := Finset.univ.filter pairBadPred
  let goodPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := Finset.univ.filter (fun uv => ¬pairBadPred uv)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ :=
    isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  have hg : orderOf g = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
    exact hg
  let shift : ((ZMod p)ˣ × (ZMod q)ˣ) → ((ZMod p)ˣ × (ZMod q)ˣ) := fun uv => (uv.1 * g, uv.2)
  have h_badPairs_le_goodPairs : badPairs.card ≤ goodPairs.card := by
    apply Finset.card_le_card_of_injOn shift
    · intro uv huv
      have huv_bad : pairBadPred uv := by
        simpa [badPairs] using huv
      change shift uv ∈ Finset.univ.filter (fun uv => ¬pairBadPred uv)
      simp [Finset.mem_filter]
      intro hshift_bad
      exact order_factorization_two_mul_generator_ne hp hp2 hg <|
        hshift_bad.trans huv_bad.symm
    · intro uv _ vw _ hEq
      rcases Prod.mk.inj hEq with ⟨h1, h2⟩
      apply Prod.ext
      · exact mul_right_cancel h1
      · exact h2
  have h_pair_partition :
      badPairs.card + goodPairs.card = (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := by
    simpa [badPairs, goodPairs] using
      (Finset.card_filter_add_card_filter_not pairBadPred
        (s := (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ))))
  have h_badPairs_bound :
      2 * badPairs.card ≤ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := by
    omega
  simpa [badPairs] using h_badPairs_bound

/-- The main counting bound for general N: at most half of the coprime residues mod N
    are unsuccessful for Shor's algorithm.

    Proof: Define pairBad(a) = v₂(ord_p(a)) = v₂(ord_q(a)). Then:
    • unsuccessful ⊆ pairBad (via unsuccessful_implies_v2_match)
    • pairBad depends only on (a mod p, a mod q), which lives in (ℤ/pℤ)ˣ × (ℤ/qℤ)ˣ
    • The shift (u,v) ↦ (u·g, v) injects bad pairs into good pairs (bad_pairs_le_half)
    • Via the surjection (ℤ/Nℤ)ˣ ↠ (ℤ/pℤ)ˣ × (ℤ/qℤ)ˣ with uniform fibers,
      this lifts to |{pairBad}| ≤ φ(N)/2 -/
lemma general_unsuccessful_bound {N p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpN : p ∣ N) (hqN : q ∣ N) :
    2 * ((Finset.range N).filter (fun a =>
      Nat.gcd a N = 1 ∧ ¬is_successful_choice a N)).card
    ≤ Nat.totient N := by
  by_cases hN0 : N = 0
  · subst hN0
    simp
  · letI : NeZero N := ⟨hN0⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero q := ⟨hq.ne_zero⟩
    let U := (ZMod N)ˣ
    haveI : Fintype U := by dsimp [U]; infer_instance
    haveI : DecidableEq U := by dsimp [U]; infer_instance
    let hpqcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hpqN : p * q ∣ N := hpqcop.mul_dvd_of_dvd_of_dvd hpN hqN
    let φpq : (ZMod (p * q))ˣ ≃* ((ZMod p)ˣ × (ZMod q)ˣ) :=
      (Units.mapEquiv (ZMod.chineseRemainder hpqcop).toMulEquiv).trans
        (@MulEquiv.prodUnits (ZMod p) (ZMod q) _ _)
    let ψ : U →* ((ZMod p)ˣ × (ZMod q)ˣ) := φpq.toMonoidHom.comp (ZMod.unitsMap hpqN)
    let pairBadPred : ((ZMod p)ˣ × (ZMod q)ˣ) → Prop := fun uv =>
      (orderOf uv.1).factorization 2 = (orderOf uv.2).factorization 2
    let badPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := Finset.univ.filter pairBadPred
    let badUnits : Finset U := Finset.univ.filter (fun u => pairBadPred (ψ u))
    let badNat := (Finset.range N).filter (fun a =>
      Nat.gcd a N = 1 ∧ ¬is_successful_choice a N)
    let n := ((Finset.univ : Finset U).filter fun u => ψ u = 1).card
    let natToUnit : ℕ → U := fun a =>
      if hcop : Nat.Coprime a N then ZMod.unitOfCoprime a hcop else 1
    have hψ_surj : Function.Surjective ψ := by
      intro uv
      obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hpqN (φpq.symm uv)
      refine ⟨u, ?_⟩
      change φpq (ZMod.unitsMap hpqN u) = uv
      rw [hu, φpq.apply_symm_apply]
    have h_fiber : ∀ uv : ((ZMod p)ˣ × (ZMod q)ˣ),
        ((Finset.univ : Finset U).filter fun u => ψ u = uv).card = n := by
      intro uv
      simpa [n] using (MonoidHom.card_fiber_eq_of_mem_range ψ (hψ_surj uv) (hψ_surj 1))
    have hψ_unitOfCoprime {a : ℕ} (hcop : Nat.Coprime a N) :
        ψ (ZMod.unitOfCoprime a hcop)
          =
            (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hpN hcop),
             ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hqN hcop)) := by
      have hacop_pq : Nat.Coprime a (p * q) := Nat.Coprime.of_dvd_right hpqN hcop
      have hu_pq :
          ZMod.unitsMap hpqN (ZMod.unitOfCoprime a hcop) = ZMod.unitOfCoprime a hacop_pq := by
        apply Units.ext
        change ((((ZMod.unitOfCoprime a hcop : U) : ZMod N)).cast : ZMod (p * q)) = (a : ZMod (p * q))
        rw [ZMod.coe_unitOfCoprime]
        simpa using (ZMod.cast_natCast (R := ZMod (p * q)) hpqN a)
      calc
        ψ (ZMod.unitOfCoprime a hcop) = φpq (ZMod.unitsMap hpqN (ZMod.unitOfCoprime a hcop)) := by
          rfl
        _ = φpq (ZMod.unitOfCoprime a hacop_pq) := by rw [hu_pq]
        _ =
            (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hpN hcop),
             ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hqN hcop)) := by
          simpa [φpq] using crt_units_unitOfCoprime hacop_pq hpqcop
    have h_pairBad_of_unsuccessful {a : ℕ} (hcop : Nat.Coprime a N)
        (hbad : ¬is_successful_choice a N) :
        pairBadPred (ψ (ZMod.unitOfCoprime a hcop)) := by
      have hmatch := unsuccessful_implies_v2_match hp hq hpq hp2 hq2 hpN hqN hcop hbad
      have hpord :
          orderOf (a : ZMod p) =
            orderOf (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hpN hcop)) := by
        simpa [ZMod.coe_unitOfCoprime] using
          (orderOf_units (y := ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hpN hcop)))
      have hqord :
          orderOf (a : ZMod q) =
            orderOf (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hqN hcop)) := by
        simpa [ZMod.coe_unitOfCoprime] using
          (orderOf_units (y := ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hqN hcop)))
      rw [hψ_unitOfCoprime hcop]
      change
        (orderOf (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hpN hcop))).factorization 2
          =
        (orderOf (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right hqN hcop))).factorization 2
      simpa [hpord, hqord] using hmatch
    have h_badNat_le_badUnits : badNat.card ≤ badUnits.card := by
      apply Finset.card_le_card_of_injOn natToUnit
      · intro a ha
        change a ∈ (Finset.range N).filter (fun a => Nat.gcd a N = 1 ∧ ¬is_successful_choice a N) at ha
        rw [Finset.mem_filter] at ha
        have hacop : Nat.Coprime a N := by
          rw [Nat.coprime_iff_gcd_eq_one]
          exact ha.2.1
        change natToUnit a ∈ Finset.univ.filter (fun u => pairBadPred (ψ u))
        rw [Finset.mem_filter]
        refine ⟨by simp, ?_⟩
        dsimp [natToUnit]
        simpa [dif_pos hacop] using h_pairBad_of_unsuccessful hacop ha.2.2
      · intro a ha b hb hEq
        change a ∈ (Finset.range N).filter (fun a => Nat.gcd a N = 1 ∧ ¬is_successful_choice a N) at ha
        change b ∈ (Finset.range N).filter (fun a => Nat.gcd a N = 1 ∧ ¬is_successful_choice a N) at hb
        rw [Finset.mem_filter] at ha hb
        have hacop : Nat.Coprime a N := by
          rw [Nat.coprime_iff_gcd_eq_one]
          exact ha.2.1
        have hbcop : Nat.Coprime b N := by
          rw [Nat.coprime_iff_gcd_eq_one]
          exact hb.2.1
        have ha_lt : a < N := Finset.mem_range.mp ha.1
        have hb_lt : b < N := Finset.mem_range.mp hb.1
        have hnatA : natToUnit a = ZMod.unitOfCoprime a hacop := by
          simp [natToUnit, dif_pos hacop]
        have hnatB : natToUnit b = ZMod.unitOfCoprime b hbcop := by
          simp [natToUnit, dif_pos hbcop]
        have hunit : ZMod.unitOfCoprime a hacop = ZMod.unitOfCoprime b hbcop := by
          calc
            ZMod.unitOfCoprime a hacop = natToUnit a := hnatA.symm
            _ = natToUnit b := hEq
            _ = ZMod.unitOfCoprime b hbcop := hnatB
        have hzmod : (a : ZMod N) = (b : ZMod N) := by
          simpa [U, ZMod.coe_unitOfCoprime] using
            congrArg (fun u : U => (u : ZMod N)) hunit
        have hmod := (ZMod.natCast_eq_natCast_iff' a b N).1 hzmod
        simpa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] using hmod
    have h_badPairs_bound : 2 * badPairs.card ≤ Fintype.card ((ZMod p)ˣ × (ZMod q)ˣ) := by
      simpa [badPairs, pairBadPred] using bad_pairs_le_half hp hq hp2 hq2
    have h_badUnits_le : badUnits.card ≤ n * badPairs.card := by
      refine Finset.card_le_mul_card_image_of_maps_to (s := badUnits) (t := badPairs) (f := ψ) ?_ n ?_
      · intro u hu
        simpa [badUnits, badPairs] using hu
      · intro uv huv
        have huv_bad : pairBadPred uv := by
          simpa [badPairs] using huv
        have hfilter_eq :
            badUnits.filter (fun u => ψ u = uv) = (Finset.univ : Finset U).filter (fun u => ψ u = uv) := by
          ext u
          by_cases hu : ψ u = uv
          · simp [badUnits, hu, huv_bad]
          · simp [badUnits, hu]
        calc
          (badUnits.filter fun u => ψ u = uv).card
              = ((Finset.univ : Finset U).filter fun u => ψ u = uv).card := by
            rw [hfilter_eq]
          _ = n := h_fiber uv
          _ ≤ n := le_rfl
    have h_total_lower : n * Fintype.card ((ZMod p)ˣ × (ZMod q)ˣ) ≤ Fintype.card U := by
      have himage :
          (Finset.univ : Finset U).image ψ = (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)) := by
        ext uv
        simp [hψ_surj uv]
      have htmp :
          n * ((Finset.univ : Finset U).image ψ).card ≤ (Finset.univ : Finset U).card := by
        refine Finset.mul_card_image_le_card (s := (Finset.univ : Finset U)) (f := ψ) n ?_
        intro uv huv
        rw [h_fiber uv]
      have htmp' : n * Fintype.card ((ZMod p)ˣ × (ZMod q)ˣ) ≤ Fintype.card U := by
        simpa [himage, U] using htmp
      exact htmp'
    have hUcard : Fintype.card U = Nat.totient N := by
      simp [U]
    calc
      2 * ((Finset.range N).filter (fun a => Nat.gcd a N = 1 ∧ ¬is_successful_choice a N)).card
        = 2 * badNat.card := by rfl
      _ ≤ 2 * badUnits.card := Nat.mul_le_mul_left 2 h_badNat_le_badUnits
      _ ≤ 2 * (n * badPairs.card) := Nat.mul_le_mul_left 2 h_badUnits_le
      _ = n * (2 * badPairs.card) := by ring
      _ ≤ n * Fintype.card ((ZMod p)ˣ × (ZMod q)ˣ) := Nat.mul_le_mul_left n h_badPairs_bound
      _ ≤ Fintype.card U := h_total_lower
      _ = Nat.totient N := hUcard

/-- Lemma for defining the conditions for 'a', given that a is a successful choice -/
lemma success_eq_conditions (a N : ℕ) (h : a ∈ successful_choices N) :
(1 < a ∧ a < N) ∧ Nat.gcd a N = 1 := by {
  unfold successful_choices valid_choices at h
  simp [Finset.mem_filter] at h
  simp [h.1]
}
