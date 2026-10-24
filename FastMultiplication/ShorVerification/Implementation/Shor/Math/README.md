# `Math/`

Pure math, no framework/register dependencies: number-theory, Fourier/
geometric-sum, and counting lemmas backing the ideal order-finding
good-outcome analysis. Import closure is Mathlib plus the project's
semantics-free vocabulary (`ord`, `qftPhase`, `GoodOutcome`) — no
`QSemantics`, `eval`, or measurement.

Three files. `OrderFindingAnalysis.lean` carries no internal section banners; it
was moved byte-for-byte out of the single `Proofs/NaiveShor/Lemmas.lean` that
preceded today's `NaiveShor/` split (`Preliminaries.lean`,
`PhaseEstimation.lean`, `GoodOutcomeMassLowerBound.lean`), so the grouping below
follows its actual top-to-bottom logical flow rather than author-labeled
sections. `TotientBounds.lean` and `TotientBoundsLarge.lean` are sectioned;
together they prove the `Ω(1 / log log N)` totient bound the success constant
`κ = 1/π²` is stated with — `TotientBounds.lean` below `2 ^ 2048` by a finite
case split (Mathlib only), `TotientBoundsLarge.lean` above it by Mertens' third
theorem (which is vendored, see `Vendor/Mertens/README.md`). This file's own
totient lemmas are the `r < 255` end of that case split.

## `OrderFindingAnalysis.lean`

### Multiplicative order

- **`ord_pos_of_gcd`** — `ord a N hgcd > 0` (the order of a unit is
  positive), via `orderOf_pos` on `ZMod.unitOfCoprime`.
- **`pow_ord_mod_eq_one`** — `a ^ (ord a N hgcd) ≡ 1 (mod N)` for `N > 1`,
  transporting `pow_orderOf_eq_one` from `(ZMod N)ˣ` back to `ℕ`.
- **`ord_le_of_pow_mod_eq_one`** — the order is the *least* positive
  exponent with `aᵈ ≡ 1`: any positive `d` with `aᵈ ≡ 1 (mod N)` satisfies
  `ord a N hgcd ≤ d`, via `orderOf_le_of_pow_eq_one`.

### Register-capacity and modular-exponentiation accumulation arithmetic

- **`pow_log2_two_mul_bounds`** — `n < 2^(log₂ 2n) ≤ 2n` for `n > 0`: the
  register-capacity sandwich used to size registers from `log2` widths.
- **`modexp_step_arith`** — the per-qubit modular-exponentiation
  accumulation identity: conditionally multiplying by `a^(2^e) mod N` then
  folding in the rest of the exponent (`a^(2^(e+1)·t)`) equals directly
  raising to `a^(2^e·(bit + 2t))`, mod `N`. The arithmetic core of the
  controlled-modular-exponentiation recursion.
- **`sum_two_pow_toNat_testBit`** — binary decomposition: a natural below
  `2^w` equals the weighted sum of its low `w` bits
  (`∑ i < w, 2^i · (n.testBit i).toNat = n`). Bridges per-qubit exponent
  accumulation to `RegEncoding.toNat`.

### Period-class and spectral amplitudes (the QPE Fourier machinery)

- **`goodOutcomeIndicator`** — `1` if `GoodOutcome o Q r` holds, else `0`, as
  a real number (for use inside finite sums).
- **`shorPeriodClassAmplitude`** — the contribution of one residue class
  `s mod r` to observing output `o`: `(1/Q) · ∑_{t<Q, t≡s mod r} conj(qftPhase Q t o)`
  (Shor's substitution `t = j·r + s`; conjugated because the circuit applies
  an inverse QFT).
- **`shorPaperOutcomeProb`** — Shor's marginal probability of observing
  output `o`, summing `‖shorPeriodClassAmplitude‖²` over the `r` residue
  classes (the marginal version of the paper's equations (5.5)–(5.7)).
- **`sum_range_group_by_mod`** — regroups a sum over `range Q` by residue
  class mod `r`, via a `Finset.sum_comm`/indicator rewrite; the combinatorial
  engine behind `shorSpectralAmplitude_eq_period_classes`.
- **`shorSpectralAmplitude`** — the Fourier coefficient (in character `k`) of
  the period-class amplitude vector: `(1/Q) · ∑_{t<Q} qftPhase r t k · conj(qftPhase Q t o)`.
- **`shorQPEAmplitude`** — the same amplitude reindexed as an ordinary
  normalized QPE geometric sum over the rational-frequency difference
  `δ = k/r - o/Q`.
- **`shorSpectralAmplitude_eq_period_classes`** — `shorSpectralAmplitude`
  equals the character-weighted sum of `shorPeriodClassAmplitude` over
  residue classes, via `sum_range_group_by_mod` and `qftPhase_mod_left_shor`.
- **`sq_sum_le_card_mul_sum_sq_shor`** / **`norm_sum_le_sum_norm_shor`** —
  generic Cauchy–Schwarz-style (`(∑f)² ≤ |S|·∑f²`) and triangle-inequality
  (`‖∑f‖ ≤ ∑‖f‖`) helpers over a `Finset`, proved by induction; used to bound
  the spectral amplitude sums that follow.
- **`shorSpectralAmplitude_sq_le_paper`** — Cauchy–Schwarz bound:
  `‖shorSpectralAmplitude Q r k o‖² ≤ r · shorPaperOutcomeProb Q r o`.
- **`shorSpectralAmplitude_eq_qpe`** — `shorSpectralAmplitude` and
  `shorQPEAmplitude` coincide (rewriting `qftPhase` as a complex exponential
  and matching exponents).
- **`norm_natCast_complex_shor`** — `‖(n : ℂ)‖ = (n : ℝ)` for `n : ℕ`, a
  trivial norm-cast helper reused below.

### The Fourier-peak lower bound

- **`shor_normalized_geometric_peak`** — the analytic heart: if
  `|δ| ≤ 1/(2Q)`, the normalized geometric sum
  `(1/Q)·∑_{t<Q} e^{2πiδ}ᵗ` has norm at least `2/π`. Proved via the
  geometric-sum identity `G·(ζ-1) = ζ^Q - 1`, a chord bound on `|ζ-1|`
  (`Real.norm_exp_I_mul_ofReal_sub_one_le`), Jordan's inequality
  (`Real.mul_abs_le_abs_sin`) to lower-bound `|ζ^Q - 1|`, and dividing
  through.
- **`shor_paper_peak_lower_bound`** — if `o` is a `1/(2Q)`-good rational
  approximation to `k/r` (`approxRat`), then
  `(4/π²)·(1/r) ≤ shorPaperOutcomeProb Q r o`: squares the `2/π` amplitude
  bound above and combines it with the Cauchy–Schwarz bound via
  `shorSpectralAmplitude_eq_qpe`. This is the analytic heart of Shor's
  equations (5.7)–(5.13).
- **`shor_paper_goodOutcome_lower_bound`** — restates the above for any
  `GoodOutcome o Q r` (just unpacks the existential `k`; no new analytic
  work).

### Counting good outcomes

- **`goodOutcomeFinset`** — the finite set of outputs `o : Fin Q` satisfying
  `GoodOutcome o Q r`; **`mem_goodOutcomeFinset`** (`@[simp]`) is its
  membership characterization.
- **`shorNearestOutput`** — the integer nearest `Q·k/r` (`⌊Qk/r + 1/2⌋`), the
  candidate good output for residue `k`.
- **`shorNearestOutput_spec`** — for `k < r` and `r² ≤ Q`: the nearest
  output is `< Q` and is a `1/(2Q)`-good approximation to `k/r`
  (`approxRat`) — established via careful floor-function bookkeeping,
  showing the rounding gap can't overflow past `Q`.
- **`shorNearestOutput_injective_below`** — distinct `k₁, k₂ < r` (with
  `r² ≤ Q`) give distinct nearest outputs: two outputs within `1/(2Q)` of
  their targets would force `|k₁-k₂|/r ≤ 1/Q`, contradicting `Q ≤ r` unless
  `k₁ = k₂`.
- **`goodOutcome_card_ge_totient`** — Shor's counting step: for `r² < Q`,
  `φ(r) ≤ |goodOutcomeFinset Q r|`, via an explicit injection from
  `{k < r : gcd(r,k) = 1}` (cardinality `φ(r)` by
  `Nat.totient_eq_card_coprime`) into good outcomes, using
  `shorNearestOutput_spec` for well-definedness and
  `shorNearestOutput_injective_below` for injectivity.
- **`goodOutcome_mass_lower_bound_from_card_and_pointwise`** — pure
  finite-sum bookkeeping (no quantum content): given at least `φ(r)` good
  outputs each with pointwise probability `≥ (4/π²)/r`, the total good-outcome
  probability mass is `≥ (4/π²)·φ(r)/r`.

### Totient lower bound (from `r` to `log₂ N`)

A chain converting the totient-ratio bound into one depending only on
`log₂ N`: `φ(r)/r ≥ 1/(log₂ N + 1)`, from the count of distinct prime factors.
The success bound uses `φ(r)/r ≥ 1 / (4 · log(log₂ N + 1))`
(`shor_totient_ratio_lower_bound`, in
`Proofs/NaiveShor/GoodOutcomeMassLowerBound.lean`), proved by a case split on
`r`; the lemmas here discharge the `r < 255` case, where `1/(log₂ N + 1)` is
already at least `1 / (4 · log(log₂ N + 1))`.

- **`le_log2_of_two_pow_le`** — `2^c ≤ N` and `N > 0` imply `c ≤ log₂ N`, by
  induction on `c` unfolding `Nat.log2`.
- **`two_pow_card_le_prod`** — for a finite set `S` of naturals all `≥ 2`,
  `2^|S| ≤ ∏_{p∈S} p`, by induction on `S`.
- **`primeFactors_card_le_log2`** — for `0 < r < N`,
  `|r.primeFactors| ≤ log₂ N`: combines `two_pow_card_le_prod` (prime
  factors are all `≥ 2`) with `∏ primeFactors ∣ r` and `le_log2_of_two_pow_le`.
- **`prod_one_sub_inv_ge_inv_card_succ`** — for a finite set `S` of naturals
  all `≥ 2`, `1/(|S|+1) ≤ ∏_{p∈S} (1 - 1/p)`, by strong induction on `S` via
  `Finset.induction_on_max` (each new largest prime `p` satisfies
  `p ≥ |S|+2`, giving the multiplicative step).
- **`totient_ratio_ge_inv_primeFactors_card_succ`** — `φ(r)/r ≥ 1/(|r.primeFactors|+1)`,
  by rewriting `φ(r)/r` as `∏_{p | r} (1 - 1/p)` (via
  `Nat.totient_eq_mul_prod_factors`) and applying the previous lemma.
- **`totient_ratio_ge_inv_log2_succ`** — for `0 < r < N`,
  `φ(r)/r ≥ 1/(log₂ N + 1)`, combining the previous two lemmas via
  `primeFactors_card_le_log2`.
  This is the lemma the small-`N` branch of `shor_totient_ratio_lower_bound`
  consumes: for `log₂ N + 1 ≤ 7` one checks `L + 1 ≤ 4 · log(L + 1)` numerically
  and the `Ω(1/log log N)` statement follows.

## `TotientBounds.lean`

The Mertens-type bound `φ(r)/r ≥ 1 / (4 · log(log₂ N + 1))`, for `r < 2 ^ 2048`.
Imports `OrderFindingAnalysis.lean` (for the `r < 255` case) plus Mathlib.

Everything rests on Euler's product `φ(r)/r = ∏_{p ∣ r} (1 − 1/p)` split at a
natural threshold `M`: divisors below `M` form a subset of the primes below `M`,
and each of the `k` divisors `≥ M` contributes at least `1 − 1/M`.  The number
`k` is pinned by `M^k ≤ r`, a `ℕ` computation, so no logarithm enters the split.

### Bounding `log` from below

- **`log_ge_of_two_pow_le`** — `k·log 2 + (1 − 2^k/x) ≤ log x` for `2^k ≤ x`:
  split off the largest power of two below `x` (`Real.log_div`, `Real.log_pow`)
  and apply `Real.one_sub_inv_le_log_of_pos` to the remainder.  This is the only
  analytic input in the file; with `Real.log_two_gt_d9` for `log 2` it makes
  every logarithm bound a `norm_num` goal.
- **`log_ge_aux`** (private) — the same with `log 2` already replaced by its
  rational lower bound, so callers only discharge arithmetic.

### The split

- **`totient_ratio_eq_prod`** — `φ(r)/r = ∏_{p ∣ r} (1 − 1/p)`, transported to
  `ℝ` from `Nat.totient_eq_mul_prod_factors`.
- **`pow_card_filter_le`** — `M^k ≤ r` where `k` is the number of prime divisors
  of `r` that are `≥ M` (`Finset.pow_card_le_prod`, `Nat.prod_primeFactors_dvd`).
- **`totient_ratio_ge_split`** — the split lemma: `φ(r)/r ≥ P(M) · (1 − k/M)`,
  with `P(M) = ∏_{p < M, p prime} (1 − 1/p)`.  The small part is
  `Finset.prod_sdiff` plus `Finset.prod_le_one`; the large part is
  `Finset.prod_const` plus Bernoulli (`one_add_mul_le_pow`).
- **`prod_primesBelow_eq_div`**, **`le_prod_primesBelow`** — `P(M)` as the ratio
  of the two naturals `∏ (p−1)` and `∏ p`, so a rational lower bound for it is
  two kernel `decide`s and one `norm_num`.

### Regions

- **`totient_ratio_region`** — `φ(r)/r ≥ c · (1 − K/M)` for `r < 2^b`, given
  `c ≤ P(M)` and any `K` with `2^b ≤ M^(K+1)`.
- **`region_bound`** (private) — the same with the target
  `1 / (4 log(log₂(r+1) + 1))` on the left, for `2^a ≤ r + 1`.
- **`region_A`**, **`region_B1`–`region_B8`** (private) — the nine cases.
  Region A (`r < 255`) is `totient_ratio_ge_inv_log2_succ` plus the numeric fact
  `L + 1 ≤ 4 log(L + 1)` for `L ≤ 7` (`log_succ_bound`).  The eight dyadic
  regions `[255, 2^16), …, [2^1024, 2^2048)` use thresholds
  `M = 17, 23, 31, 53, 89, 151, 269, 479` (6 to 91 primes); each clears its
  target by about 30%.
- **`totient_ratio_loglog_of_lt`** — the nine cases assembled: for `0 < r < 2^2048`,
  `1 / (4 · log(log₂(r+1) + 1)) ≤ φ(r)/r`.
- **`shor_totient_ratio_of_lt`** — the `N`-indexed form (`r + 1 ≤ N` and
  monotonicity of `Nat.log2` and `Real.log`) that
  `Proofs/NaiveShor/GoodOutcomeMassLowerBound.lean` consumes.

The complementary range `2^2048 ≤ r` is `TotientBoundsLarge.lean`.

## `TotientBoundsLarge.lean`

The same split lemma, with the threshold taken to be `M = ⌊log r⌋₊` and the
prime product below `M` evaluated by Mertens' third theorem.  Imports
`TotientBounds.lean` and `Vendor/Mertens/Theorems.lean`.

- **`gamma_lt`** — `γ < 0.609`, from
  `Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 16`
  (`γ < harmonic 16 - log 16`) and `Real.log_two_gt_d9`.
- **`neg_log_log_two_ge`** — `0.35 ≤ -log (log 2)`, i.e. `log 2 ≤ exp (-0.35)`,
  from `exp 0.35 = (exp 0.0875)⁴ ≤ (1 - 0.0875)⁻⁴` and `Real.log_two_lt_d9`.
  This is the `log L - log log 2` gain in the denominator, and the proof does
  not go through without it.
- **`prod_primesBelow_ge`** — `exp(-0.609 - (4.387/v + 1/1418)) ≤ P(M) · v`
  where `v = log (M-1)`: Mertens' `prod_prime_one_minus_inv_eq_nat` together
  with `E₃_bound`, `gamma_lt`, and `Nat.primesBelow M = Nat.primesLE (M-1)`.
- **`exp_neg_one_ge`**, **`exp_neg_c_ge`** — `0.2917 ≤ exp (-1.219012)`, via
  `exp(-c) = exp(-1) · (exp ((1-c)/2))²` and `1 + t ≤ exp t`; `Real.exp_one_lt_d9`
  supplies `exp(-1)`.  Splitting off `exp(-1)` is what keeps the linear bound
  usable at an argument above `1`.
- **`totient_ratio_loglog_of_ge`** — region C: `φ(r)/r ≥ (0.2917/v)(1 - 1.015/v)`
  against a target of `1/(4(v + 0.35))`, which reduces to a quadratic in `v`
  that holds for `v ≥ 5.14`; here `v ≥ 7.2`.  Margin at `2 ^ 2048`: about 5%.
- **`totient_ratio_loglog`** — the two regions combined, for every `0 < r`.
- **`shor_totient_ratio`** — the `N`-indexed form that
  `Proofs/NaiveShor/GoodOutcomeMassLowerBound.lean` consumes.
