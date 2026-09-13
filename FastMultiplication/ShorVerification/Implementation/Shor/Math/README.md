# `Math/`

Pure math, no framework/register dependencies: number-theory, Fourier/
geometric-sum, and counting lemmas backing the ideal order-finding
good-outcome analysis. Import closure is Mathlib plus the project's
semantics-free vocabulary (`ord`, `qftPhase`, `GoodOutcome`) — no
`QSemantics`, `eval`, or measurement. The one file, `OrderFindingAnalysis.lean`,
carries no internal section banners; it was moved byte-for-byte from the old
`Proofs/NaiveShor/Lemmas.lean`, so the grouping below follows its actual
top-to-bottom logical flow rather than author-labeled sections.

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
`log₂ N`, then into the concrete `exp(-2)` constant used for `κ`.

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
- **`exp_neg_two_div_pow4_le_inv_succ`** — for `L ≥ 1`,
  `exp(-2)/L⁴ ≤ 1/(L+1)`: the final numeric estimate (case-split on `L = 1`
  vs. `L ≥ 2`, the latter via `L+1 ≤ L² ≤ L⁴`) that converts the `1/(log₂N+1)`
  bound above into the `κ`-shaped constant `exp(-2)/(log₂N)⁴` used in
  `Spec/Assertions.lean`'s final success-probability guarantees.
