# `NaiveShor/`

The ideal-circuit (`orderFindingIdeal`, using exact modular exponentiation)
analysis: preparing the periodic pre-IQFT state, the Fourier/measurement
formula for the post-IQFT outcome probability, the good-outcome mass lower
bound, and the final ideal-circuit success theorem `Shor_correct` (typed by
`Spec/Assertions.lean`'s `ShorCorrect`). Internal order:

```
Preliminaries  <  PhaseEstimation  <  GoodOutcomeMassLowerBound  <  Correctness
```

(each file imports exactly the ones before it — confirmed from their own
`import` lines).

## `Preliminaries.lean`

Small arithmetic/probability facts shared by the rest of the folder.

### `ord`/`BasicSetting` facts

- **`basicSetting_of_shor_instance`** — a `ShorOrderFindingInstance` together
  with register widths `m = log₂(2N²)`, `n = log₂(2N)` satisfies
  `BasicSetting a (ord a N) N m n`, the standard parameter package the
  continued-fraction/Fourier analysis is stated over.
- **`goodOutcome_r_found_one`** — if an outcome `o` is `GoodOutcome` for
  `Q`/`r = ord a N`, then the classical continued-fraction post-processing
  `r_found` (using the verifier `d ↦ a^d mod N = 1`) recovers exactly `1`,
  i.e. the classical step succeeds on every good quantum outcome.

### Register/basis bookkeeping

- **`toNat_qubitReg`** *(private)* — a single-qubit register's `toNat` value
  is `1` iff its one bit is set, `0` otherwise.
- **`toNat_cons_reg`** *(private)* — `toNat` of a register built by
  `cons`-ing one qubit onto a list decomposes as bit-of-head plus
  `2 *` toNat-of-tail.
- **`eval_modExpIdealSteps_ket`** *(private theorem)* — the recursive ideal
  modular-exponentiation step-list (over a list of control qubits) multiplies
  the data register in place by `a^(2^e · toNat ctrls)` mod `N`, proved by
  induction on the control list using `toNat_cons_reg` and the ideal
  controlled-modmul gate's exact ket semantics.

### Small probability lemmas

- **`measProbAfter_nonneg`** — every post-measurement probability
  (`MeasureClass.probMeas`) is nonnegative.
- **`r_found_nonneg`** — the classical success indicator `r_found` is always
  nonnegative (it's an indicator, `0` or `1`).
- **`goodOutcome_mass_le_probability_of_success`** — the total probability
  mass on good outcomes is a lower bound for the true `probability_of_success`
  (every good outcome contributes its full probability via
  `goodOutcome_r_found_one`, every non-good outcome contributes a
  nonnegative amount).

### Shared order-finding parameter bound

- **`shor_order_parameter_bounds`** — from `BasicSetting a r N m n`, derives
  `0 < r`, `r < N`, and `r² < 2^m` (the continued-fraction precision
  requirement), via `ZMod N`ˣ order-of-unit facts (`orderOf_le_card_univ`,
  `ZMod.card_units_eq_totient`, `Nat.totient_lt`).

## `PhaseEstimation.lean`

The QPE chain for ideal order finding: the pre-IQFT state, the exact
inverse-QFT evaluation, grouping outputs by residue class, the measurement
projector on the grouped post-IQFT state, and the paper output-probability
formula.

- **`idealPreIQFTState`** — the ideal state immediately before the inverse
  QFT, `1/√Q ∑ₜ |t⟩|aᵗ mod N⟩`, defined independently of `H_reg`/`initY1`/
  `modExpIdeal'`'s implementations so later Fourier lemmas don't depend on
  them.
- **`shorOutputBasis`** *(private)* — the basis state with exponent register
  set to `o` and data register set to `aˢ mod N`.
- **`shorGroupedPostIQFTState`** *(private)* — the post-IQFT state written as
  a double sum over outcome `o` and residue class `s < r`, weighted by
  `shorPeriodClassAmplitude`.
- **`active_disjoint_of_ownedDisjoint`**, **`eval_finset_sum_local`**,
  **`eval_fintype_sum_local`**, **`shor_inv_sqrt_sq`** *(all private)* —
  small bookkeeping: register-ownership disjointness gives active-qubit
  disjointness; gate evaluation distributes over finite/`Fintype` sums; the
  normalization constant squares to `1/Q`.
- **`shor_pow_mod_periodic`** *(private)* — `aᵗ mod N` depends only on
  `t mod r` (period `r = ord a N`), via the unit group `(ZMod N)ˣ`.
- **`shor_pow_mod_injective_below_order`** *(private)* — below one full
  period, distinct exponents give distinct residues, via
  `pow_injOn_Iio_orderOf`.
- **`eval_IQFT_ket_exact`** *(private)* — exact inverse-QFT action on a basis
  state (Fourier inversion via the conjugated `qftPhase`), restated from
  `QFTSemantics.eval_adj_QFT_ket`.
- **`shor_preIQFT_x_value`**, **`shor_IQFT_output_basis_eq`**,
  **`shor_group_fixed_output`** *(all private)* — algebraic steps
  identifying the exponent-register value in the pre-IQFT sum, rewriting an
  IQFT output basis state via `shor_pow_mod_periodic`, and regrouping the
  `t`-sum by residue class `s = t mod r` (via `sum_range_group_by_mod`) into
  the `shorPeriodClassAmplitude`-weighted form.
- **`eval_IQFT_idealPreIQFTState_grouped`** *(private)* — assembles the above
  into the file's central identity: applying `IQFT x` to `idealPreIQFTState`
  equals `shorGroupedPostIQFTState`, by linearity, Fourier inversion, the
  periodicity rewrite, and swapping/regrouping the double sum.
- **`shorOutputBasis_x_value`** *(private, `@[simp]`)* — the exponent
  register of `shorOutputBasis a N x y b0 o s` reads back as `o`.
- **`measProj_shorGroupedPostIQFTState`** *(private)* — measuring the
  exponent register at outcome `o` on the grouped state kills every term
  except the `o`-labelled residue-class sum (`Finset.sum_eq_single`).
- **`shorOutputBasis_ne_of_residue_ne`** *(private)* — for fixed `o`, distinct
  residues `s ≠ t` (both `< r`) give distinct output basis states, via
  `shor_pow_mod_injective_below_order` reading back the data register.
- **`norm_sq_sum_eq_sum_norm_sq_of_orthogonal_shor`** *(private)* — Pythagoras
  for a finite sum of pairwise-orthogonal vectors (by induction on the
  finset, expanding `‖f a + ∑ S‖²` via `norm_add_sq`).
- **`norm_sq_shor_period_class_sum`** *(private)* — the squared norm of the
  residue-class superposition equals `shorPaperOutcomeProb Q r o`, combining
  the orthogonality above (distinct data-register labels) with the ket-norm
  identity.
- **`measProbAfter_orderFindingIdeal_eq_paper_formula`** — the file's
  headline theorem, "Equations (5.4)–(5.7)": starting from the explicit
  periodic pre-IQFT state, measuring the exponent register after the final
  IQFT gives exactly `shorPaperOutcomeProb Q r o`. Chains
  `eval_IQFT_idealPreIQFTState_grouped` (Fourier regrouping),
  `measProj_shorGroupedPostIQFTState` (projection), and
  `norm_sq_shor_period_class_sum` (norm), then applies the Born rule
  (`MeasureClass.probMeas_born`).

## `GoodOutcomeMassLowerBound.lean`

Follows the structure of Shor's original paper, Section 5: (5.2) the
periodic modular-exponentiation state, (5.4–5.7) the Fourier/output
probability formula (from `PhaseEstimation.lean`), (5.11–13) the lower bound
near multiples of `Q/r`, (5.24–25) counting coprime numerators — assembled
here into the final good-outcome probability-mass lower bound.

### Totient ratio bound

- **`shor_totient_ratio_log4_lower_bound`** — a deliberately weak bound,
  `exp(-2)/log₂(N)⁴ ≤ φ(r)/r` for order `r < N`; weaker than Shor's classical
  asymptotic bound but convenient because it directly gives the public
  theorem's inverse-polylogarithmic form. Combines
  `exp_neg_two_div_pow4_le_inv_succ` (analytic step) and
  `totient_ratio_ge_inv_log2_succ` (from `Math/OrderFindingAnalysis.lean`).

### Exact preparation of the ideal Shor state

- **`basicSetting_data_facts`** *(private)* — `BasicSetting` implies
  `1 < N`, `0 < n`, and `N ≤ 2ⁿ` — the numerical facts needed to initialize
  and use the data register.
- **`initY1_eq_X_lowQubit_naive`** *(private)* — `initY1` is `Gate.X` on the
  register's lowest qubit (duplicate of `Correctness.lean`'s
  `initY1_eq_X_lowQubit`, kept local to avoid an extra import for one small
  fact).
- **`eval_initY1_after_exponent_write`** *(private)* — writing an exponent
  value into a register disjoint from `y` leaves `y = 0`, so `initY1`
  afterward sets `y` to `1`.
- **`qftPhase_zero_left`** *(private)* — `qftPhase N 0 y = 1`.
- **`eval_Hreg_zero_uniform_sum`** — starting from a zero register, `H_reg`
  produces the uniform superposition over all basis values (via
  `GateSemanticsFacts.eval_Hreg_zero_eq_QFT` and `QFTSemantics.eval_QFT_ket`).
- **`eval_initY1_after_Hreg_zero`** *(private)* — from `x = y = 0`, applying
  `H_reg` then `initY1` produces `1/√Q ∑ₜ |t⟩|1⟩`, Shor's state immediately
  before modular exponentiation.
- **`ctrlExp`** *(private def)* — the exponent accumulated by processing a
  list of control qubits with the head at bit-weight `2^e`, matching
  `modExpIdealSteps`'s recursion.
- **`ctrlExp_eq_sum`**, **`ctrlExp_zero_qubits_eq_toNat`**,
  **`ctrlExp_writeNat_out`** *(all private)* — `ctrlExp` equals the
  corresponding weighted bit sum; processing all of a register's qubits from
  `e = 0` accumulates exactly `toNat`; control bits disjoint from a written
  register are unaffected by the write.
- **`eval_modExpIdealSteps_ket`** *(private)* — generalizes
  `Preliminaries.lean`'s lemma of the same name to arbitrary starting
  exponent `e`: the ideal modexp step-list multiplies `y` in place by
  `a ^ (ctrlExp of the processed controls)` mod `N`.
- **`eval_modExpIdeal_ket`** — specializes the above to the full control list
  `x.qubits` from `e = 0`: `modExpIdeal'` maps `|t⟩|v⟩ ↦ |t⟩|v · aᵗ mod N⟩`, via
  `ctrlExp_zero_qubits_eq_toNat`.
- **`eval_modExpIdeal_on_initialized_label`** *(private)* — exact modular
  exponentiation on one initialized basis label: `|t⟩|1⟩ ↦ |t⟩|aᵗ mod N⟩`.
- **`eval_modExpIdeal_on_initialized_superposition`** *(private)* — by
  linearity, lifts the label-level fact to the full uniform superposition:
  `1/√Q ∑ₜ|t⟩|1⟩ ↦ 1/√Q ∑ₜ|t⟩|aᵗ mod N⟩`.
- **`eval_orderFindingIdeal_prefix`** — Shor's equation (5.2): Hadamards
  followed by exact modular exponentiation create the uniform periodic state
  `idealPreIQFTState`, combining `eval_initY1_after_Hreg_zero` and
  `eval_modExpIdeal_on_initialized_superposition`.

### Final quantum good-outcome mass theorem

- **`ideal_orderFinding_goodOutcome_mass_lower_bound`** — the file's headline
  theorem: `κ / log₂(N)⁴ ≤` the total probability mass on good outcomes for
  the ideal circuit. Seven-step proof: (1) `0 < r`, `r < N`, `r² < Q`; (2)
  prepare the periodic state (5.2, `eval_orderFindingIdeal_prefix`); (3) the
  Fourier/measurement formula (5.4–5.7, `PhaseEstimation.lean`'s
  `measProbAfter_orderFindingIdeal_eq_paper_formula`); (4) every good Fourier
  peak has probability `≥ 4/(π² r)` (`shor_paper_goodOutcome_lower_bound`
  from `Math/OrderFindingAnalysis.lean`); (5) at least `φ(r)` distinct good
  outputs (`goodOutcome_card_ge_totient`); (6) sum the per-outcome bounds
  (`goodOutcome_mass_lower_bound_from_card_and_pointwise`); (7) replace
  `φ(r)/r` by the inverse-polylogarithmic bound
  (`shor_totient_ratio_log4_lower_bound`) to land on `κ/log₂(N)⁴`.

## `Correctness.lean`

The folder's public theorem.

- **`Shor_correct`** — ideal order-finding success probability for Shor's
  algorithm: `ShorCorrect T hT inst x y b0 hm hn hinput` (i.e.
  `probability_of_success ≥ κ/log₂(N)⁴`). Two-step proof: the good-outcome
  mass lower bound (`ideal_orderFinding_goodOutcome_mass_lower_bound`) is
  itself a lower bound for the full success probability
  (`goodOutcome_mass_le_probability_of_success`, from `Preliminaries.lean`).
  Typed directly by `Spec/Assertions.lean`'s `ShorCorrect` Prop; consumed by
  `Proofs/Correctness.lean`'s `Shor_correct_approx_uniform` (via the uniform
  modular-exponentiation transfer) and exposed as one of `Main.lean`'s public
  theorems.
