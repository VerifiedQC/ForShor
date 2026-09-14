# `Proofs/`

Everything below is proof-only; nothing outside `Proofs/`/`Main.lean` may
import it. This folder proves that the concrete `Circuit/` gates approximate
the ideal controlled modular multiplication/exponentiation gates, culminating
in `ModExp.lean`'s `modExpApprox_valid_dist_uniform`.

Two foundation files, then the Step-4 comparator and Step-3 lowering
correctness proofs, then the five-step Algorithm-1 error analysis in
pipeline order:

```
Model, Core  <  CmpLtNW, ConstArithmetic  <  Algorithm1Expansion  <  Step1QPE
  <  Step1Bound, Step2Bound, Step34Exact  <  FinalModMul  <  ModExp
```

## `Model.lean` — the analysis vocabulary

Pure definitions — no proofs of nontrivial facts. Every other file in this
folder states its theorems in terms of these names.

- **`Step5ConstantOK`** — states that the concrete `step5Constant`
  (`Circuit/Steps.lean`) is a valid encoding of `1 - c⁻¹ mod N`.
- **`ModMulConfig.U1`/`.U2`/`.U34`/`.U5`** — name Steps 1, 2, the combined
  3+4 comparator block, and 5 as gates over a `ModMulConfig`;
  **`stagedGate`** is `U1 ;; U2 ;; U34 ;; U5`, the staged form of the
  five-step core the whole error decomposition reasons about instead of the
  raw `CmodMulInPlaceCore` circuit.
- **`alg1TargetResidue`**, **`alg1TargetFraction`**, **`alg1WorkFraction`** —
  the intended residue Step 1's phase load targets, and its real-fraction
  form; the real-fraction form of a work-register label.
- **`alg1GoodLabels`** — the QPE labels within `η/N` of the target fraction.
  Retained (good) vs. discarded (bad) labels is the central dichotomy of the
  whole proof.
- **`alg1Step2Value`** — the exact data-carry value Step 2 should produce
  for a retained label.
- **`Alg1Step2SourceIndex`**, **`Alg1Step2FourierIndex`**,
  **`alg1Step2FourierIndices`**, **`alg1Step2FourierLabel`**,
  **`alg1Step2FourierBaseCoeff`**, **`alg1Step2FourierMultiplier`**,
  **`alg1Step2ActualFourierCoeff`**, **`alg1Step2IdealFourierCoeff`**,
  **`alg1Step2ShiftDiscrepancy`**, **`alg1Step2Error`** — index and label
  machinery for expanding Step-2 states into per-Fourier-label packets, the
  actual vs. ideal post-QFT Fourier coefficients, their real shift
  discrepancy, and the one-label Step-2 error vector.
- **`alg1OutputValue`**, **`alg1Step4CrossCondition`**, **`alg1Overflow`** —
  the final data value Steps 3-4 should produce exactly; the comparator
  condition Step 4 checks; whether the pre-reduction Step-2 value overflowed
  `N`.
- **`Alg1Trace`** — a structure packaging a finite input superposition's
  basis support, coefficients, phase coefficients after Step 1, and the
  hypothesis that Step 3/4's cross-condition matches the overflow flag on
  every retained label. The central bookkeeping object threaded through the
  whole error decomposition.
- **`Alg1Trace.goodStep1`/`.afterStep2Ref`/`.afterStep34Ref`** — the
  retained-good-label reference packets after Steps 1, 2, and 3+4
  respectively, each replacing the approximate circuit output with the exact
  intended value.
- **`alg1PhaseCoeff`**, **`alg1QpeBadMass`**, **`alg1TraceBadMass`** — the
  actual Step-1 amplitude of one work-label basis vector; the discarded QPE
  probability mass for one input, and for a whole trace.
- **`Alg1Trace.badStep1`/`.afterStep34Full`/`.afterStep34Bad`** — the
  discarded-label packet after Step 1; the (all-labels-retained) formal
  post-Step-3/4 reference packet and its discarded part, used to identify
  the Step-5 cleanup with the same QPE tail.
- **`alg1Step1Phase`**, **`alg1Step5Phase`**, **`alg1Step5Forward`**,
  **`alg1Step1PhaseScalar`**, **`alg1TargetPhaseScalar`**,
  **`alg1LoadPreCoeff`**, **`alg1IQFTCoeff`**, **`alg1FractionalLoadCoeff`**
  — the explicit diagonal-phase/Hadamard/inverse-QFT coefficient chain
  computing the Step-1 fractional-load amplitude in closed form (and the
  un-adjointed Step-5 circuit whose phase turns out to match it).

## `Core.lean` — basic facts about the model

Everything `Model.lean` defines, this file proves basic facts about — small
arithmetic lemmas and a few substantial semantic theorems, but not yet the
per-step error bounds (those live in `Step1Bound.lean`/`Step2Bound.lean`/
`Step34Exact.lean`/`FinalModMul.lean`).

- **`IdealCtrlModMulExactSemantics.eval_idealCtrlModMul_good_ket_exact`** /
  **`.eval_idealCtrlModMul_good_ket`** — the ideal controlled-modmul gate is
  exact (returns `c·x mod N`) on any basis ket with a good input, restated
  from and then in terms of the semantics typeclass.
- **`idealCtrlModMul_preserves_valid`** — the ideal gate maps the
  valid-input subspace into itself, needed since the hybrid argument reasons
  inductively over repeated applications.
- **`step5Constant_ok`** — the concrete `step5Constant` satisfies
  `Step5ConstantOK` whenever `c` is coprime to `N`; bridges `Model.lean`'s
  spec to `Circuit/Steps.lean`'s concrete construction.
- **`eval_step3_clean_ket`** / **`eval_step4_cancels_ket`** — exact
  basis-ket semantics of Step 3 (comparator + subtract) and Step 4 (flag
  cleanup) on a clean workspace; **`eval_step3_local_ket`** /
  **`eval_step4_local_ket`** are the versions `Shor/Proofs/Readiness.lean`
  imports this file directly for.
- **`alg1TargetResidue_lt_N`**, **`alg1Step2Value_lt_dataCarry_capacity`**,
  **`alg1OutputValue_lt_data_capacity`** — the three named `Model.lean`
  quantities all fit in their registers' capacity, needed throughout to
  justify `RegEncoding.writeNat` calls.
- **`modExp_multiplier_coprime`** — each per-qubit exponentiation multiplier
  `a^(2^i) mod N` stays coprime to `N`, feeding `ModExpArithmeticOK`.

## `CmpLtNW.lean` — Step-4 comparator correctness

Exact correctness of the concrete `Circuit/CmpLtNW.lean` circuit: it computes
`N·work` into clean scratch via a QFT/phase-product/inverse-QFT sandwich,
forms the signed difference `2^|work|·data - N·work`, copies its sign bit to
`flag`, then uncomputes both temporary stages — exact on basis states, with
every scratch/reserve qubit restored.

- **`eval_cmp_lt_nw_ket`** — the one public headline theorem: on a basis ket
  with clean `data`/`work`/`scratch`, `cmpLtNW` toggles `flag` iff
  `data · |work| < N · work` (the exact unsigned comparison Step 4 needs),
  restoring everything else. Consumed by `Core.lean`'s
  `eval_step4_cancels_ket`/`eval_step4_local_ket` rather than reasoned about
  directly downstream.

## `ConstArithmetic.lean` — Step-3 constant-arithmetic lowering correctness

Correctness of `Lowering/ConstArithmetic.lean`'s concrete `LowGate`
realizations of Step 3's typed comparator/subtractor.

- **`evalL_lowerCmpGeConst_ket`** — basis-ket correctness of the lowered
  `CmpGeConst`.
- **`evalL_lowerCmpGeConst_preserves_clean`** — comparison changes only its
  flag and restores `data`/`scratch`, so the same clean predicate survives
  into the following controlled subtraction.
- **`evalL_lowerCSubConst_ket`** — basis-ket correctness of the lowered
  `CSubConst`.
- **`evalL_lowerCmpGeConst`** / **`evalL_lowerCSubConst`** — the two
  headline results: linear extension (by induction on `CleanClosure`) of the
  ket-level facts above to every state in the clean-workspace span, i.e.
  `lowerCmpGeConst`/`lowerCSubConst` evaluate exactly like the typed
  source-language gates `Gate.CmpGeConst`/`Gate.CSubConst` on the full clean
  subspace. Consumed by `Shor/Proofs/WholeProgramCorrectness.lean` and
  `Shor/Proofs/Readiness.lean` rather than by other files in this folder.

## Algorithm 1 proof outline

The remaining six files carry out the error analysis for Algorithm 1's five
circuit steps and assemble the folder's two headline theorems. Algorithm 1
approximately implements `|x⟩|0⟩ ↦ |c·x mod N⟩|0⟩`; retained ("good") QPE
work labels are within `η/N` of the target fraction and drive the circuit to
(nearly) the right answer, while discarded ("bad") labels are bounded in
total mass rather than tracked individually.

### `Algorithm1Expansion.lean` — Step 1: expand the staged gates on basis states

Expands `ModMulConfig.stagedGate` on valid basis states and builds the
finite `Alg1Trace` the later quantitative bounds are stated over.

- **`ModMulConfig.eval_approxGate_eq_staged`** — the public approximate gate
  is definitionally `U1 ;; U2 ;; U34 ;; U5`.
- **`eval_finset_sum`**, **`eval_iqft_work_expansion`**,
  **`eval_cphaseprodusing_work_diagonal`**, **`eval_Hreg_work_expansion`** —
  linear-expansion helpers: gate evaluation distributes over finite sums; the
  inverse QFT on a work register expands as a finite basis sum; on a clean
  workspace the controlled phase product is diagonal in the work label;
  register Hadamards applied to a work-written basis state expand over work
  labels only.
- **`alg1_step1_ket_expansion`** / **`alg1_step1_ket_qpe_expansion`** — Step
  1 maps a good basis input to a coherent work-label packet, whose
  coefficients are exactly `alg1PhaseCoeff`.
- **`alg1_step1_zero_target_exact`** — if the Step-1 target residue is zero,
  the inverse QFT exactly returns the input basis state (rules out nonzero
  good labels in the zero-target case).
- **`alg1_output_mod`** — rewrites the final controlled-multiplication
  residue through the Step-1 target residue.
- **`alg1_step4_cross_iff_overflow_of_good`** — for good labels, the Step-4
  comparator condition is exactly Step-2 overflow.
- **`alg1_trace_of_valid`** — the file's apex: assembles the valid-state
  expansion, Step-1 coefficient identification, zero-target support fact,
  and Step-3/4 overflow arithmetic into the `Alg1Trace` record consumed by
  the rest of this folder.

### `Step1QPE.lean` — Step 1: the QPE tail estimate for the fractional load

Views the fractional work-register load in Step 1 as a QPE kernel and bounds
its tail uniformly over valid basis inputs, in three stages: trace
bookkeeping, packet algebra, then analysis.

- **`writeNat_overwrite_same_reg`** and other shared register-level lemmas
  — reindexing invariance and register restoration used by the rest of the
  file.
- **`alg1_trace_phaseCoeff_eq_alg1PhaseCoeff`** — an `Alg1Trace`'s abstract
  coefficients are the canonical ones.
- **`alg1_trace_bad_mass_le_of_basis_tail`** — lifts a per-basis-input tail
  bound to a whole trace.
- **`alg1_step1_error_sq_eq_trace_bad_mass`** — turns the operator-level
  Step-1 error into the purely numerical `alg1TraceBadMass`.
- **`alg1_step5_cleanup_residue_eq_target`** — the Step-5 constant's
  composite residue equals `alg1TargetResidue`: Step 5 is the inverse of the
  Step-1 load mod `N`.
- **`alg1_step1_phase_scalar_eq_target`**, **`alg1_step5_phase_scalar_eq_target`**,
  **`alg1_step5_phase_scalar_eq_step1`** — both Step-1 and Step-5 phase
  scalars collapse to the common `alg1TargetPhaseScalar`.
- **`alg1_step1_cphase_on_work_label`**, **`alg1_step5_cphase_on_output_work_label`**
  — evaluate the Step-1/forward-Step-5 phase gates on one work label.
- **`alg1_step1_preIQFT_packet`**, **`alg1_step5_forward_preIQFT_packet`** —
  run Step 1 forward exactly (Hadamards → uniform superposition, controlled
  phase product → diagonal scalar, inverse QFT → explicit mixing),
  identifying `alg1PhaseCoeff` with the closed-form `alg1FractionalLoadCoeff`.
- **`alg1_bad_label_set_eq_qpe_bad_set`**, **`alg1_precision_grid_ratio`** —
  convert `Algorithm1Precision` into the grid-to-capacity ratio the numeric
  bound in `Math/QPETail.lean` consumes; the definition of `qpeKernel` itself
  lives in this file's `AnalyticQpeSetup` section, straddling the boundary
  with `Math/QPETail.lean` (everything downstream of it — the numerical
  majorant argument — was extracted there in an earlier reorg step).
- **`alg1_qpe_tail_basis_uniform`** — the file's other named endpoint:
  bounds the QPE bad mass by `512 * η` uniformly over good basis inputs, via
  `Math/QPETail.lean`'s `qpeKernel_bad_mass_le_grid_ratio`.

### `Step1Bound.lean` — Steps 1 and 5: lift the basis bound to arbitrary states

Lifts `Step1QPE.lean`'s basis-state QPE estimate to arbitrary valid unit
states, and covers the matching Step-5 cleanup estimate (which is why Step 5
does not get a separate file: its error is controlled by the same
fractional-load/QPE estimate, viewed on the opposite side of the exact
modular-multiplication map).

- **`alg1_step5_forward_packet_on_extended_output`**,
  **`alg1_step5_forward_packet_on_basis`**,
  **`alg1_step5_full_packet_on_basis`**, **`alg1_step5_full_packet_eq_ideal`**
  — build the exact Step-5 cleanup identity from the basis-level forward
  packet up to arbitrary traces (by linearity).
- **`alg1_afterStep34Full_eq_good_add_bad`** — the post-Step-3/4 packet
  splits into good-label + bad-label sums.
- **`alg1_step34_label_injective`**, **`alg1_work_label_injective`** — the
  basis label after Steps 3/4 (resp. after just the work write) uniquely
  determines the original input and QPE label, so packet terms can't
  collide.
- **`alg1_afterStep34Bad_norm_sq_eq_trace_bad_mass`** — Steps 3/4 preserve
  the squared norm of the bad packet.
- **`alg1_step5_cleanup_error_eq_neg_bad_packet`**,
  **`alg1_step5_cleanup_sq_eq_trace_bad_mass`** — the Step-5 cleanup error is
  exactly (minus) the bad packet, hence its squared norm is the trace bad
  mass.
- **`alg1_goodStep1_norm_le_one`** — the retained-good Step-1 packet has
  norm ≤ 1.
- **`alg1_qpe_tail_uniform`** — the file's headline theorem: one
  nonnegative constant (`≤ 512`) simultaneously bounds the basis-level bad
  QPE mass, the squared Step-1 truncation error, and the squared Step-5
  cleanup error, for every valid unit state. Consumed directly by
  `FinalModMul.lean`.

### `Step2Bound.lean` — Step 2: the quantitative Fourier stability bound

Adds `N·w` to the data register; for retained work labels, `N·w` is close
enough to `(c-1)·x mod N` that the result is close to `c·x mod N` (or
`c·x mod N + N`). Analyzes one retained label first, then controls coherent
superpositions by decomposing into orthogonal work-label fibers.

- **`alg1_step2_source_label_injective_on_good`** — the written work-register
  label uniquely identifies the original basis input and work value within
  the retained good packet.
- **`alg1_step2_trace_error_eq_good_branch_sum`** — expands the Step-2 trace
  error as the coherent sum of individual branch errors over retained
  labels.
- **`alg1_step2_good_coeff_energy_eq_norm_sq`** /
  **`alg1_step2_good_coeff_energy_le_one`** — the retained packet's squared
  coefficient energy equals `‖goodStep1‖²`, which is ≤ 1 for a valid unit
  input.
- **`alg1_step2_good_label_shift_discrepancy_lt`** — a retained work label
  approximates its target residue with discrepancy strictly less than `η`.
- **`alg1_step2_actual_preIQFT_packet`** / **`alg1_step2_ideal_preIQFT_packet`**
  — explicit Fourier-basis expansions of the actual vs. ideal packets just
  before the inverse QFT.
- **`alg1_step2_branch_norm_eq_preIQFT_norm`** — unitarity of the inverse
  QFT reduces a branch error's norm to the pre-IQFT packet difference.
- **`alg1_step2_fourier_coeff_error_bound`**,
  **`alg1_step2_normalized_fourier_packet_bound`** — each actual Fourier
  coefficient differs from the ideal by at most the normalized phase error
  from the shift discrepancy; the normalized orthogonal Fourier packet has
  norm at most `2πη`.
- **`alg1_good_labels_same_work_residue`** — the same work label being good
  for two inputs forces the same target residue (makes the phase multiplier
  constant within a work fiber).
- **`alg1_step2_fixed_work_error_eq_iqft_multiplier_packet`**,
  **`alg1_step2_fixed_work_fourier_contraction`**,
  **`alg1_step2_fixed_work_packet_sq_bound`** — represent/bound the
  fixed-work-fiber coherent error via the inverse QFT of a
  bounded-phase-multiplier packet, contracting to a linear-in-`η` energy
  bound.
- **`alg1_step2_work_fiber_orthogonal`**, **`alg1_step2_energy_eq_sum_work_fibers`**
  — distinct work-label fibers are orthogonal; total coefficient energy is
  the sum of fiber energies.
- **`alg1_step2_good_packet_operator_sq_bound`** — a uniform constant
  controls the squared Step-2 error of every good coherent packet by `η`
  times its coefficient energy.
- **`alg1_step2_good_label_branch_uniform`** — the file's headline theorem
  (its own docstring calls it "the main theorem of the file"): one
  nonnegative constant simultaneously bounds the error of every retained
  basis/work branch and the squared Step-2 error of every valid unit-state
  trace. Consumed by `FinalModMul.lean`.

### `Step34Exact.lean` — Steps 3 and 4: exactness, not approximation

Step 3 checks whether the grown data register is at least `N` and subtracts
it if needed; Step 4 uncomputes the comparison flag. Neither is an
approximation step in this proof.

- **`alg1_step3_reduces_to_modmul`** — conditional subtraction of `N` from
  the Step-2 value produces exactly the controlled modular-multiplication
  output, using that the unreduced sum is below `2N` so at most one
  subtraction is needed.
- **`alg1_step34_reference_exact_core`** — Steps 3 and 4 are exact on the
  Step-2 reference state, combining the arithmetic reduction above with
  register-locality/disjointness helpers.
- **`alg1_step34_reference_exact`** — the headline/public theorem: Steps 3
  and 4 map the complete Step-2 reference state exactly to the post-Step-3/4
  reference state. Directly consumed by `FinalModMul.lean`; since it carries
  no error term, it contributes only an algebraic identity to that file's
  triangle-inequality chain, not one of the three approximation budgets.

### `FinalModMul.lean` — final assembly for one modular multiplication

Combines the Step 1, Step 2, and Step 5 approximation budgets (Steps 3/4
contribute no error) into the final single-call bound.

- **`three_stepErr_le`** — combines three square-root error budgets into one
  `stepErr` budget via `(√a + √b + √c)² ≤ 3(a+b+c)`.
- **`norm_chain_three`** — the generic three-link triangle inequality
  `‖x₀-x₃‖ ≤ ‖x₀-x₁‖+‖x₁-x₂‖+‖x₂-x₃‖`.
- **`modMul_approx_valid_dist_uniform`** — the headline theorem: a
  nonnegative constant `K ≤ 2048`, independent of `η`, the configuration, or
  the input state, such that every valid unit input is within
  `stepErr K η` of ideal modular multiplication. Combines
  `alg1_qpe_tail_uniform` (Steps 1 & 5), `alg1_step2_good_label_branch_uniform`
  (Step 2), and `alg1_step34_reference_exact` (the exact link) via
  `norm_chain_three` and `three_stepErr_le`.

### `ModExp.lean` — lift to full modular exponentiation

Lifts the uniform modular-multiplication estimate through the recursive
sequence of controlled multiplications used by modular exponentiation; each
step contributes one `stepErr K η` term, so total error is proportional to
the number of exponent-control bits.

- **`ModExpTailLayout`** / **`ModExpTailArithmeticOK`** — the layout/coprimality
  side conditions required by every remaining controlled-multiplication step
  in a tail of exponent-control qubits; **`modExpTailLayout_tail`** /
  **`modExpTailArithmeticOK_tail`** show removing the head control preserves
  them.
- **`ideal_preserves_valid`** — the ideal controlled multiplication preserves
  the valid modular-input subspace (via the private ket-level
  `ideal_preserves_algorithm1_good_ket`), the invariant threaded through the
  recursive hybrid argument below.
- **`modExpApproxSteps_valid_dist_uniform`** — uniform hybrid bound for a
  control-qubit tail: the approximate step-list differs from the ideal by
  at most `ctrls.length * stepErr K η`, by induction over `ctrls` applying
  `modMul_approx_valid_dist_uniform` at the head and `ideal_preserves_valid`
  to carry validity into the induction hypothesis.
- **`modExpApprox_valid_dist_uniform`** — the folder's headline theorem: the
  full modular-exponentiation bound, instantiating the tail theorem at all
  qubits of the exponent register, with final factor `tbits cfg.x`.
  `Main.lean` imports this file directly and packages the theorem into
  `Spec.Assertions.ModExpApproxValidDistUniform`.
