# `Proofs/`

Everything below is proof-only; nothing outside `Proofs/`/`Main.lean` may
import it. This folder proves workspace readiness for the whole lowered
order-finding circuit, transfers the ideal circuit's success-probability
bound across the modular-exponentiation implementation error, and (via
`NaiveShor/`) proves the ideal circuit itself correct and reduces a good
order-finding outcome to a nontrivial factor.

```
Lowering, Budgets, Setup  <  Readiness/*  <  NaiveShor/*  <  Correctness
```

See `Readiness/README.md` for the workspace-readiness split (11 files, chained
by circuit stage) and `NaiveShor/README.md` for the ideal-circuit/classical-
reduction analysis.

## `Lowering.lean` — correctness of the whole-program lowerer

Correctness of the whole-program lowerer (`lowerGate_correctness`), the
`GateWorkspaceOK` projection lemmas, and the `lowerGate` simp equations.
Imports nothing from `Shor/`; consumed by `Readiness/*`, `Correctness.lean`,
and `GateCount/`.

## `Budgets.lean` — dynamic clean-state preservation

The dynamic clean-state preservation lemmas for the clean-state invariants
declared in `Spec/Cleanliness.lean`.

- **`freshZero_append`** *(private)* — freshness of an appended register
  follows from freshness of both halves, via `RegEncoding.toNat_append`.
- **`shorConcreteCleanState_ket`** — an initial `ShorWorkspaceCleanInput`
  basis state (plus fresh scratch-active qubits) satisfies
  `ShorConcreteCleanState`.
- **`ShorConcreteCleanState.to_lowering`** — `ShorConcreteCleanState` implies
  `ShorLoweringCleanState`, by peeling the exponent-scratch append back down
  to just the exponent reserve.
- **`fullShorWorkspaceCleanState_ket`** — an initial `ShorWorkspaceCleanInput`
  basis state satisfies `FullShorWorkspaceCleanState`.
- **`fullShorWorkspaceCleanState_to_carry`** — `FullShorWorkspaceCleanState`
  implies `ShorLoweringCleanState`, by dropping the data register's carry
  bit.
- **`shorLoweringCleanState_ket`** — the file's entry lemma: an initial
  `ShorWorkspaceCleanInput` basis state satisfies `ShorLoweringCleanState`
  directly (`fullShorWorkspaceCleanState_to_carry` ∘
  `fullShorWorkspaceCleanState_ket`). This is what every lowered Shor
  readiness theorem starts from.

## `Setup.lean` — bridge to the ideal order-finding input

- **`ShorApproxSetup.toIdealOrderFindingInput`** — forgets the
  approximate/implementation-only fields of a `ShorApproxSetup`, keeping only
  the exponent/data zero-state and disjointness facts the ideal
  specification (`IdealOrderFindingInput`) needs.

## `Correctness.lean` — the quantum-facing Shor statement

Keeps the ideal and approximate order-finding circuits, the measurement
interface, and the final success-probability theorem. Classical
order/continued-fraction material lives in `NaiveShor/`.

### Probability-transfer lemmas

The bridge from state-vector approximation to success-probability
approximation: pure real/probability bookkeeping, then gate isometry moving
distance bounds through common circuit context.

- **`lower_bound_of_abs_sub_le`** — `|A - B| ≤ ε → A ≥ B - ε`.
- **`transfer_lower_bound_from_abs_prob`** — if approximate/ideal success
  probabilities differ by at most `ε` and the ideal one is at least `L`, the
  approximate one is at least `L - ε`.
- **`dist_eval_common_suffix_le`** — applying a common suffix gate preserves
  a state-distance bound (via gate isometry / inner-product preservation).
- **`probability_of_success_eval_dist`** — converts a state-distance bound
  between two complete circuits into a lower bound on the approximate
  circuit's postprocessed success probability, via `probMeas_weighted_dist`
  from `Semantics/Measurement.lean`.

### Final correctness statements

The ideal theorem lives in `Proofs.NaiveShor.Correctness`; this section
imports that bound and transfers it across the modular-exponentiation
implementation error to obtain the approximate order-finding statement.

- **`initY1_eq_X_lowQubit`** — `initY1` is exactly `Gate.X` on the register's
  lowest qubit (for a nonempty register).
- **`ShorApproxSetup.prepared_state_valid`** — after Shor's Hadamards on
  `x.active` and initializing `y.active` to `1`, the state is a valid input
  for modular exponentiation; uses only the clean computational-basis input,
  the list-based modular-exponentiation layout, `H_reg`'s
  expansion/locality theorem, and the semantics of `Gate.X`.
- **`shor_data_capacity_from_log2`** — `N ≤ 2 ^ log₂(2N)`, the capacity fact
  needed to fit the modulus in the data register sized by `log₂(2N)`.
- **`ShorApproxSetup.toModExpConfig`** — builds a `ModExpConfig η` from a
  `ShorApproxSetup`, the coprimality/capacity side facts, and the per-qubit
  multiplier-coprimality fact for the arithmetic obligation.
- **`Shor_correct_approx_uniform_of_modExp_bound`** — given a uniform
  modular-exponentiation approximation bound (`hmodExp`), transfers the ideal
  order-finding success probability (from `Proofs.NaiveShor.Correctness`)
  across it via `probability_of_success_eval_dist` to bound the *approximate*
  circuit's success probability.
- **`Shor_correct_approx_uniform`** — instantiates the above with the actual
  uniform bound `modExpApprox_valid_dist_uniform`; the "uniform approximate
  Shor order-finding bound" — `K` is chosen once, independent of `η`.
- **`probability_of_success_lowerGate_eq`** — lowering preserves success
  probability exactly, given whole-program lowering workspace and dynamic
  cleanliness (via `lowerGate_correctness`).
- **`orderFindingApproxLow_probability_eq`** — specializes the above to
  `orderFindingApproxLow` vs. the high-level `orderFindingApprox` (not vs.
  `orderFindingIdeal` — whole-program lowering introduces no additional
  error on its own).
- **`Shor_correct_approx_lowered_of_modExp_bound`** — the file's headline
  theorem: combines `orderFindingApproxLow_probability_eq` (lowering is
  exact) with `Shor_correct_approx_uniform_of_modExp_bound` (the approximate
  circuit's bound) to get the final lowered success-probability guarantee
  from a `LoweredShorReady` package. Typed by
  `Spec.Assertions.ShorCorrectApproxLoweredUniform` and exposed as
  `Main.lean`'s `Shor_correct_approx_lowered_uniform`.
