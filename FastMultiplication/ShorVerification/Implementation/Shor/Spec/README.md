# `Spec/`

The public specification surface: clean-input/clean-state predicates, the
user-facing setup records, and the final correctness Props. Internal order:
`Cleanliness → Setup → Assertions` (each may import the ones before it).

## `Cleanliness.lean` — clean-input predicates and clean-state invariants

- **`ShorWorkspaceCleanInput`** — every reserve register that may be used
  during Shor lowering (`x`/`y`/`work`/`scratch`) starts fresh-zero.
- **`ShorCleanInput`** — the full input-cleanliness predicate: each active
  register is zero and fresh for its needed extension bits, plus the
  comparator flag is zero.
- **`IdealOrderFindingInput`** — the clean-input predicate used by the ideal
  correctness proofs: both public registers (`x`, `y`) start at zero and own
  disjoint qubits.
- **`ThreeRegsCleanState`** — a state supported only on basis states where
  three given registers are all fresh-zero, defined via `CleanClosure`; its
  `namespace` re-exposes `CleanClosure`'s smart constructors
  (`zero`/`ket`/`add`/`smul`) under this name, plus a custom eliminator
  **`rec'`** (marked `@[induction_eliminator, cases_eliminator]`) that
  preserves the original three-hypothesis `ket` case shape.
- **`FullShorWorkspaceCleanState`** — `ThreeRegsCleanState` specialized to
  `x.reserve`/`data.reserve`/`work.reserve`: the invariant at entry to and
  exit from each modular-multiplication core. Its namespace carries the same
  `rec'` eliminator, delegating to `ThreeRegsCleanState.rec'`.
- **`ShorLoweringCleanState`** — the same invariant but with `data.reserve`
  dropped by one qubit, since that first bit is the algorithmic carry bit and
  not part of the lowering workspace kept clean between modular-multiplication
  stages. Same `rec'` pattern.
- **`exponentScratchCleanReg`** — the exponent reserve appended to the
  Step-3/4 scratch register's owned qubits (given they're disjoint), used to
  fold scratch cleanliness into the same three-register invariant shape
  without disturbing the existing phase-product readiness lemmas' boundary.
- **`ShorConcreteCleanState`** — the compiler-clean invariant strengthened
  with the complete comparator scratch register (via
  `exponentScratchCleanReg` as the first slot), so Step 3 can combine
  data-carry freshness with scratch cleanliness in a single basis-span
  predicate.

## `Setup.lean` — user-facing setup/readiness records

- **`ShorLoweringSetup`** — the low-level lowering assumptions shared by
  every lowered Shor statement: the synthesis-register count `k` (`1 < k`),
  the interpolation-point program `ops`, and its point-consumption/return
  safety proofs.
- **`ShorApproxSetup`** — the public assumptions for the approximate Shor
  implementation: register layout (`ModExpLayout`), modular-exponentiation
  workspace, the Step-4 comparator/Step-3 scratch layout, exponent/data and
  exponent/scratch disjointness, work-register precision, and clean input.
- **`ShorApproxSetupMinimal`** — the lower-level assumptions
  `ShorApproxSetup` is reconstructed from: growable reserve on `data`/`work`,
  the comparator layout, the various disjointness/outside-ownership facts,
  Algorithm-1 precision, and per-register zero/freshness facts, spelled out
  register-by-register rather than packaged.
- **`active_get_mem_ownedQubits`** *(private)* — every active qubit of a
  register belongs to that register's owned qubits; a bookkeeping step for
  the bridge theorem below.
- **`ShorApproxSetupMinimal.toShorApproxSetup`** — the bridge: reconstructs
  `ModExpLayout`, `ModMulCircuitWorkspaceOK`, and `ShorCleanInput` from a
  `ShorApproxSetupMinimal`'s more elementary fields, producing a full
  `ShorApproxSetup`.
- **`LoweredShorReady`** — the public readiness package: a
  `ShorApproxSetupMinimal`, static reserve sufficiency
  (`ShorWorkspaceLargeEnough`), workspace isolation
  (`ShorWorkspaceIsolation`), and initial zero-cleanliness
  (`ShorWorkspaceCleanInput`). `Proofs/Readiness/Static.lean` and
  `Proofs/Readiness/Dynamic.lean` produce its two proof-carrying fields,
  `.workspace` and `.workspace_clean`.
- **`ShorFactoringInstance`** — the classical assumptions on a modulus for
  the final factoring theorem: odd, greater than two, not a prime power.

## `Assertions.lean` — the final correctness Props

This file imports `Proofs.Readiness.Static`: the statements below plug
proof-derived terms into `Prop`-valued hypothesis slots (e.g.
`hready.workspace`), so by proof irrelevance the *meaning* of each Prop does
not depend on those proof bodies — the trusted reading surface remains
`Spec/*`, not `Proofs/*`. See the repo-root `scripts/check_shor_layers.sh`
for this one allowlisted layer exception.

- **`ShorCorrect`** — the ideal-circuit success-probability guarantee:
  running `orderFindingIdeal` on a clean input succeeds with probability at
  least `κ / (log₂ N)⁴`. Proved by `Proofs/NaiveShor/Correctness.lean`'s
  `Shor_correct`.
- **`ShorEndToEndFactoring`** — the full classical statement: enough moduli
  are "successful" that a majority of valid choices work, and for each
  successful `a`, the ideal circuit meets the same success bound *and* the
  classical post-processing (`gcd(a^(r/2) ± 1, N)`) yields a nontrivial
  factor. Proved by `Main.lean`'s `Shor_end_to_end_factoring`.
- **`ShorCorrectApproxLoweredUniform`** — the approximate/lowered-circuit
  guarantee: a single uniform constant `K` such that for every ready setup,
  the lowered approximate circuit's success probability is within
  `2·tbits(x)·√(2Kη)` of the same ideal bound. Proved by
  `Proofs/Correctness.lean`'s `Shor_correct_approx_lowered_of_modExp_bound`,
  exposed as `Main.lean`'s `Shor_correct_approx_lowered_uniform`.
